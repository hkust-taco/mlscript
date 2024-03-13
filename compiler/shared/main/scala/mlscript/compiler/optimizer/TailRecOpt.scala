package mlscript.compiler.optimizer

import mlscript.compiler.ir.Program
import mlscript.compiler.ir.Defn
import mlscript.compiler.ir.Node
import mlscript.compiler.ir.Node._
import scala.annotation.tailrec

class TailRecOpt {
  private type DefnGraph = Set[DefnNode]

  private def findTailCalls(node: Node)(implicit nodeMap: Map[Defn, DefnNode]): List[DefnNode] = node match
    case Result(res)                      => Nil
    case Jump(defn, args)                 => nodeMap(defn.expectDefn) :: Nil
    case Case(scrut, cases)               => cases.flatMap((_, body) => findTailCalls(body))
    case LetExpr(name, expr, body)        => findTailCalls(body)
    case LetCall(names, defn, args, body) => findTailCalls(body)

  // Partions a tail recursive call graph into strongly connected components
  // Refernece: https://en.wikipedia.org/wiki/Strongly_connected_component

  // Implements Tarjan's algorithm.
  // Wikipedia: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
  // Implementation Reference: https://www.baeldung.com/cs/scc-tarjans-algorithm

  private class DefnNode(val defn: Defn) {
    override def hashCode(): Int = defn.hashCode

    var num: Int = Int.MaxValue
    var lowest: Int = Int.MaxValue
    var visited: Boolean = false
    var processed: Boolean = false
  }

  // TODO: this is untested. test this.
  private def partitionNodes(defns: DefnGraph)(implicit nodeMap: Map[Defn, DefnNode]): List[DefnGraph] = {
    var ctr = 0
    var stack: List[DefnNode] = Nil
    var sccs: List[DefnGraph] = Nil

    def dfs(src: DefnNode): Unit = {
      src.num = ctr
      src.lowest = ctr
      ctr += 1
      src.visited = true
      stack = src :: stack

      for (u <- findTailCalls(src.defn.body)) do {
        if (u.visited)
          if (!u.processed)
            src.lowest = u.num.min(src.lowest)          
        else
          dfs(u)
          src.lowest = u.lowest.min(src.lowest)
      }

      src.processed = true

      if (src.num == src.lowest) {
        var scc: DefnGraph = Set()

        def pop(): DefnNode = {
          val ret = stack.head
          stack = stack.tail
          ret
        }

        var vertex = pop()

        while (vertex != src) {
          scc = scc + vertex
          vertex = pop()
        }

        scc = scc + vertex

        sccs = scc :: sccs 
      }
    }

    for (v <- defns) {
      if (!v.visited)
        dfs(v)
    }

    sccs
  }

  def partition(defns: Set[Defn]) = {
    val nodeMap = defns.foldLeft[Map[Defn, DefnNode]](Map())((m, d) => m + (d -> DefnNode(d)))
    partitionNodes(nodeMap.values.toSet)(nodeMap).map(g => g.map(d => d.defn))
  }

  def apply(p: Program) = run(p)

  def run(p: Program): Program = {
    val defnMap = p.defs.foldLeft[Map[Int, Defn]](Map())((m, d) => m + (d.id -> d))

    // TODO
    p
  }
}