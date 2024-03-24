package mlscript.compiler.optimizer

import mlscript.compiler.ir.Program
import mlscript.compiler.ir.Defn
import mlscript.compiler.ir.Node
import mlscript.compiler.ir.Node._
import scala.annotation.tailrec
import mlscript.compiler.ir.FreshInt
import mlscript.compiler.ir.Name
import mlscript.compiler.ir.ClassInfo
import mlscript.compiler.ir.DefnRef
import mlscript.compiler.ir.Expr
import mlscript.IntLit
import mlscript.compiler.ir.resolveDefnRef

// fnUid should be the same FreshInt that was used to build the graph being passed into this class
class TailRecOpt(fnUid: FreshInt, tag: FreshInt) {
  private type DefnGraph = Set[DefnNode]

  private def findTailCalls(node: Node)(implicit nodeMap: Map[Defn, DefnNode]): List[DefnNode] = node match
    case Result(res)                      => Nil
    case Jump(defn, args)                 => nodeMap(defn.expectDefn) :: Nil // assume that all definition references are resolved
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
  private def partitionNodes(implicit nodeMap: Map[Defn, DefnNode]): List[DefnGraph] = {
    val defns = nodeMap.values.toSet

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

  private case class DefnInfo(defn: Defn, stackFrameIdx: Int)

  // Returns a set containing the optimized function and the
  // original functions pointing to an optimized function.
  // TODO: Currently untested
  def optimize(defns: Set[Defn], classes: Set[ClassInfo]): Set[Defn] = {

    def asLit(x: Int) = Expr.Literal(IntLit(x))

    // To build the case block, we need to compare integers and check if the result is "True"
    val trueClass = classes.find(c => c.ident == "True").get
    val falseClass = classes.find(c => c.ident == "False").get

    // currently, single tail recursive functions are already optimised
    if (defns.size <= 1)
      return defns

    // concretely order the functions as soon as possible, since the order of the functions matter
    val defnsList = defns.toList

    // TODO: make sure that name clashes aren't a problem
    val trName = Name("tailrecBranch");
    val stackFrame = trName :: defnsList.flatMap(_.params) // take union of stack frames

    val stackFrameIdxes = defnsList.foldRight(1 :: Nil)((defn, ls) => defn.params.size + ls.head :: ls)

    val defnInfoMap: Map[Defn, DefnInfo] = (defnsList zip stackFrameIdxes.drop(1))
      .foldLeft(Map.empty)((map, item) => map + (item._1 -> DefnInfo(item._1, item._2)))

    // TODO: This works fine for now, but ideally should find a way to guarantee the new
    // name is unique
    val newName = defns.foldLeft("")(_ + "_" + _.name) + "opt"

    val newDefnRef = DefnRef(Right(newName))

    // Build the node.
    def transformNode(node: Node)(implicit info: DefnInfo): Node = node match
      case Jump(defn, args) =>
        // transform the stack frame
        val start = stackFrame.take(info.stackFrameIdx).drop(1).map { Expr.Ref(_) } // we drop tailrecBranch and replace it with the defn id
        val end = stackFrame.drop(info.stackFrameIdx + args.size).map { Expr.Ref(_) }
        val concated = asLit(info.defn.id) :: start ::: args ::: end
        Jump(newDefnRef, concated)

      case Result(_)                        => node
      case Case(scrut, cases)               => Case(scrut, cases.map(n => (n._1, transformNode(n._2))))
      case LetExpr(name, expr, body)        => LetExpr(name, expr, transformNode(body))
      case LetCall(names, defn, args, body) => LetCall(names, defn, args, transformNode(body))

    // Tail calls to another function in the component will be replaced with a tail call
    // to the merged function
    def transformDefn(defn: Defn): Defn = Defn(
      defn.id,
      defn.name,
      defn.params,
      defn.resultNum,
      Jump(newDefnRef, asLit(defn.id) :: stackFrame.map(n => Expr.Ref(n)).drop(1)).attachTag(tag)
    )

    // given expressions value, e1, e2, transform it into
    // let scrut = tailrecBranch == value
    // in case scrut of True  -> e1
    //                  False -> e2
    def makeCaseBranch(value: Int, e1: Node, e2: Node): Node =
      val name = Name("scrut")
      val cases = Case(name, List((trueClass, e1), (falseClass, e2))).attachTag(tag)
      LetExpr(
        name,
        Expr.BasicOp("==", List(asLit(value), Expr.Ref(trName))),
        cases
      ).attachTag(tag)

    val first = defnsList.head;
    val firstNode = transformNode(first.body)(defnInfoMap(first))

    val newNode = defnsList.tail
      .foldLeft(firstNode)((elz, defn) =>
        val thisNode = transformNode(defn.body)(defnInfoMap(defn))
        makeCaseBranch(defn.id, thisNode, elz)
      )
      .attachTag(tag)

    // TODO: What is resultNum? It's only ever set to 1 elsewhere
    val newDefn = Defn(fnUid.make, newName, stackFrame, 1, newNode)

    newDefnRef.defn = Left(newDefn)

    defns.map { d => transformDefn(d) } + newDefn
  }

  def partition(defns: Set[Defn]): List[Set[Defn]] = {
    val nodeMap: Map[Defn, DefnNode] = defns.foldLeft(Map.empty)((m, d) => m + (d -> DefnNode(d)))
    partitionNodes(nodeMap).map(g => g.map(d => d.defn))
  }

  def apply(p: Program) = run(p)

  def run(p: Program): Program = {
    val partitions = partition(p.defs)
    val newDefs: Set[Defn] = partitions.flatMap { optimize(_, p.classes) }.toSet

    // update the definition refs
    newDefs.foreach { defn => resolveDefnRef(defn.body, newDefs, true) }
    resolveDefnRef(p.main, newDefs, true)

    Program(p.classes, newDefs, p.main)
  }
}
