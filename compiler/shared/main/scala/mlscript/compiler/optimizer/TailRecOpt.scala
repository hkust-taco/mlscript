package mlscript.compiler.optimizer

import mlscript.compiler.ir._
import mlscript.compiler.ir.Node._
import scala.annotation.tailrec
import mlscript.IntLit
import mlscript.utils.shorthands.Bool

// fnUid should be the same FreshInt that was used to build the graph being passed into this class
class TailRecOpt(fnUid: FreshInt, tag: FreshInt) {
  private type DefnGraph = Set[DefnNode]

  class ModConsCallInfo(defn: Defn, letCallName: Name, letCtorName: Name, fieldName: String, clsInfo: ClassInfo)

  class TailCallInfo(defn: Defn)

  private def getModConsCall(
    node: Node, 
    defnAcc: Option[Defn], 
    letCallName: Option[Name], 
    letCtorName: Option[Name], 
    fieldName: Option[String], 
    clsInfo: Option[ClassInfo], 
    hasTailrecAnn: Boolean // has tailrec annotation
  ): Option[ModConsCallInfo] = node match
    case Result(res) => 
      (defnAcc, letCallName, letCtorName, fieldName, clsInfo) match
        case (Some(defn), Some(letCallName), Some(letCtorName), Some(fieldName), Some(clsInfo)) =>
          Some(ModConsCallInfo(defn, letCallName, letCtorName, fieldName, clsInfo))
        case _ => None
    case Jump(_, _) => None 
    case Case(scrut, cases) => ???
    case LetExpr(name, expr, body) => body match
      case Result(res) =>  ???
      case Jump(defn, args) => ???
      case _ => getModConsCall(body, defnAcc, letCallName, letCtorName, fieldName, clsInfo, hasTailrecAnn)
    
    case LetCall(names, defn, args, body, _) => ???
    case AssignField(assignee, clsInfo, fieldName, value, body) => ???

  // checks whether a list of names is equal to a list of trivial expressions referencing those names
  private def argsListEqual(names: List[Name], exprs: List[TrivialExpr]) =
    val results = exprs.collect { case Expr.Ref(name) => name }
    names == results

  private def isIdentityJp(d: Defn): Bool = true
  
  private def isTailCall(node: Node): Boolean = node match
    case LetCall(names, defn, args, body, _) => body match
      case Result(res) => argsListEqual(names, res) 
      case Jump(defn, args) => argsListEqual(names, args) && isIdentityJp(defn.expectDefn)
      case _ => false
    case _ => false
  
  private def findTailCalls(node: Node)(implicit nodeMap: Map[Int, DefnNode]): List[DefnNode] = node match
    case LetCall(names, defn, args, body, isTailRec) =>
      if isTailCall(node) then nodeMap(defn.expectDefn.id) :: Nil
      else 
        if isTailRec then
          throw IRError("not a tail call")
        findTailCalls(body)
    case Result(res)                      => Nil
    // case Jump(defn, args)                 => nodeMap(defn.expectDefn.id) :: Nil // assume that all definition references are resolved
    case Jump(defn, args)                 => Nil // jump points are already optimized and we should not touch them
    case Case(scrut, cases)               => cases.flatMap((_, body) => findTailCalls(body))
    case LetExpr(name, expr, body)        => findTailCalls(body)
    case AssignField(_, _, _, _, body)       => findTailCalls(body)

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

  private def partitionNodes(implicit nodeMap: Map[Int, DefnNode]): List[DefnGraph] = {
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
        if (u.visited) then
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

  // Given a strongly connected component `defns`,
  // returns a set containing the optimized function and the
  // original functions pointing to an optimized function.
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

    // assume all defns have the same number of results
    // in fact, they should theoretically have the same return type if the program type checked
    val resultNum = defnsList.head.resultNum

    // TODO: make sure that name clashes aren't a problem
    val trName = Name("tailrecBranch");

    // To be used to replace variable names inside a definition to avoid variable name clashes 
    val nameMaps: Map[Int, Map[Name, Name]] = defnsList.map(
      defn => defn.id -> defn.params.map(n => n -> Name(defn.name + "_" + n.str)).toMap
    ).toMap

    val stackFrameIdxes = defnsList.foldLeft(1 :: Nil)((ls, defn) => defn.params.size + ls.head :: ls).drop(1).reverse

    val defnInfoMap: Map[Int, DefnInfo] = (defnsList zip stackFrameIdxes)
      .foldLeft(Map.empty)((map, item) => map + (item._1.id -> DefnInfo(item._1, item._2)))

    val stackFrame = trName :: defnsList.flatMap(d => d.params.map(n => nameMaps(d.id)(n))) // take union of stack frames

    // TODO: This works fine for now, but ideally should find a way to guarantee the new
    // name is unique
    val newName = defns.foldLeft("")(_ + "_" + _.name) + "_opt"
    val jpName = defns.foldLeft("")(_ + "_" + _.name) + "_opt_jp"

    val newDefnRef = DefnRef(Right(newName))
    val jpDefnRef = DefnRef(Right(jpName))

    def transformStackFrame(args: List[TrivialExpr], info: DefnInfo) =
      val start = stackFrame.take(info.stackFrameIdx).drop(1).map { Expr.Ref(_) } // we drop tailrecBranch and replace it with the defn id
      val end = stackFrame.drop(info.stackFrameIdx + args.size).map { Expr.Ref(_) }
      asLit(info.defn.id) :: start ::: args ::: end

    // Build the node which will be contained inside the jump point.
    def transformNode(node: Node): Node = node match
      case Jump(_, _)                                => node
      case Result(_)                                 => node
      case Case(scrut, cases)                        => Case(scrut, cases.map(n => (n._1, transformNode(n._2))))
      case LetExpr(name, expr, body)                 => LetExpr(name, expr, transformNode(body))
      case LetCall(names, defn, args, body, isTailRec) =>
        if isTailCall(node) && defnInfoMap.contains(defn.expectDefn.id) then
          Jump(jpDefnRef, transformStackFrame(args, defnInfoMap(defn.expectDefn.id))).attachTag(tag)
        else
          LetCall(names, defn, args, transformNode(body), isTailRec)
      case AssignField(assignee, clsInfo, field, value, body) => AssignField(assignee, clsInfo, field, value, transformNode(body))

    // Tail calls to another function in the component will be replaced with a tail call
    // to the merged function
    def transformDefn(defn: Defn): Defn = {
      // TODO: Figure out how to substitute variables with dummy variables.
      val info = defnInfoMap(defn.id)

      val start = stackFrame.take(info.stackFrameIdx).drop(1).map { _ => Expr.Literal(IntLit(0)) } // we drop tailrecBranch and replace it with the defn id
      val end = stackFrame.drop(info.stackFrameIdx + defn.params.size).map { _ => Expr.Literal(IntLit(0)) }
      val args = asLit(info.defn.id) :: start ::: defn.params.map(Expr.Ref(_)) ::: end

      // We use a let call instead of a jump to avoid newDefn from being turned into a join point,
      // which would cause it to be inlined and result in code duplication.
      val names = (0 until resultNum).map(i => Name("r" + i.toString())).toList
      val namesExpr = names.map(Expr.Ref(_))
      val res = Result(namesExpr).attachTag(tag)
      val call = LetCall(names, newDefnRef, args, res, false).attachTag(tag)
      Defn(defn.id, defn.name, defn.params, defn.resultNum, call)
    }

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

    def getOrKey[T](m: Map[T, T])(key: T): T = m.get(key) match
      case None => key
      case Some(value) => value
     

    val first = defnsList.head;
    val firstMap = nameMaps(first.id)
    val firstBodyRenamed = first.body.mapName(getOrKey(firstMap))
    val firstNode = transformNode(firstBodyRenamed)

    val newNode = defnsList.tail
      .foldLeft(firstNode)((elz, defn) =>
        val nmeNap = nameMaps(defn.id)
        val renamed = defn.body.mapName(getOrKey(nmeNap))
        val thisNode = transformNode(renamed)
        makeCaseBranch(defn.id, thisNode, elz)
      )
      .attachTag(tag)

    val jpDefn = Defn(fnUid.make, jpName, stackFrame, resultNum, newNode)

    val jmp = Jump(jpDefnRef, stackFrame.map(Expr.Ref(_))).attachTag(tag)
    val newDefn = Defn(fnUid.make, newName, stackFrame, resultNum, jmp)

    // This is the definition that will be called
    // val createIntermidDefn =

    jpDefnRef.defn = Left(jpDefn)
    newDefnRef.defn = Left(newDefn)

    defns.map { d => transformDefn(d) } + newDefn + jpDefn
  }

  def partition(defns: Set[Defn]): List[Set[Defn]] = {
    val nodeMap: Map[Int, DefnNode] = defns.foldLeft(Map.empty)((m, d) => m + (d.id -> DefnNode(d)))
    partitionNodes(nodeMap).map(g => g.map(d => d.defn))
  }

   

  def apply(p: Program) = run(p)

  def run_debug(p: Program): (Program, List[Set[String]]) = {
    // val rewritten = p.defs.map(d => Defn(d.id, d.name, d.params, d.resultNum, rewriteTailCalls(d.body)))
    val partitions = partition(p.defs)
    val newDefs: Set[Defn] = partitions.flatMap { optimize(_, p.classes) }.toSet

    // update the definition refs
    newDefs.foreach { defn => resolveDefnRef(defn.body, newDefs, true) }
    resolveDefnRef(p.main, newDefs, true)

    (Program(p.classes, newDefs, p.main), partitions.map(t => t.map(f => f.name)))
  }

  def run(p: Program): Program = {
    run_debug(p)._1
  }
}
