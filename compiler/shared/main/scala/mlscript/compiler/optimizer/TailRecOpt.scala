package mlscript.compiler.optimizer

import mlscript.compiler.ir._
import mlscript.compiler.ir.Node._
import scala.annotation.tailrec
import mlscript.IntLit
import mlscript.utils.shorthands.Bool

// fnUid should be the same FreshInt that was used to build the graph being passed into this class
class TailRecOpt(fnUid: FreshInt, tag: FreshInt):
  case class LetCtorNodeInfo(node: LetExpr, ctor: Expr.CtorApp, ctorValName: Name, fieldName: String)

  enum CallInfo:
    case TailCallInfo(src: Defn, defn: Defn, letCallNode: LetCall) extends CallInfo
    case ModConsCallInfo(src: Defn, startNode: Node, defn: Defn, letCallNode: LetCall, letCtorNode: LetCtorNodeInfo) extends CallInfo

    def getSrc = this match
      case TailCallInfo(src, _, _) => src
      case ModConsCallInfo(src, _, _, _, _) => src 

    def getDefn = this match
      case TailCallInfo(_, defn, _) => defn
      case ModConsCallInfo(_, _, defn, _, _) => defn
    

  private class DefnGraph(val nodes: Set[DefnNode], val edges: Set[CallInfo]):
    def removeMetadata: ScComponent = ScComponent(nodes.map(_.defn), edges)
  
  private class ScComponent(val nodes: Set[Defn], val edges: Set[CallInfo])

  import CallInfo._

  @tailrec
  private def getOptimizableCalls(node: Node)(implicit
    src: Defn,
    start: Node,
    calledDefn: Option[Defn],
    letCallNode: Option[LetCall],
    letCtorNode: Option[LetCtorNodeInfo],
    candReturnName: Option[Name]
  ): Either[CallInfo, List[Node]] = 
    def returnFailure = letCallNode match
      case Some(LetCall(_, _, _, _, isTailRec)) if isTailRec => throw IRError("not a tail call")
      case _ => Right(Nil)

    node match // Left if mod cons call found, Right if none was found -- we return the next nodes to be scanned 
      case Result(res) =>
        (calledDefn, letCallNode, letCtorNode, candReturnName) match
          case (Some(defn), Some(letCallNode), Some(letCtorName), Some(candReturnName)) =>
            if argsListEqual(List(candReturnName), res) then
              Left(ModConsCallInfo(src, start, defn, letCallNode, letCtorName))
            else
              returnFailure
          case _ => returnFailure
      case Jump(jp, args) => 
        // different cases
        (calledDefn, letCallNode, letCtorNode, candReturnName) match
          case (Some(defn), Some(letCallNode), Some(letCtorName), Some(candReturnName)) =>
            if argsListEqual(List(candReturnName), args) && isIdentityJp(jp.expectDefn) then
              Left(ModConsCallInfo(src, start, defn, letCallNode, letCtorName))
            else
              returnFailure
          case _ => returnFailure
        
      case Case(scrut, cases) => Right(cases.map(_._2))
      case x: LetExpr =>
        val LetExpr(name, expr, body) = x
        expr match
          // Check if this let binding references the mod cons call.
          case Expr.Ref(name) => 
            letCallNode match
              case None => getOptimizableCalls(body) // OK
              case Some(LetCall(names, _, _, _, isTailRec)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                if names.contains(name) then
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered
                else
                  getOptimizableCalls(body) // OK
          
          case Expr.Literal(lit) => getOptimizableCalls(body) // OK
          case y: Expr.CtorApp =>
            val Expr.CtorApp(clsInfo, ctorArgs) = y
            // if expr is a constructor with a call to some function as a parameter
            letCallNode match
              case None => getOptimizableCalls(body) // OK
              case Some(LetCall(letCallNames, _, _, _, isTailRec)) => // there was a previous call
                // 1. Check if the ctor application contains this call
                val argNames = ctorArgs.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = letCallNames.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then
                  // OK, this constructor does not use the mod cons call
                  // Now check if the constructor uses the previous ctor.
                  candReturnName match
                    case None => getOptimizableCalls(body) // no previous ctor, just continue
                    case Some(value) => getOptimizableCalls(body)(src, start, calledDefn, letCallNode, letCtorNode, Some(name)) 
                else
                  // it does use it, further analyse
                  letCtorNode match
                    case None => 
                      // First constructor discovered using this call as a parameter.
                      // This is OK. Add this discovered information
                      
                      // TODO: for now, assume functions return only one value. handling multiple
                      // values is a bit more complicated
                      val ctorArgName = inters.head
                      val ctorArgIndex = ctorArgs.indexWhere { 
                        case Expr.Ref(nme) => nme == ctorArgName
                        case _ => false 
                      }

                      val fieldName = clsInfo.fields(ctorArgIndex)
                      
                      // populate required values
                      getOptimizableCalls(body)(src, start, calledDefn, letCallNode, Some(LetCtorNodeInfo(x, y, name, fieldName)), Some(name))
                    case Some(_) =>
                      // another constructor is already using the call. Not OK

                      // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                      // invalidate the discovered call and continue
                      if isTailRec then throw IRError("not a mod cons call")
                      else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered

          case Expr.Select(name, cls, field) =>
            letCallNode match
              case None => getOptimizableCalls(body) // OK
              case Some(LetCall(names, _, _, _, isTailRec)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                if names.contains(name) then
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered
                else
                  getOptimizableCalls(body) // OK
          case Expr.BasicOp(name, args) =>
            letCallNode match
              case None => getOptimizableCalls(body) // OK
              case Some(LetCall(names, _, _, _, isTailRec)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                val argNames = args.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = names.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then
                  getOptimizableCalls(body) // OK
                else
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered
      case x: LetCall =>
        val LetCall(names, defn, args, body, isTailRec) = x

        if isTailCall(x) then
          Left(TailCallInfo(src, defn.expectDefn, x))
        else
          letCallNode match
            case None => // OK, use this LetCall as the mod cons
              getOptimizableCalls(body)(src, start, Some(defn.expectDefn), Some(x), None, None)
            case Some(LetCall(namesOld, defnOld, argsOld, bodyOld, isTailRecOld)) =>
              if isTailRecOld && isTailRec then
                // 1. If both the old and newly discovered call are marked with tailrec, error
                throw IRError("multiple calls in the same branch marked with tailrec")
              else if isTailRecOld then
                // 2. old call is marked as tailrec so we must continue using it as the mod cons call.
                // make sure the newly discovered call does not use the current call as a parameter
                val argNames = args.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = namesOld.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then getOptimizableCalls(body) // OK
                else throw IRError("not a mod cons call") 
              else
                // old call is not tailrec, so we can override it however we want
                // we take a lucky guess and mark this as the mod cons call, but the
                // user really should mark which calls should be tailrec
                getOptimizableCalls(body)(src, start, Some(defn.expectDefn), Some(x), None, None)
        
      case AssignField(assignee, clsInfo, assignmentFieldName, value, body) =>
        // make sure `value` is not the mod cons call
        letCallNode match
          case None => getOptimizableCalls(body) // OK
          case Some(LetCall(names, defn, args, body, isTailRec)) =>
            value match
              case Expr.Ref(name) =>
                if names.contains(name) && isTailRec then throw IRError("not a mod cons call")
                  else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered
              case _ =>
                letCtorNode match
                  case None => getOptimizableCalls(body) // OK
                  case Some(LetCtorNodeInfo(_, ctor, name, fieldName)) =>
                    // If this assignment overwrites the mod cons value, forget it
                    if fieldName == assignmentFieldName && isTailRec then throw IRError("not a mod cons call")
                    else getOptimizableCalls(body)(src, start, None, None, None, None) // invalidate everything that's been discovered 

  // checks whether a list of names is equal to a list of trivial expressions referencing those names
  private def argsListEqual(names: List[Name], exprs: List[TrivialExpr]) =
    if names.length == exprs.length then
      val results = exprs.collect { case Expr.Ref(name) => name }
      names == results
    else
      false

  private def isIdentityJp(d: Defn): Bool = true

  private def isTailCall(node: Node): Boolean = node match
    case LetCall(names, defn, args, body, _) =>
      body match
        case Result(res)      => argsListEqual(names, res)
        case Jump(defn, args) => argsListEqual(names, args) && isIdentityJp(defn.expectDefn)
        case _                => false
    case _ => false

  private def findTailCalls(node: Node)(implicit src: Defn): Set[CallInfo] = 
    getOptimizableCalls(node)(src, node, None, None, None, None) match
      case Left(callInfo) => Set(callInfo)
      case Right(nodes) => nodes.foldLeft(Set())((calls, node) => calls ++ findTailCalls(node))
  
  // Partions a tail recursive call graph into strongly connected components
  // Refernece: https://en.wikipedia.org/wiki/Strongly_connected_component

  // Implements Tarjan's algorithm.
  // Wikipedia: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
  // Implementation Reference: https://www.baeldung.com/cs/scc-tarjans-algorithm

  private class DefnNode(val defn: Defn):
    override def hashCode(): Int = defn.hashCode

    var num: Int = Int.MaxValue
    var lowest: Int = Int.MaxValue
    var visited: Boolean = false
    var processed: Boolean = false

  private def partitionNodes(implicit nodeMap: Map[Int, DefnNode]): List[DefnGraph] =
    val defns = nodeMap.values.toSet

    var ctr = 0
    var stack: List[(DefnNode, Set[CallInfo])] = Nil
    var sccs: List[DefnGraph] = Nil

    def dfs(src: DefnNode): Unit =
      src.num = ctr
      src.lowest = ctr
      ctr += 1
      src.visited = true
      
      val tailCalls = findTailCalls(src.defn.body)(src.defn)
      stack = (src, tailCalls) :: stack
      for (u <- tailCalls) do {
        val neighbour = nodeMap(u.getDefn.id)
        if (neighbour.visited) then
          if (!neighbour.processed)
            src.lowest = neighbour.num.min(src.lowest)
        else
          dfs(neighbour)
          src.lowest = neighbour.lowest.min(src.lowest)
      }

      src.processed = true

      if (src.num == src.lowest) then
        var scc: Set[DefnNode] = Set()
        var sccEdges: Set[CallInfo] = Set()

        def pop(): (DefnNode, Set[CallInfo]) =
          val ret = stack.head
          stack = stack.tail
          ret
        

        var (vertex, edges) = pop()

        while (vertex != src) {
          scc = scc + vertex
          sccEdges = sccEdges ++ edges
          
          val next = pop()
          vertex = next._1
          edges = next._2
        }

        scc = scc + vertex
        val sccIds = scc.map { d => d.defn.id }
        sccEdges = sccEdges.filter { c => sccIds.contains(c.getDefn.id)}

        sccs = DefnGraph(scc, sccEdges) :: sccs
      
    

    for (v <- defns)
      if (!v.visited)
        dfs(v)

    
    sccs
  

  private case class DefnInfo(defn: Defn, stackFrameIdx: Int)

  def asLit(x: Int) = Expr.Literal(IntLit(x))
  
  // Given a strongly connected component `defns` of mutually mod cons functions,
  // returns a set containing mutually tail recursive versions of them and
  // the original functions pointing to the optimized ones. 
  private def optimizeModCons(component: ScComponent, classes: Set[ClassInfo]): Set[Defn] = ???


  // Given a strongly connected component `defns` of mutually
  // tail recursive functions, returns a set containing the optimized function and the
  // original functions pointing to an optimized function.
  private def optimizeTailRec(component: ScComponent, classes: Set[ClassInfo]): Set[Defn] = 

    // To build the case block, we need to compare integers and check if the result is "True"
    val trueClass = classes.find(c => c.ident == "True").get
    val falseClass = classes.find(c => c.ident == "False").get

    val defns = component.nodes

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
    val nameMaps: Map[Int, Map[Name, Name]] = defnsList.map(defn => defn.id -> defn.params.map(n => n -> Name(defn.name + "_" + n.str)).toMap).toMap

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
      case Jump(_, _)                => node
      case Result(_)                 => node
      case Case(scrut, cases)        => Case(scrut, cases.map(n => (n._1, transformNode(n._2))))
      case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body))
      case LetCall(names, defn, args, body, isTailRec) =>
        if isTailCall(node) && defnInfoMap.contains(defn.expectDefn.id) then
          Jump(jpDefnRef, transformStackFrame(args, defnInfoMap(defn.expectDefn.id))).attachTag(tag)
        else LetCall(names, defn, args, transformNode(body), isTailRec)
      case AssignField(assignee, clsInfo, field, value, body) => AssignField(assignee, clsInfo, field, value, transformNode(body))

    // Tail calls to another function in the component will be replaced with a tail call
    // to the merged function
    def transformDefn(defn: Defn): Defn =
      // TODO: Figure out how to substitute variables with dummy variables.
      val info = defnInfoMap(defn.id)

      val start =
        stackFrame.take(info.stackFrameIdx).drop(1).map { _ => Expr.Literal(IntLit(0)) } // we drop tailrecBranch and replace it with the defn id
      val end = stackFrame.drop(info.stackFrameIdx + defn.params.size).map { _ => Expr.Literal(IntLit(0)) }
      val args = asLit(info.defn.id) :: start ::: defn.params.map(Expr.Ref(_)) ::: end

      // We use a let call instead of a jump to avoid newDefn from being turned into a join point,
      // which would cause it to be inlined and result in code duplication.
      val names = (0 until resultNum).map(i => Name("r" + i.toString())).toList
      val namesExpr = names.map(Expr.Ref(_))
      val res = Result(namesExpr).attachTag(tag)
      val call = LetCall(names, newDefnRef, args, res, false).attachTag(tag)
      Defn(defn.id, defn.name, defn.params, defn.resultNum, call)
    

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
      case None        => key
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
  

  private def partition(defns: Set[Defn]): List[ScComponent] = 
    val nodeMap: Map[Int, DefnNode] = defns.foldLeft(Map.empty)((m, d) => m + (d.id -> DefnNode(d)))
    partitionNodes(nodeMap).map(_.removeMetadata)
  

  def apply(p: Program) = run(p)

  def run_debug(p: Program): (Program, List[Set[String]]) = 
    // val rewritten = p.defs.map(d => Defn(d.id, d.name, d.params, d.resultNum, rewriteTailCalls(d.body)))
    val partitions = partition(p.defs)
    val newDefs: Set[Defn] = partitions.flatMap { optimizeTailRec(_, p.classes) }.toSet

    // update the definition refs
    newDefs.foreach { defn => resolveDefnRef(defn.body, newDefs, true) }
    resolveDefnRef(p.main, newDefs, true)

    (Program(p.classes, newDefs, p.main), partitions.map(t => t.nodes.map(f => f.name)))

  def run(p: Program): Program = run_debug(p)._1