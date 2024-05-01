package mlscript.compiler.optimizer

import mlscript.compiler.ir._
import mlscript.compiler.ir.Node._
import scala.annotation.tailrec
import mlscript.IntLit
import mlscript.utils.shorthands.Bool

// fnUid should be the same FreshInt that was used to build the graph being passed into this class
class TailRecOpt(fnUid: FreshInt, classUid: FreshInt, tag: FreshInt):
  case class LetCtorNodeInfo(node: LetExpr, ctor: Expr.CtorApp, cls: ClassInfo, ctorValName: Name, fieldName: String)

  enum CallInfo:
    case TailCallInfo(src: Defn, defn: Defn, letCallNode: LetCall) extends CallInfo
    case ModConsCallInfo(src: Defn, startNode: Node, defn: Defn, letCallNode: LetCall, letCtorNode: LetCtorNodeInfo, retName: Name, retNode: Node) extends CallInfo

    override def toString(): String = this match
      case TailCallInfo(src, defn, letCallNode) => 
        f"TailCall { ${src.name}$$${src.id} -> ${defn.name}$$${defn.id} }"
      case ModConsCallInfo(src, startNode, defn, letCallNode, letCtorNode, _, _) =>
        f"ModConsCall { ${src.name}$$${src.id} -> ${defn.name}$$${defn.id}, class: ${letCtorNode.cls.ident}, field: ${letCtorNode.fieldName} }"

    def getSrc = this match
      case TailCallInfo(src, _, _) => src
      case ModConsCallInfo(src, _, _, _, _, _, _) => src 

    def getDefn = this match
      case TailCallInfo(_, defn, _) => defn
      case ModConsCallInfo(_, _, defn, _, _, _, _) => defn
    
  private class DefnGraph(val nodes: Set[DefnNode], val edges: Set[CallInfo], val joinPoints: Set[Defn]):
    def removeMetadata: ScComponent = ScComponent(nodes.map(_.defn), edges, joinPoints)
  
  private class ScComponent(val nodes: Set[Defn], val edges: Set[CallInfo], val joinPoints: Set[Defn])

  import CallInfo._

  // Hack to make scala think discoverJoinPoints is tail recursive and be
  // partially optimized :P
  def casesToJps(cases: List[(ClassInfo, Node)], acc: Set[Defn]): Set[Defn] =
    cases.foldLeft(acc)((jps, branch) => discoverJoinPoints(branch._2, jps))
  
  def discoverJoinPointsCont(defn: Defn, acc: Set[Defn]) =
    discoverJoinPoints(defn.body, acc) + defn

  // do a DFS to discover join points
  @tailrec
  private def discoverJoinPoints(node: Node, acc: Set[Defn]): Set[Defn] =
    node match
      case Result(res) => Set()
      case Jump(defn_, args) => 
        val defn = defn_.expectDefn
        if isIdentityJp(defn) then acc
        else if acc.contains(defn) then acc
        else discoverJoinPointsCont(defn, acc + defn)
      case Case(scrut, cases) => casesToJps(cases, acc)
      case LetExpr(name, expr, body) => discoverJoinPoints(body, acc)
      case LetCall(names, defn, args, isTailRec, body) => discoverJoinPoints(body, acc)
      case AssignField(assignee, clsInfo, fieldName, value, body) => discoverJoinPoints(body, acc)

  private def getRetName(names: Set[Name], retVals: List[TrivialExpr]): Option[Name] =
    val names = retVals.collect { case Expr.Ref(nme) => nme }
    if names.length != 1 then None
    else
      val nme = names.head
      if names.contains(nme) then Some(nme)
      else None

  // would prefer to have this inside discoverOptimizableCalls, but this makes scala think it's not tail recursive
  def shadowAndCont(next: Node, nme: Name)(implicit
    acc: Map[Int, Set[CallInfo]],
    src: Defn,
    start: Node,
    calledDefn: Option[Defn],
    letCallNode: Option[LetCall],
    letCtorNode: Option[LetCtorNodeInfo],
    containingCtors: Set[Name]
  ) = discoverOptimizableCalls(next)(acc, src, start, calledDefn, letCallNode, letCtorNode, containingCtors - nme) 
  
  @tailrec
  private def discoverOptimizableCalls(node: Node)(implicit
    acc: Map[Int, Set[CallInfo]],
    src: Defn,
    start: Node,
    calledDefn: Option[Defn], // The definition that was called in a tailrec mod cons call
    letCallNode: Option[LetCall], // The place where that definition was called
    letCtorNode: Option[LetCtorNodeInfo], // The place where the result from that call was put into a constructor
    containingCtors: Set[Name], // Value names of ctors containing the constructor containing the result from the call
  ): Either[Map[Int, Set[CallInfo]], List[Node]] = 
    def updateMap(acc: Map[Int, Set[CallInfo]], c: Set[CallInfo]) =
      acc.get(src.id) match
        case None => acc + (src.id -> c)
        case Some(value) => acc + (src.id -> (value ++ c))
    
    def updateMapSimple(c: CallInfo) = updateMap(acc, Set(c))

    def returnFailure = letCallNode match
      case Some(LetCall(_, _, _, isTailRec, _)) if isTailRec => throw IRError("not a tail call")
      case _ => Right(Nil)

    node match // Left if mod cons call found, Right if none was found -- we return the next nodes to be scanned 
      case Result(res) =>
        (calledDefn, letCallNode, letCtorNode) match
          case (Some(defn), Some(letCallNode), Some(letCtorName)) =>
            getRetName(containingCtors, res) match
              case None => returnFailure
              case Some(value) => Left(updateMapSimple(ModConsCallInfo(src, start, defn, letCallNode, letCtorName, value, node)))
          case _ => returnFailure
      case Jump(jp, args) => 
        def mergeCalls(acc: Map[Int, Set[CallInfo]], calls: Set[CallInfo]) =
          val newCalls = calls.map {
            case TailCallInfo(_, defn, letCallNode) => 
              TailCallInfo(src, defn, letCallNode)
            case ModConsCallInfo(_, startNode, defn, letCallNode, letCtorNode, retName, retNode) =>
              ModConsCallInfo(src, startNode, defn, letCallNode, letCtorNode, retName, retNode)
          }
          updateMap(acc, newCalls)

        def updateAndMergeJpCalls = letCallNode match
          case Some(LetCall(_, _, _, isTailRec, _)) if isTailRec => throw IRError("not a tail call")
          case _ => 
            val jpDefn = jp.expectDefn
            acc.get(jpDefn.id) match
              case None => // explore the join point
                val newAcc = discoverCalls(jpDefn.body)(jpDefn, acc)
                mergeCalls(newAcc, newAcc(jpDefn.id))
              case Some(value) => mergeCalls(acc, value)

        // different cases
        (calledDefn, letCallNode, letCtorNode) match
          case (Some(defn), Some(letCallNode), Some(letCtorName)) =>
            getRetName(containingCtors, args) match
              case Some(value) if isIdentityJp(jp.expectDefn) => 
                Left(updateMapSimple(ModConsCallInfo(src, start, defn, letCallNode, letCtorName, value, node)))
              case _ => 
                Left(updateAndMergeJpCalls)
          case _ => Left(updateAndMergeJpCalls)
        
      case Case(scrut, cases) => Right(cases.map(_._2))
      case x: LetExpr =>
        val LetExpr(name, expr, body) = x
        expr match
          // Check if this let binding references the mod cons call.
          case Expr.Ref(name) => 
            letCallNode match
              case None => 
                shadowAndCont(body, name) // OK
              case Some(LetCall(names, _, _, isTailRec, _)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                if names.contains(name) then
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered
                else
                  shadowAndCont(body, name) // OK
          
          case Expr.Literal(lit) => shadowAndCont(body, name) // OK
          case y: Expr.CtorApp =>
            val Expr.CtorApp(clsInfo, ctorArgs) = y
            // if expr is a constructor with a call to some function as a parameter
            letCallNode match
              case None => shadowAndCont(body, name) // OK
              case Some(LetCall(letCallNames, _, _, isTailRec, _)) => // there was a previous call
                // 1. Check if the ctor application contains this call
                val argNames = ctorArgs.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = letCallNames.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then
                  // OK, this constructor does not use the mod cons call
                  // Now check if the constructor uses any previous ctor containing the call.
                  // If it does, then add this name to the list of constructors containing the call
                  val inters = containingCtors.intersect(argNames)
                  
                  if inters.isEmpty then
                    shadowAndCont(body, name) // does not use, OK to ignore this one
                  else 
                    // add this name to the list of constructors containing the call
                    discoverOptimizableCalls(body)(acc, src, start, calledDefn, letCallNode, letCtorNode, containingCtors + name) 
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
                      discoverOptimizableCalls(body)(acc, src, start, calledDefn, letCallNode, Some(LetCtorNodeInfo(x, y, clsInfo, name, fieldName)), Set(name))
                    case Some(_) =>
                      // another constructor is already using the call. Not OK

                      // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                      // invalidate the discovered call and continue
                      if isTailRec then throw IRError("not a mod cons call")
                      else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered

          case Expr.Select(name, cls, field) =>
            letCallNode match
              case None => shadowAndCont(body, name) // OK
              case Some(LetCall(names, _, _, isTailRec, _)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                if names.contains(name) then
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered
                else
                  shadowAndCont(body, name) // OK
          case Expr.BasicOp(_, args) =>
            letCallNode match
              case None => shadowAndCont(body, name) // OK
              case Some(LetCall(names, _, _, isTailRec, _)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                val argNames = args.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = names.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then
                  shadowAndCont(body, name) // OK
                else
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  if isTailRec then throw IRError("not a mod cons call")
                  else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered
      case x: LetCall =>
        val LetCall(names, defn, args, isTailRec, body) = x

        if isTailCall(x) then
          Left(updateMapSimple(TailCallInfo(src, defn.expectDefn, x)))
        else
          letCallNode match
            case None => // OK, use this LetCall as the mod cons
              // For now, only optimize functions which return one value
              if defn.expectDefn.resultNum == 1 then
                discoverOptimizableCalls(body)(acc, src, start, Some(defn.expectDefn), Some(x), None, Set())
              else
                discoverOptimizableCalls(body)
            case Some(LetCall(namesOld, defnOld, argsOld, isTailRecOld, bodyOld)) =>
              if isTailRecOld && isTailRec then
                // 1. If both the old and newly discovered call are marked with tailrec, error
                throw IRError("multiple calls in the same branch marked with tailrec")
              else if isTailRecOld then
                // 2. old call is marked as tailrec so we must continue using it as the mod cons call.
                // make sure the newly discovered call does not use the current call as a parameter
                val argNames = args.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = namesOld.toSet
                val inters = argNames.intersect(namesSet)

                if inters.isEmpty then discoverOptimizableCalls(body) // OK
                else throw IRError("not a mod cons call") 
              else
                // old call is not tailrec, so we can override it however we want
                // we take a lucky guess and mark this as the mod cons call, but the
                // user really should mark which calls should be tailrec
                if defn.expectDefn.resultNum == 1 then
                  discoverOptimizableCalls(body)(acc, src, start, Some(defn.expectDefn), Some(x), None, Set())
                else
                  // shadow all the variables in this letcall
                  discoverOptimizableCalls(body)(acc, src, start, calledDefn, letCallNode, letCtorNode, containingCtors -- names)
        
      case AssignField(assignee, clsInfo, assignmentFieldName, value, body) =>
        // make sure `value` is not the mod cons call
        letCallNode match
          case None => discoverOptimizableCalls(body) // OK
          case Some(LetCall(names, defn, args, isTailRec, body)) =>
            value match
              case Expr.Ref(name) =>
                if names.contains(name) && isTailRec then throw IRError("not a mod cons call")
                  else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered
              case _ =>
                letCtorNode match
                  case None => discoverOptimizableCalls(body) // OK
                  case Some(LetCtorNodeInfo(_, ctor, _, name, fieldName)) =>
                    // If this assignment overwrites the mod cons value, forget it
                    if fieldName == assignmentFieldName && isTailRec then throw IRError("not a mod cons call")
                    else discoverOptimizableCalls(body)(acc, src, start, None, None, None, Set()) // invalidate everything that's been discovered

  // checks whether a list of names is equal to a list of trivial expressions referencing those names
  private def argsListEqual(names: List[Name], exprs: List[TrivialExpr]) =
    if names.length == exprs.length then
      val results = exprs.collect { case Expr.Ref(name) => name }
      names == results
    else
      false

  private def isIdentityJp(d: Defn): Bool = d.body match
    case Result(res) => argsListEqual(d.params, res)
    case Jump(defn, args) => argsListEqual(d.params, args) && isIdentityJp(defn.expectDefn)
    case _ => false

  private def isTailCall(node: Node): Boolean = node match
    case LetCall(names, defn, args, _, body) =>
      body match
        case Result(res)      => argsListEqual(names, res)
        case Jump(defn, args) => argsListEqual(names, args) && isIdentityJp(defn.expectDefn)
        case _                => false
    case _ => false

  private def discoverCallsCont(node: Node)(implicit src: Defn, acc: Map[Int, Set[CallInfo]]): Map[Int, Set[CallInfo]] =
    discoverOptimizableCalls(node)(acc, src, node, None, None, None, Set()) match
      case Left(acc) => acc
      case Right(nodes) => nodes.foldLeft(acc)((acc, node) => discoverCalls(node)(src, acc))

  private def discoverCalls(node: Node)(implicit src: Defn, acc: Map[Int, Set[CallInfo]]): Map[Int, Set[CallInfo]] = 
    val ret = discoverCallsCont(node)
    ret.get(src.id) match
      case None => ret + (src.id -> Set())
      case Some(value) => ret
  
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
    val inital = Map[Int, Set[CallInfo]]()
    val edges = defns.foldLeft(inital)((acc, defn) => discoverCalls(defn.defn.body)(defn.defn, acc)).withDefaultValue(Set())
    print(edges)

    var ctr = 0
    // nodes, edges
    var stack: List[(DefnNode, Set[CallInfo])] = Nil
    var sccs: List[DefnGraph] = Nil

    def dfs(src: DefnNode): Unit =
      src.num = ctr
      src.lowest = ctr
      ctr += 1
      src.visited = true
      
      val tailCalls = edges(src.defn.id)
      stack = (src, tailCalls) :: stack
      for u <- tailCalls do
        val neighbour = nodeMap(u.getDefn.id)
        if (neighbour.visited) then
          if (!neighbour.processed)
            src.lowest = neighbour.num.min(src.lowest)
        else
          dfs(neighbour)
          src.lowest = neighbour.lowest.min(src.lowest)
      

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
          sccEdges = edges ++ sccEdges
          
          val next = pop()
          vertex = next._1
          edges = next._2
        }

        scc = scc + vertex
        sccEdges = edges ++ sccEdges

        val sccIds = scc.map { d => d.defn.id }
        sccEdges = sccEdges.filter { c => sccIds.contains(c.getDefn.id)}

        val joinPoints = scc.foldLeft(Set[Defn]())((jps, defn) => discoverJoinPoints(defn.defn.body, jps))
        println(joinPoints.map(_.name))
        sccs = DefnGraph(scc, sccEdges, joinPoints) :: sccs
      
    for v <- defns do
      if (!v.visited)
        dfs(v)

    sccs
  

  private case class DefnInfo(defn: Defn, stackFrameIdx: Int)

  def asLit(x: Int) = Expr.Literal(IntLit(x))

  private def makeSwitch(scrutName: Name, cases: List[(Int, Node)], default: Node)(implicit trueClass: ClassInfo, falseClass: ClassInfo): Node =
    // given expressions value, e1, e2, transform it into
    // let scrut = tailrecBranch == value
    // in case scrut of True  -> e1
    //                  False -> e2
    def makeCaseBranch(value: Int, e1: Node, e2: Node): Node =
      val name = Name("scrut")
      val cases = Case(name, List((trueClass, e1), (falseClass, e2))).attachTag(tag)
      LetExpr(
        name,
        Expr.BasicOp("==", List(asLit(value), Expr.Ref(scrutName))),
        cases
      ).attachTag(tag)
      
    cases.foldLeft(default)((elz, item) => 
      val cmpValue = item._1
      val nodeIfTrue = item._2
      makeCaseBranch(cmpValue, nodeIfTrue, elz)
    )
  
  // TAIL RECURSION MOD CONS
  // Uses the ideas in section 2.2 of the paper `Tail Recursion Modulo Context` 
  // by Leijen and Lorenzen: https://dl.acm.org/doi/abs/10.1145/3571233
  // of whom attribute the method to Risch, Friedman, Wise, Minamide.

  final val ID_CONTEXT_NAME = "_IdContext"
  final val CONTEXT_NAME = "_Context"

  // `ctx` class for tailrec mod cons.
  // The paper uses two values `res: T` and `hole: ptr<T>` to represent the context. 
  // We represent the context as three values instead of two to avoid needing pointers:
  //
  // acc:       The accumulated value. This is the same as `res`  in the paper. If the functions f1, ..., fn
  //            in the compoennt return type T1, ..., Tn, then acc has type T1 | ... | Tn. 
  //
  // The following together represent `hole` in the paper:
  // ptr:       Represents the object containing the "hole" to be written to.
  // field:     Integer representing which class and field the "hole" belongs to. Which class and field this
  //            represents is different for each strongly connected component.
  final val ID_CTX_CLASS = ClassInfo(classUid.make, ID_CONTEXT_NAME, Nil)
  final val CTX_CLASS = ClassInfo(classUid.make, CONTEXT_NAME, List("acc", "ptr", "field"))
  
  // Given a strongly connected component `defns` of mutually mod cons functions,
  // returns a set containing mutually tail recursive versions of them and
  // the original functions pointing to the optimized ones. 
  private def optimizeModCons(component: ScComponent, classes: Set[ClassInfo]): (Set[Defn], Set[ClassInfo]) = 
    val modConsCalls = component.edges.collect { case x: ModConsCallInfo => x }
    val defns = component.nodes
    val defnsIdSet = defns.map(_.id).toSet

    // no mod cons, just return the original
    if modConsCalls.isEmpty then
      (component.nodes, classes)
    else
      val trueClass = classes.find(c => c.ident == "True").get
      val falseClass = classes.find(c => c.ident == "False").get
      
      // CONOTEXT APPLICATION

      val mergedNames = defns.foldLeft("")(_ + "_" + _.name)
      
      val ctxAppName = mergedNames + "_ctx_app"
      val ctxCompName = mergedNames + "_ctx_comp"
      
      // map integers to classes and fields which will be assigned to
      val classIdMap = classes.map(c => c.id -> c).toMap
      val possibleAssigns = modConsCalls.map(call => (call.letCtorNode.cls.id, call.letCtorNode.fieldName)).toSet
      val possibleAssignsIdxes = possibleAssigns.toList.zipWithIndex

      val assignToIdx = possibleAssignsIdxes.map((item, idx) => item -> idx).toMap

      // fun app(ctx, x: T): T
      val appCtxName = Name("ctx")
      val appValName = Name("x")

      val assignmentCases = possibleAssignsIdxes.map((item, idx) =>
        val clsId = item._1
        val fieldName = item._2
        val cls = classIdMap(clsId)
        
        // let ptr = ctx.ptr in
        // ptr.<fieldName> = x in
        // let acc = ctx.acc
        // acc
        val node = LetExpr(
          Name("ptr"), 
          Expr.Select(appCtxName, CTX_CLASS, "ptr"),
          AssignField(
            Name("ptr"), 
            cls, 
            fieldName, 
            Expr.Ref(appValName), 
            LetExpr(
              Name("acc"), 
              Expr.Select(appCtxName, CTX_CLASS, "acc"), // this could be a join point but it's not that bad
              Result(
                List(Expr.Ref(Name("acc")))
              ).attachTag(tag)
            ).attachTag(tag)
          ).attachTag(tag)
        ).attachTag(tag)

        (idx, node)
      )
      
      
      val ctxBranch = LetExpr(
        Name("field"), Expr.Select(appCtxName, CTX_CLASS, "field"),
        makeSwitch(Name("field"), assignmentCases.tail, assignmentCases.head._2)(trueClass, falseClass)
      )
      
      val idBranch = Result(List(Expr.Ref(appValName))).attachTag(tag)

      val appNode = Case(appCtxName,
        List(
          (ID_CTX_CLASS, idBranch),
          (CTX_CLASS, ctxBranch)
        )
      ).attachTag(tag)

      val appDefn = Defn(fnUid.make, ctxAppName, List(appCtxName, appValName), 1, appNode)

      // CONTEXT COMPOSITION
      val cmpCtx1Name = Name("ctx1")
      val cmpCtx2Name = Name("ctx2")

      // Note that ctx2 may never be an identity context. If we ever want to compose ctx1 and ctx2
      // where ctx2 is the identity, just use ctx1 directly.
      
      // Ctx(app(ctx1, ctx2), ctx2.ptr, ctx2.field) ->
      // let ctx2acc = ctx2.acc in
      // let ctx2ptr = ctx2.ptr in
      // let ctx2field = ctx2.field in
      // let newAcc = app(ctx1, ctx2acc) in
      // let ret = Ctx(newAcc, ctx2ptr, ctx2field) in
      // ret
      val cmpNode = LetExpr(
        Name("ctx2acc"), 
        Expr.Select(cmpCtx2Name, CTX_CLASS, "acc"),
        LetExpr(
          Name("ctx2ptr"), 
          Expr.Select(cmpCtx2Name, CTX_CLASS, "ptr"),
          LetExpr(
            Name("ctx2field"), 
            Expr.Select(cmpCtx2Name, CTX_CLASS, "field"),
            LetCall(
              List(Name("newAcc")), 
              DefnRef(Left(appDefn)), List(Expr.Ref(cmpCtx1Name), Expr.Ref(Name("ctx2acc"))),
              false,
              LetExpr(
                Name("ret"), 
                Expr.CtorApp(CTX_CLASS, List("newAcc", "ctx2ptr", "ctx2field").map(n => Expr.Ref(Name(n)))),
                Result(
                  List(Expr.Ref(Name("ret")))
                ).attachTag(tag)
              ).attachTag(tag),
            ).attachTag(tag)
          ).attachTag(tag)
        ).attachTag(tag)
      ).attachTag(tag)

      val cmpDefn = Defn(fnUid.make, ctxCompName, List(cmpCtx1Name, cmpCtx2Name), 1, cmpNode)

      // We use tags to identify nodes
      // a bit hacky but it's the most elegant way
      // First, build a map of all branches that contain a mod cons call
      val modConsBranches = modConsCalls.toList.map(call => (call.startNode.tag.inner -> call)).toMap
      
      val MOD_CONS_PTR_NAME = Name("_mod_cons_ptr")

      val modConsMap = defns.map(d => d.id -> DefnRef(Right(d.name + "_modcons"))).toMap
      
      def transformModConsBranch(node: Node, call: ModConsCallInfo): (Node, Set[Defn]) = 
        
        def makeCall =
          val field = assignToIdx((call.letCtorNode.cls.id, call.letCtorNode.fieldName))
          
          // let composed = comp(ctx, ctx2) in
          // f(composed, *args)
          LetExpr(
            Name("ctx2"),
            Expr.CtorApp(CTX_CLASS, List(Expr.Ref(call.retName), Expr.Ref(call.letCtorNode.ctorValName), asLit(field))),
            LetCall(
              List(Name("composed")),
              DefnRef(Left(cmpDefn)),
              List("ctx", "ctx2").map(n => Expr.Ref(Name(n))),
              false,
              LetCall(
                List(Name("res")), 
                modConsMap(call.defn.id),
                Expr.Ref(Name("composed")) :: call.letCallNode.args, // TODO: change
                false,
                Result(
                  List(Expr.Ref(Name("res")))
                ).attachTag(tag)
              ).attachTag(tag)
            ).attachTag(tag)
          ).attachTag(tag)

        node match
          case Result(res) => (node, Set())
          case Jump(defn, args) => ???
          case Case(scrut, cases) => ???
          case LetExpr(name, expr, body) => ???
          case LetCall(names, defn, args, isTailRec, body) => ???
          case AssignField(assignee, clsInfo, fieldName, value, body) => ???
      
      // Here, we assume we are inside the modcons function and hence have an extra
      // `ctx` parameter at the start.
      def transformNode(node: Node): (Node, Set[Defn]) = 
        modConsBranches.get(node.tag.inner) match
          case Some(call) => transformModConsBranch(node, call)
          case None => node match
            case Result(_) => (node.attachTag(tag), Set())
            case Jump(_, _) => (node.attachTag(tag), Set())
            case Case(scrut, cases) => 
              val casesAndDefns = cases.map { (cls, body) => (cls, transformNode(body)) }

              val transformedCases = casesAndDefns.map { (cls, item) => (cls, item._1) } 
              val newDefns: Set[Defn] = casesAndDefns.map((_, item) => item._2).foldLeft(Set())((a, b) => a ++ b)

              (Case(scrut, transformedCases).attachTag(tag), newDefns)
            case LetExpr(name, expr, body) => 
              val (transformed, newDefns) = transformNode(body)
              (LetExpr(name, expr, transformed).attachTag(tag), newDefns)
            case LetCall(names, defn, args, isTailRec, body) =>
              // This case is not handled by the paper. The way to transform this is: 
              // let res = foo(*args) in res
              // --> let res = foo_modcons(ctx, *args) in res
              if isTailCall(node) && defnsIdSet.contains(defn.expectDefn.id) then
                // Transform it into a tail recursive call where we pass on the current context
                (
                  LetCall(
                    List(Name("res")), 
                    modConsMap(defn.expectDefn.id), Expr.Ref(Name("ctx")) :: args, 
                    isTailRec,
                    Result(List(Expr.Ref(Name("res"))))
                  ),
                  Set()
                )
              else 
                val (transformed, newDefns) = transformNode(body)
                (LetCall(names, defn, args, isTailRec, transformed).attachTag(tag), newDefns)
            case AssignField(assignee, clsInfo, fieldName, value, body) => 
              val (transformed, newDefns) = transformNode(body)
              (AssignField(assignee, clsInfo, fieldName, value, transformed).attachTag(tag), newDefns)

      // will create two definitions: one has the same signature as the original function,
      // while the other one will have extra parameters to support mod cons

      // We will need to rewrite join points, thus new definitions may be created.
      def transformDefn(d: Defn): Set[Defn] =
        val (transformed, newDefns) = transformNode(d.body)
        newDefns + Defn(fnUid.make, d.name + "_modcons", Name("ctx") :: d.params, d.resultNum, transformed)

      ???
        


  // Given a strongly connected component `defns` of mutually
  // tail recursive functions, returns a set containing the optimized function and the
  // original functions pointing to an optimized function.
  private def optimizeTailRec(component: ScComponent, classes: Set[ClassInfo]): Set[Defn] = 
    // println(component.edges)
    // To build the case block, we need to compare integers and check if the result is "True"
    val trueClass = classes.find(c => c.ident == "True").get
    val falseClass = classes.find(c => c.ident == "False").get
    
    // join points need to be rewritten. For now, just combine them into the rest of the function. They will be inlined anyways
    val defns = component.nodes ++ component.joinPoints
    val defnsNoJp = component.nodes
    val edges = component.edges

    // dummy case, should not happen
    if (defns.size == 0)
      return defns

    // for single tail recursive functions, just move the body into a join point
    if (defns.size <= 1)
      val defn = defns.head
      
      // if the function does not even tail call itself, just return
      if edges.size == 0 then
        return defns
      
      val jpName = defn.name + "_jp"
      val jpDefnRef = DefnRef(Right(jpName))
      
      def transformNode(node: Node): Node = node match
        case Result(res) => node.attachTag(tag)
        case Jump(defn, args) => node.attachTag(tag)
        case Case(scrut, cases) => Case(scrut, cases.map((cls, body) => (cls, transformNode(body)))).attachTag(tag)
        case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body)).attachTag(tag)
        case LetCall(names, defn_, args, isTailRec, body) =>
          if isTailCall(node) && defn_.expectDefn.id == defn.id then
            Jump(jpDefnRef, args).attachTag(tag)
          else
            LetCall(names, defn_, args, isTailRec, transformNode(body)).attachTag(tag)
        case AssignField(assignee, clsInfo, fieldName, value, body) => 
          AssignField(assignee, clsInfo, fieldName, value, transformNode(body)).attachTag(tag)
      
      val jpDef = Defn(fnUid.make, jpName, defn.params, defn.resultNum, transformNode(defn.body))
      
      val rets = (0 until defn.resultNum).map(n => Name("r" + n.toString)).toList
      val callJpNode = LetCall(
        rets, 
        DefnRef(Left(jpDef)),
        defn.params.map(Expr.Ref(_)),
        false,
        Result(rets.map(Expr.Ref(_))).attachTag(tag),
      ).attachTag(tag)
      
      val newDefn = Defn(fnUid.make, defn.name, defn.params, defn.resultNum, callJpNode)
      Set(newDefn, jpDef)

    else
      // Note that we do not use the actual edges in ScCompoennt here.
      // We assume the only things we can optimize are tail calls, which
      // are cheap to identify, and nothing else.

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
        case Jump(defn, args)          =>
          if defnInfoMap.contains(defn.expectDefn.id) then
            Jump(jpDefnRef, transformStackFrame(args, defnInfoMap(defn.expectDefn.id))).attachTag(tag)
          else
            node.attachTag(tag)
        case Result(_)                 => node.attachTag(tag)
        case Case(scrut, cases)        => Case(scrut, cases.map(n => (n._1, transformNode(n._2)))).attachTag(tag)
        case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body)).attachTag(tag)
        case LetCall(names, defn, args, isTailRec, body) =>
          if isTailCall(node) && defnInfoMap.contains(defn.expectDefn.id) then
            Jump(jpDefnRef, transformStackFrame(args, defnInfoMap(defn.expectDefn.id))).attachTag(tag)
          else LetCall(names, defn, args, isTailRec, transformNode(body)).attachTag(tag)
        case AssignField(assignee, clsInfo, field, value, body) => AssignField(assignee, clsInfo, field, value, transformNode(body)).attachTag(tag)

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
        val call = LetCall(names, newDefnRef, args, false, res).attachTag(tag)
        Defn(defn.id, defn.name, defn.params, defn.resultNum, call)

      def getOrKey[T](m: Map[T, T])(key: T): T = m.get(key) match
        case None        => key
        case Some(value) => value

      val first = defnsList.head;
      val firstMap = nameMaps(first.id)
      val firstBodyRenamed = first.body.mapName(getOrKey(firstMap))
      val firstNode = transformNode(firstBodyRenamed)

      val valsAndNodes = defnsList.map(defn =>
        val nmeMap = nameMaps(defn.id)
        val renamed = defn.body.mapName(getOrKey(nmeMap))
        val transformed = transformNode(renamed)
        (defn.id, transformed)
      )

      val newNode = makeSwitch(trName, valsAndNodes.tail, valsAndNodes.head._2)(trueClass, falseClass)

      val jpDefn = Defn(fnUid.make, jpName, stackFrame, resultNum, newNode)

      val jmp = Jump(jpDefnRef, stackFrame.map(Expr.Ref(_))).attachTag(tag)
      val newDefn = Defn(fnUid.make, newName, stackFrame, resultNum, jmp)

      // This is the definition that will be called
      // val createIntermidDefn =

      jpDefnRef.defn = Left(jpDefn)
      newDefnRef.defn = Left(newDefn)

      defnsNoJp.map { d => transformDefn(d) } + newDefn + jpDefn
  
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