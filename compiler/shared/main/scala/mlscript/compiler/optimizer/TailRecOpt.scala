package mlscript
package compiler.optimizer

import scala.annotation.tailrec

import utils.shorthands._
import Message.MessageContext

import compiler.ir._
import compiler.ir.Node._

/*

DOCUMENTATION OF SEMANTICS OF @tailcall and @tailrec

@tailcall: Used to annotate specific function calls. Calls annotated with @tailcall 
must be tail calls or tail modulo-cons calls. These calls must be optimized to not
consume additional stack space. If such an optimization is not possible, then the
compiler will throw an error.

If there are multiple possible candidates for tail modulo-cons calls in a single
branch of an expression, then @tailcall can be uesd to indicate which one will be
optimized. For instance in

fun foo() =
  A(foo(), bar())

we can use @tailcall to annotate the call foo() or bar(). If a call other than the
last call is annotated with @tailcall, then the remaining functions must be pure
to ensure that reordering computations does not change the result.

If bar() is impure but you still want to optimize the call foo(), then you can do

fun foo() =
  let b = bar()
  let a = @tailcall foo()
  A(a, b)

because here, you are taking responsibility for the reordering of the computations.

@tailrec: Used to annotate functions. When this annotation is used on a function, say
@tailrec fun foo(), the compiler will ensure no sequence of direct recursive calls back 
to foo() consume stack space, i.e. they are all tail calls. Note that a call to foo() 
may consume an arbitrary amount of stack space as long as foo() is only consuming finite
stack space. For example,

@tailrec fun foo() = bar()
fun bar() =
  bar()
  bar()

is valid. However,

@tailrec fun foo() = bar()
fun bar() =
  foo()
  bar()

is invalid. If we swap the position of foo() and bar() in the body of bar, it is still invalid.

Equivalently, if fun foo() is annotated with @tailrec, let S be the largest strongly
connected component in the call-graph of the program that contains foo. Then an error
will be thrown unless all edges (calls) connecting the nodes of the strongly
connected component are tail calls or tail modulo-cons calls.

*/

// fnUid should be the same FreshInt that was used to build the graph being passed into this class
class TailRecOpt(fnUid: FreshInt, classUid: FreshInt, tag: FreshInt, raise: Diagnostic => Unit):
  case class LetCtorNodeInfo(node: LetExpr, ctor: Expr.CtorApp, cls: ClassInfo, ctorValName: Name, fieldName: String, idx: Int)

  enum CallInfo:
    case NormalCallInfo(src: Defn, defn: Defn)(val loc: Option[Loc]) extends CallInfo
    case TailCallInfo(src: Defn, defn: Defn) extends CallInfo
    case ModConsCallInfo(src: Defn, startNode: Node, defn: Defn, letCallNode: LetCall, letCtorNode: LetCtorNodeInfo, retName: Name, retNode: Node) extends CallInfo

    override def toString(): String = this match
      case NormalCallInfo(src, defn) =>
        f"Call { ${src.name}$$${src.id} -> ${defn.name}$$${defn.id} }"
      case TailCallInfo(src, defn) => 
        f"TailCall { ${src.name}$$${src.id} -> ${defn.name}$$${defn.id} }"
      case ModConsCallInfo(src, startNode, defn, letCallNode, letCtorNode, _, _) =>
        f"ModConsCall { ${src.name}$$${src.id} -> ${defn.name}$$${defn.id}, class: ${letCtorNode.cls.name}, field: ${letCtorNode.fieldName} }"

    def getSrc = this match
      case NormalCallInfo(src, _) => src 
      case TailCallInfo(src, _) => src
      case ModConsCallInfo(src, _, _, _, _, _, _) => src 

    def getDefn = this match
      case NormalCallInfo(_, defn) => defn
      case TailCallInfo(_, defn) => defn
      case ModConsCallInfo(_, _, defn, _, _, _, _) => defn
    
  private class DefnGraph(val nodes: Set[DefnNode], val edges: Set[CallInfo], val joinPoints: Set[Defn]):
    def removeMetadata: ScComponent = ScComponent(nodes.map(_.defn), edges, joinPoints)
  
  private class ScComponent(val nodes: Set[Defn], val edges: Set[CallInfo], val joinPoints: Set[Defn])

  import CallInfo._

  def filterOptCalls(calls: Iterable[CallInfo]) =
    calls.collect { case c: TailCallInfo => c; case c: ModConsCallInfo => c }

  def filterNormalCalls(calls: Iterable[CallInfo]) =
    calls.collect { case c: NormalCallInfo => c }

  // Hack to make scala think discoverJoinPoints is tail recursive and be
  // partially optimized :P
  def casesToJps(cases: List[(Pat, Node)], default: Opt[Node], acc: Set[Defn]): Set[Defn] =
    cases.foldLeft(default.fold(acc)(x => discoverJoinPoints(x, acc)))((jps, branch) => discoverJoinPoints(branch._2, jps))
  
  def discoverJoinPointsCont(defn: Defn, acc: Set[Defn]) =
    discoverJoinPoints(defn.body, acc) + defn

  // TODO: implement proper purity checking. This is a very simple purity check that only allows the last
  // parameter of a mod cons call to be optimised.
  private val pureCache: scala.collection.mutable.Map[Int, Bool] = scala.collection.mutable.Map[Int, Bool]()
  private def isPure(node: Node): Bool = 
    pureCache.get(node.tag.inner) match
      case None => 
        val ret = node match
          case Jump(defn, args) => isIdentityJp(defn.expectDefn)
          case _: LetCall => false
          case LetMethodCall(names, cls, method, args, body) => false
          case Case(scrut, cases, default) => cases.foldLeft(default.fold(false)(isPure))((value, branch) => value && isPure(branch._2))
          case LetExpr(name, expr: Expr.AssignField, body) => false
          case x: LetExpr => true
          case Result(res) => true
        pureCache.put(node.tag.inner, ret)
        ret
    
      case Some(value) => value

    


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
      case Case(scrut, cases, default) => casesToJps(cases, default, acc)
      case LetExpr(name, expr, body) => discoverJoinPoints(body, acc)
      case LetMethodCall(names, cls, method, args, body) => discoverJoinPoints(body, acc)
      case LetCall(names, defn, args, isTailRec, body) => discoverJoinPoints(body, acc)

  private def getRetName(names: Set[Name], retVals: List[TrivialExpr]): Option[Name] =
    val names = retVals.collect { case Expr.Ref(nme) => nme }
    if names.length != 1 then None
    else
      val nme = names.head
      if names.contains(nme) then Some(nme)
      else None

  // would prefer to have this inside discoverOptCalls, but scala does not support partially tail recursive functions directly
  def shadowAndCont(next: Node, nme: Name)(implicit
    acc: Set[CallInfo],
    src: Defn,
    scc: Set[Defn],
    start: Node,
    calledDefn: Option[Defn],
    letCallNode: Option[LetCall],
    letCtorNode: Option[LetCtorNodeInfo],
    containingCtors: Set[Name]
  ) = searchOptCalls(next)(acc, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors - nme) 

  // same here...
  def invalidateAndCont(body: Node)(implicit
    acc: Set[CallInfo],
    src: Defn,
    scc: Set[Defn],
    start: Node,
    calledDefn: Option[Defn],
    letCallNode: Option[LetCall],
    letCtorNode: Option[LetCtorNodeInfo],
    containingCtors: Set[Name]
  ) =
    letCallNode match
      case None => searchOptCalls(body)(acc, src, scc, start, None, None, None, Set()) // invalidate everything that's been discovered
      case Some(x: LetCall) =>
        val LetCall(_, defn, _, isTailRec, _) = x
        if isTailRec then 
          raise(ErrorReport(List(msg"not a tail call" -> x.loc), true, Diagnostic.Compilation))

        val newAcc = acc + NormalCallInfo(src, defn.expectDefn)(x.loc)
        searchOptCalls(body)(newAcc, src, scc, start, None, None, None, Set()) // invalidate everything that's been discovered
  
  @tailrec
  private def searchOptCalls(node: Node)(implicit
    acc: Set[CallInfo],
    src: Defn,
    scc: Set[Defn],
    start: Node,
    calledDefn: Option[Defn], // The definition that was called in a tailrec mod cons call
    letCallNode: Option[LetCall], // The place where that definition was called
    letCtorNode: Option[LetCtorNodeInfo], // The place where the result from that call was put into a constructor
    containingCtors: Set[Name], // Value names of ctors containing the constructor containing the result from the call
  ): Either[Set[CallInfo], List[Node]] = 

    def updateMapSimple(c: CallInfo) = acc + c

    def returnNoneCont = calledDefn match
      case None => Left(acc)
      case Some(dest) => 
        Left(updateMapSimple(NormalCallInfo(src, dest)(letCallNode.flatMap(_.loc)))) // treat the discovered call as a normal call

    def returnNone = letCallNode match
      case Some(x: LetCall) =>
        val LetCall(_, _, _, isTailRec, _) = x
        if isTailRec then
          raise(ErrorReport(List(msg"not a tail call" -> x.loc), true, Diagnostic.Compilation))
        returnNoneCont
      case _ => returnNoneCont

    node match // Left if mod cons call found, Right if none was found -- we return the next nodes to be scanned 
      case Result(res) =>
        (calledDefn, letCallNode, letCtorNode) match
          case (Some(defn), Some(letCallNode), Some(letCtorName)) =>
            getRetName(containingCtors, res) match
              case None => returnNone
              case Some(value) => Left(updateMapSimple(ModConsCallInfo(src, start, defn, letCallNode, letCtorName, value, node)))
          case _ => returnNone
      case Jump(jp, args) => 
        // different cases
        (calledDefn, letCallNode, letCtorNode) match
          case (Some(defn), Some(letCallNode), Some(letCtorName)) =>
            getRetName(containingCtors, args) match
              case Some(value) if isIdentityJp(jp.expectDefn) => 
                Left(updateMapSimple(ModConsCallInfo(src, start, defn, letCallNode, letCtorName, value, node)))
              case _ => returnNone
          case _ => returnNone
        
      case Case(scrut, cases, default) => Right(cases.map(_._2) ++ default.toList)
      case x @ LetExpr(name, expr, body) =>
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
                  invalidateAndCont(body)
                else
                  shadowAndCont(body, name) // OK
          
          case Expr.Literal(lit) => shadowAndCont(body, name) // OK
          case y @ Expr.CtorApp(clsInfo, ctorArgs) =>
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
                    searchOptCalls(body)(acc, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors + name) 
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

                      val fieldName = clsInfo.expectClass.fields(ctorArgIndex)
                      
                      // populate required values
                      searchOptCalls(body)(acc, src, scc, start, calledDefn, letCallNode, Some(LetCtorNodeInfo(x, y, clsInfo.expectClass, name, fieldName, ctorArgIndex)), Set(name))
                    case Some(_) =>
                      // another constructor is already using the call. Not OK

                      // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                      // invalidate the discovered call and continue
                      invalidateAndCont(body)

          case Expr.Select(name, cls, field) =>
            letCallNode match
              case None => shadowAndCont(body, name) // OK
              case Some(LetCall(names, _, _, isTailRec, _)) =>
                // for it to be mod cons, other values cannot use the return value from the call.
                if names.contains(name) then
                  // if the is marked as tail recursive, we must use that call as the mod cons call, so error. otherwise,
                  // invalidate the discovered call and continue
                  invalidateAndCont(body)
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
                  invalidateAndCont(body)
          case Expr.AssignField(assignee, clsInfo, assignmentFieldName, value) =>
            // make sure `value` is not the mod cons call
            letCallNode match
              case None => searchOptCalls(body) // OK
              case Some(LetCall(names, defn, args, isTailRec, _)) =>
                value match
                  case Expr.Ref(name) =>
                    invalidateAndCont(body)
                  case _ =>
                    letCtorNode match
                      case None => searchOptCalls(body) // OK
                      case Some(LetCtorNodeInfo(_, ctor, _, name, fieldName, _)) =>
                        // If this assignment overwrites the mod cons value, forget it
                        if containingCtors.contains(assignee) then invalidateAndCont(body)
                        else searchOptCalls(body)
      case LetMethodCall(names, cls, method, args, body) =>
        // method call is unresolved, just ignore it
        // `containingCtors -- names.toSet` takes care of variable shadowing
        searchOptCalls(body)(acc, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors -- names.toSet)
      case x @ LetCall(names, defn, args, isTailRec, body) =>
        val callInScc = scc.contains(defn.expectDefn)
        
        // Only deal with calls in the scc
        if callInScc && isTailCall(x) then
          // If there is an old call marked as @tailcall, it cannot be a tail call, error

          val updatedMap = letCallNode match
            case Some(y) =>
              // If both these calls are marked @tailrec, error
              if y.isTailRec && x.isTailRec then
                raise(ErrorReport(
                  List(
                    msg"multiple calls in the same branch marked with @tailcall" -> None,
                    msg"first call" -> y.loc,
                    msg"second call" -> x.loc,
                  ),
                  true,
                  Diagnostic.Compilation
                  )
                )
              if y.isTailRec then
                raise(ErrorReport(List(msg"not a tail call" -> y.loc), true, Diagnostic.Compilation)) 

              updateMapSimple(NormalCallInfo(src, y.defn.expectDefn)(y.loc))

            case None => acc
            
          Left(updatedMap + TailCallInfo(src, defn.expectDefn))
        else
          val restIsPure = isPure(body)
          letCallNode match
            case None => // OK, we may use this LetCall as the mod cons
              // For now, only optimize functions which return one value
              if callInScc && defn.expectDefn.resultNum == 1 && restIsPure then
                searchOptCalls(body)(acc, src, scc, start, Some(defn.expectDefn), Some(x), None, Set())
              else
                if isTailRec then
                  if !restIsPure then
                    raise(ErrorReport(List(msg"not a tail call, as the remaining functions may be impure" -> x.loc), true, Diagnostic.Compilation))
                  else
                    raise(ErrorReport(List(msg"not a tail call" -> x.loc), true, Diagnostic.Compilation)) 
                  
                // Treat this as a normal call
                val newMap = updateMapSimple(NormalCallInfo(src, defn.expectDefn)(x.loc))
                searchOptCalls(body)(newMap, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors)
            case Some(y: LetCall) =>
              val LetCall(namesOld, defnOld, argsOld, isTailRecOld, bodyOld) = y
              if isTailRecOld then
                // 1. If both the old and newly discovered call are marked with tailrec, error
                if isTailRec then 
                  raise(ErrorReport(
                    List(
                      msg"multiple calls in the same branch marked with @tailcall" -> None,
                      msg"first call" -> y.loc,
                      msg"second call" -> x.loc,
                    ),
                    true,
                    Diagnostic.Compilation
                    )
                  )
                // 2. old call is marked as tailrec so we must continue using it as the mod cons call.
                // make sure the newly discovered call does not use the current call as a parameter
                val argNames = args.collect { case Expr.Ref(name) => name }.toSet
                val namesSet = namesOld.toSet
                val inters = argNames.intersect(namesSet)

                if !inters.isEmpty then
                  raise(ErrorReport(List(msg"not a tail call" -> y.loc), true, Diagnostic.Compilation)) 
                // Treat new call as a normal call
                val newMap = updateMapSimple(NormalCallInfo(src, defn.expectDefn)(x.loc))
                searchOptCalls(body)(newMap, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors) // OK
              else
                // only include mod cons calls that have one return value
                if callInScc && defn.expectDefn.resultNum == 1 && restIsPure then 
                  // old call is not tailrec, so we can override it however we want
                  // we take a lucky guess and mark this as the mod cons call, but the
                  // user really should mark which calls should be tailrec
                    
                  // Treat the old call as a normal call
                  val newMap = updateMapSimple(NormalCallInfo(src, defnOld.expectDefn)(y.loc))
                  searchOptCalls(body)(newMap, src, scc, start, Some(defn.expectDefn), Some(x), None, Set())
                else
                  if isTailRec then
                    if !restIsPure then
                      raise(ErrorReport(List(msg"not a tail call, as the remaining functions may be impure" -> x.loc), true, Diagnostic.Compilation))
                    else
                      raise(ErrorReport(List(msg"not a tail call" -> x.loc), true, Diagnostic.Compilation)) 
                  // shadow all the variables in this letcall
                  
                  // Treat this as a normal call
                  val newMap = updateMapSimple(NormalCallInfo(src, defn.expectDefn)(x.loc))
                  searchOptCalls(body)(acc, src, scc, start, calledDefn, letCallNode, letCtorNode, containingCtors -- names)

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

  private def discoverOptCallsNode(node: Node)(implicit src: Defn, scc: Set[Defn], acc: Set[CallInfo]): Set[CallInfo] = 
    searchOptCalls(node)(acc, src, scc, node, None, None, None, Set()) match
      case Left(acc) => acc
      case Right(nodes) => nodes.foldLeft(acc)((acc, node) => discoverOptCallsNode(node)(src, scc, acc))

  private def discoverOptCalls(defn: Defn, jps: Set[Defn])(implicit scc: Set[Defn], acc: Set[CallInfo]): Set[CallInfo] =
    val combined = jps + defn
    combined.foldLeft(acc)((acc, defn_) => discoverOptCallsNode(defn_.body)(defn, scc, acc))

  private def searchCalls(node: Node)(implicit src: Defn, acc: Map[Int, Set[Defn]]): Map[Int, Set[Defn]] =
    node match
      case Result(res) => acc
      case Jump(defn, args) => acc
      case Case(scrut, cases, default) => cases.foldLeft(default.fold(acc)(x => searchCalls(x)(src, acc)))((acc, item) => searchCalls(item._2)(src, acc))
      case LetExpr(name, expr, body) => searchCalls(body)
      case LetMethodCall(names, cls, method, args, body) => searchCalls(body)
      case LetCall(names, defn, args, isTailRec, body) => 
        val newSet = acc.get(src.id) match
          case None => Set(defn.expectDefn)
          case Some(defns) => defns + defn.expectDefn
        searchCalls(body)(src, acc + (src.id -> newSet))
    

  private def discoverCalls(defn: Defn, jps: Set[Defn])(implicit acc: Map[Int, Set[Defn]]): Map[Int, Set[Defn]] =
    val combined = jps + defn
    combined.foldLeft(acc)((acc, defn_) => searchCalls(defn_.body)(defn, acc))
  
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
    val inital = Map[Int, Set[Defn]]()
    val joinPoints = defns.map(d => (d.defn.id -> discoverJoinPoints(d.defn.body, Set()))).toMap
    val allJoinPoints = joinPoints.values.flatMap(x => x).toSet
    val edges = defns.foldLeft(inital)((acc, defn) => discoverCalls(defn.defn, joinPoints(defn.defn.id))(acc)).withDefaultValue(Set())

    var ctr = 0
    // nodes, edges
    var stack: List[DefnNode] = Nil
    var sccs: List[DefnGraph] = Nil

    def dfs(src: DefnNode): Unit =
      src.num = ctr
      src.lowest = ctr
      ctr += 1
      src.visited = true
      
      val tailCalls = edges(src.defn.id)
      stack = src :: stack
      for u <- tailCalls do
        val neighbour = nodeMap(u.id)
        if (neighbour.visited) then
          if (!neighbour.processed)
            src.lowest = neighbour.num.min(src.lowest)
        else
          dfs(neighbour)
          src.lowest = neighbour.lowest.min(src.lowest)
      

      src.processed = true

      if (src.num == src.lowest) then
        var scc: Set[DefnNode] = Set()

        def pop(): DefnNode =
          val ret = stack.head
          stack = stack.tail
          ret
        

        var vertex = pop()

        while (vertex != src) {
          scc = scc + vertex
          
          val next = pop()
          vertex = next
        }

        scc = scc + vertex

        val sccIds = scc.map { d => d.defn.id }

        val sccJoinPoints = scc.foldLeft(Set[Defn]())((jps, defn) => joinPoints(defn.defn.id))

        val sccDefns = scc.map(d => d.defn)

        val categorizedEdges = scc
          .foldLeft(Set[CallInfo]())(
            (calls, defn) => discoverOptCalls(defn.defn, joinPoints(defn.defn.id))(sccDefns, calls)
          )
          .filter(c => sccDefns.contains(c.getDefn))

        sccs = DefnGraph(scc, categorizedEdges, sccJoinPoints) :: sccs
      
    for v <- defns do
      if !allJoinPoints.contains(v.defn) && !v.visited then
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
      val cases = Case(name, List((Pat.Class(ClassRef(L(trueClass))), e1), (Pat.Class(ClassRef(L(falseClass))), e2)), None).attachTag(tag)
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
  //
  // The idea to use `ptr` and `field` to represent a pointer is by @LPTK.
  final val ID_CTX_CLASS = ClassInfo(classUid.make, ID_CONTEXT_NAME, Nil)
  final val CTX_CLASS = ClassInfo(classUid.make, CONTEXT_NAME, List("acc", "ptr", "field"))
  final val ID_CTX_CLASS_REF = ClassRef(L(ID_CTX_CLASS))
  final val CTX_CLASS_REF = ClassRef(L(CTX_CLASS))
  
  // Given a strongly connected component `defns` of mutually
  // tail recursive functions, returns a strongly connected component contaning the
  // optimized functions and their associated join points, and also
  // new function definitions not in this component, such as the
  // original functions pointing to an optimized function and the context
  // composition and application functions.
  private def optimizeModCons(component: ScComponent, classes: Set[ClassInfo]): (ScComponent, Set[Defn]) = 
    val modConsCalls = component.edges.collect { case x: ModConsCallInfo => x }
    val defns = component.nodes
    val defnsIdSet = defns.map(_.id).toSet

    // no mod cons, just return the original
    if modConsCalls.isEmpty then
      (component, Set())
    else
      val trueClass = classes.find(c => c.name == "True").get
      val falseClass = classes.find(c => c.name == "False").get
      
      // CONTEXT APPLICATION
      
      val mergedNames = defns.foldLeft("")(_ + "_" + _.name)
      
      val ctxAppId = fnUid.make
      val ctxAppName = mergedNames + "_ctx_app$" + ctxAppId
      val ctxCompId = fnUid.make
      val ctxCompName = mergedNames + "_ctx_comp$" + ctxCompId
      
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
          Expr.Select(appCtxName, CTX_CLASS_REF, "ptr"),
          LetExpr(
            Name("_"), 
            Expr.AssignField(
              Name("ptr"), 
              ClassRef(L(cls)), 
              fieldName, 
              Expr.Ref(appValName)
            ),
            LetExpr(
              Name("acc"), 
              Expr.Select(appCtxName, CTX_CLASS_REF, "acc"), // this could be a join point but it's not that bad
              Result(
                List(Expr.Ref(Name("acc")))
              ).attachTag(tag)
            ).attachTag(tag)
          ).attachTag(tag)
        ).attachTag(tag)

        (idx, node)
      )
      
      
      val ctxBranch = LetExpr(
        Name("field"), Expr.Select(appCtxName, CTX_CLASS_REF, "field"),
        makeSwitch(Name("field"), assignmentCases.tail, assignmentCases.head._2)(trueClass, falseClass)
      ).attachTag(tag)
      
      val idBranch = Result(List(Expr.Ref(appValName))).attachTag(tag)

      val appNode = Case(appCtxName,
        List(
          (Pat.Class(ID_CTX_CLASS_REF), idBranch),
          (Pat.Class(CTX_CLASS_REF), ctxBranch)
        ),
        None
      ).attachTag(tag)

      val appDefn = Defn(ctxAppId, ctxAppName, List(appCtxName, appValName), 1, appNode, false)

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
        Expr.Select(cmpCtx2Name, CTX_CLASS_REF, "acc"),
        LetExpr(
          Name("ctx2ptr"), 
          Expr.Select(cmpCtx2Name, CTX_CLASS_REF, "ptr"),
          LetExpr(
            Name("ctx2field"), 
            Expr.Select(cmpCtx2Name, CTX_CLASS_REF, "field"),
            LetCall(
              List(Name("newAcc")), 
              DefnRef(Left(appDefn)), List(Expr.Ref(cmpCtx1Name), Expr.Ref(Name("ctx2acc"))),
              false,
              LetExpr(
                Name("ret"), 
                Expr.CtorApp(CTX_CLASS_REF, List("newAcc", "ctx2ptr", "ctx2field").map(n => Expr.Ref(Name(n)))),
                Result(
                  List(Expr.Ref(Name("ret")))
                ).attachTag(tag)
              ).attachTag(tag),
            )().attachTag(tag)
          ).attachTag(tag)
        ).attachTag(tag)
      ).attachTag(tag)

      val cmpDefn = Defn(ctxCompId, ctxCompName, List(cmpCtx1Name, cmpCtx2Name), 1, cmpNode, false)

      // We use tags to identify nodes
      // a bit hacky but it's the most elegant way
      // First, build a map of all branches that contain a mod cons call
      val modConsBranches = modConsCalls.toList.map(call => (call.startNode.tag.inner -> call)).toMap

      val modConsRefs = defns.map(d => d.id -> DefnRef(Right(d.name + "_modcons"))).toMap
      val jpRefs = component.joinPoints.map(jp => jp.id -> DefnRef(Right(jp.name + "_modcons"))).toMap

      def makeRet(ret: TrivialExpr): Node =
        LetCall(
          List(Name("res")),
          DefnRef(Left(appDefn)),
          List(Expr.Ref(Name("ctx")), ret),
          false,
          Result(List(Expr.Ref(Name("res")))).attachTag(tag)
        )().attachTag(tag)
      
      // Here, we assume we are inside the modcons version of the function and hence have an extra
      // `ctx` parameter at the start.
      def transformNode(node: Node): Node = 
        modConsBranches.get(node.tag.inner) match
          case Some(call) => transformModConsBranch(node)(call)
          case None => node match
            case Result(res) => 
              makeRet(res.head)
            case Jump(defn, args) => 
              if isIdentityJp(defn.expectDefn) then makeRet(args.head) 
              else jpRefs.get(defn.expectDefn.id) match
                case None => throw IRError("could not find jump point with id" + defn.expectDefn.id)
                case Some(value) => Jump(value, Expr.Ref(Name("ctx")) :: args)
              
            case Case(scrut, cases, default) => Case(scrut, cases.map { (cls, body) => (cls, transformNode(body)) }, default.map(transformNode)).attachTag(tag)
            case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body)).attachTag(tag)
            case LetMethodCall(names, cls, method, args, body) => LetMethodCall(names, cls, method, args, transformNode(body)).attachTag(tag)
            case LetCall(names, defn, args, isTailRec, body) =>
              // Handle the case when we see a tail call.
              // This case is not handled by the paper. The way to transform this is: 
              // let res = foo(*args) in res
              // --> let res = foo_modcons(ctx, *args) in res
              if isTailCall(node) && defnsIdSet.contains(defn.expectDefn.id) then
                // Transform it into a tail recursive call where we pass on the current context
                LetCall(
                  List(Name("res")), 
                  modConsRefs(defn.expectDefn.id), Expr.Ref(Name("ctx")) :: args, 
                  isTailRec,
                  Result(List(Expr.Ref(Name("res")))).attachTag(tag)
                )().attachTag(tag)
              else 
                LetCall(names, defn, args, isTailRec, transformNode(body))().attachTag(tag)

      def transformModConsBranch(node: Node)(implicit call: ModConsCallInfo): Node = 
        def makeCall =
          val field = assignToIdx((call.letCtorNode.cls.id, call.letCtorNode.fieldName))
          
          // let composed = comp(ctx, Ctx(retVal, ptr, field)) in
          // f(composed, *args)
          LetExpr(
            Name("ctx2"),
            Expr.CtorApp(CTX_CLASS_REF, List(Expr.Ref(call.retName), Expr.Ref(call.letCtorNode.ctorValName), asLit(field))),
            LetCall(
              List(Name("composed")),
              DefnRef(Left(cmpDefn)),
              List("ctx", "ctx2").map(n => Expr.Ref(Name(n))),
              false,
              LetCall(
                List(Name("res")), 
                modConsRefs(call.defn.id),
                Expr.Ref(Name("composed")) :: call.letCallNode.args,
                false,
                Result(
                  List(Expr.Ref(Name("res")))
                ).attachTag(tag)
              )().attachTag(tag)
            )().attachTag(tag)
          ).attachTag(tag)

        node match
          case Result(res) if node.tag.inner == call.retNode.tag.inner =>
            makeCall
          case Jump(defn, args) if node.tag.inner == call.retNode.tag.inner =>
            makeCall
          case LetExpr(name, expr, body) => 
            if node.tag.inner == call.letCtorNode.node.tag.inner then
              // rewrite the ctor, but set the field containing the call as to 0
              val idx = call.letCtorNode.idx
              val argsList = call.letCtorNode.ctor.args.updated(idx, asLit(0))
              LetExpr(name, Expr.CtorApp(ClassRef(L(call.letCtorNode.cls)), argsList), transformModConsBranch(body)).attachTag(tag)
            else
              LetExpr(name, expr, transformModConsBranch(body)).attachTag(tag)
          case LetCall(names, defn, args, isTailRec, body) =>
            if node.tag.inner == call.letCallNode.tag.inner then
              // discard it
              transformModConsBranch(body)
            else
              LetCall(names, defn, args, isTailRec, transformModConsBranch(body))().attachTag(tag)
          case _ => throw IRError("unreachable case when transforming mod cons call")

      def rewriteDefn(d: Defn): Defn =
        val transformed = transformNode(d.body)
        val id = fnUid.make
        Defn(id, d.name + "_modcons$" + id, Name("ctx") :: d.params, d.resultNum, transformed, d.isTailRec)
      
      // returns (new defn, mod cons defn)
      // where new defn has the same signature and ids as the original, but immediately calls the mod cons defn
      // and mod cons defn is the rewritten definition
      def replaceDefn(d: Defn): (Defn, Defn) =
        val modConsDefn = rewriteDefn(d)
        val modConsCall = 
          LetExpr(
            Name("idCtx"),
            Expr.CtorApp(ID_CTX_CLASS_REF, Nil),
              LetCall(
              List(Name("res")), 
              DefnRef(Left(modConsDefn)),
              Expr.Ref(Name("idCtx")) :: d.params.map(Expr.Ref(_)),
              false,
              Result(List(Expr.Ref(Name("res")))).attachTag(tag)
            )().attachTag(tag)
          ).attachTag(tag)
        val newDefn = Defn(d.id, d.name, d.params, d.resultNum, modConsCall, false)
        (newDefn, modConsDefn)

      val jpsTransformed = component.joinPoints.map(d => d.id -> rewriteDefn(d)).toMap
      val defnsTransformed = component.nodes.map(d => d.id -> replaceDefn(d)).toMap

      // update defn refs
      for (id, ref) <- jpRefs do
        ref.defn = Left(jpsTransformed(id))
      
      for (id, ref) <- modConsRefs do
        ref.defn = Left(defnsTransformed(id)._2) // set it to the mod cons defn, not the one with the original signature

      val jps = jpsTransformed.values.toSet
      val modConsDefs = defnsTransformed.values.map((a, b) => b).toSet 
      val normalDefs = defnsTransformed.values.map((a, b) => a).toSet + appDefn + cmpDefn

      // the edges are not used later, but still, rewrite them for correctness
      val newEdges = component.edges.map { c =>
        val src = c.getSrc
        val defn = c.getDefn
        TailCallInfo(defnsTransformed(src.id)._2, defnsTransformed(defn.id)._2) 
      }

      (ScComponent(modConsDefs, newEdges, jps), normalDefs)

  // Given a strongly connected component `defns` of mutually
  // tail recursive functions, returns a set containing the optimized function and the
  // original functions pointing to an optimized function.
  // Explicitly returns the merged function in case tailrec needs to be checked.
  private def optimizeTailRec(component: ScComponent, classes: Set[ClassInfo]): (Set[Defn], Defn) = 
    // To build the case block, we need to compare integers and check if the result is "True"
    val trueClass = classes.find(c => c.name == "True").get
    val falseClass = classes.find(c => c.name == "False").get
    // undefined for dummy values
    val dummyVal = Expr.Literal(UnitLit(true))
    
    // join points need to be rewritten. For now, just combine them into the rest of the function. They will be inlined anyways
    val defns = component.nodes ++ component.joinPoints
    val defnsNoJp = component.nodes
    val edges = component.edges

    // dummy case, should not happen
    if (defns.size == 0)
      throw IRError("strongly connected component was empty")

    // for single tail recursive functions, just move the body into a join point
    if (defns.size <= 1)
      val defn = defns.head
      
      // if the function does not even tail call itself, just return
      if filterOptCalls(edges).size == 0 then
        return (defns, defns.head)
      
      val jpName = defn.name + "_jp"
      val jpDefnRef = DefnRef(Right(jpName))
      
      def transformNode(node: Node): Node = node match
        case Result(res) => node.attachTag(tag)
        case Jump(defn, args) => node.attachTag(tag)
        case Case(scrut, cases, default) => Case(scrut, cases.map((cls, body) => (cls, transformNode(body))), default.map(transformNode)).attachTag(tag)
        case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body)).attachTag(tag)
        case LetMethodCall(names, cls, method, args, body) => LetMethodCall(names, cls, method, args, transformNode(body)).attachTag(tag)
        case LetCall(names, defn_, args, isTailRec, body) =>
          if isTailCall(node) && defn_.expectDefn.id == defn.id then
            Jump(jpDefnRef, args).attachTag(tag)
          else
            LetCall(names, defn_, args, isTailRec, transformNode(body))().attachTag(tag)
      
      val jpDef = Defn(fnUid.make, jpName, defn.params, defn.resultNum, transformNode(defn.body), false)
      
      val rets = (0 until defn.resultNum).map(n => Name("r" + n.toString)).toList
      val callJpNode = LetCall(
        rets, 
        DefnRef(Left(jpDef)),
        defn.params.map(Expr.Ref(_)),
        false,
        Result(rets.map(Expr.Ref(_))).attachTag(tag),
      )().attachTag(tag)
      
      val newDefn = Defn(fnUid.make, defn.name, defn.params, defn.resultNum, callJpNode, true)
      (Set(newDefn, jpDef), newDefn)

    else
      // Note that we do not use the actual edges in ScCompoennt here.
      // We assume the only things we can optimize are tail calls, which
      // are cheap to identify, and nothing else.

      // concretely order the functions as soon as possible, since the order of the functions matter
      val defnsList = defns.toList

      // assume all defns have the same number of results
      // in fact, they should theoretically have the same return type if the program type checked
      val resultNum = defnsList.head.resultNum

      val trName = Name("tailrecBranch$");

      // To be used to replace variable names inside a definition to avoid variable name clashes
      val nameMaps: Map[Int, Map[Name, Name]] = defnsList.map(defn => defn.id -> defn.params.map(n => n -> Name(defn.name + "_" + n.str)).toMap).toMap

      val stackFrameIdxes = defnsList.foldLeft(1 :: Nil)((ls, defn) => defn.params.size + ls.head :: ls).drop(1).reverse

      val defnInfoMap: Map[Int, DefnInfo] = (defnsList zip stackFrameIdxes)
        .foldLeft(Map.empty)((map, item) => map + (item._1.id -> DefnInfo(item._1, item._2)))

      val stackFrame = trName :: defnsList.flatMap(d => d.params.map(n => nameMaps(d.id)(n))) // take union of stack frames

      val newId = fnUid.make
      val newName = defns.foldLeft("")(_ + "_" + _.name) + "_opt$" + newId
      val jpId = fnUid.make
      val jpName = defns.foldLeft("")(_ + "_" + _.name) + "_opt_jp$" + jpId

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
        case Result(_) => node.attachTag(tag)
        case Case(scrut, cases, default) => Case(scrut, cases.map(n => (n._1, transformNode(n._2))), default.map(transformNode)).attachTag(tag)
        case LetExpr(name, expr, body) => LetExpr(name, expr, transformNode(body)).attachTag(tag)
        case LetMethodCall(names, cls, method, args, body) =>
          LetMethodCall(names, cls, method, args, transformNode(body)).attachTag(tag)
        case LetCall(names, defn, args, isTailRec, body) =>
          if isTailCall(node) && defnInfoMap.contains(defn.expectDefn.id) then
            Jump(jpDefnRef, transformStackFrame(args, defnInfoMap(defn.expectDefn.id))).attachTag(tag)
          else LetCall(names, defn, args, isTailRec, transformNode(body))().attachTag(tag)

      // Tail calls to another function in the component will be replaced with a call
      // to the merged function
      // i.e. for mutually tailrec functions f(a, b) and g(c, d),
      // f's body will be replaced with a call f_g(a, b, *, *), where * is a dummy value
      def transformDefn(defn: Defn): Defn =
        val info = defnInfoMap(defn.id)

        val start =
          stackFrame.take(info.stackFrameIdx).drop(1).map { _ => dummyVal } // we drop tailrecBranch and replace it with the defn id
        val end = stackFrame.drop(info.stackFrameIdx + defn.params.size).map { _ => dummyVal }
        val args = asLit(info.defn.id) :: start ::: defn.params.map(Expr.Ref(_)) ::: end

        // We use a let call instead of a jump to avoid newDefn from being turned into a join point,
        // which would cause it to be inlined and result in code duplication.
        val names = (0 until resultNum).map(i => Name("r" + i.toString())).toList
        val namesExpr = names.map(Expr.Ref(_))
        val res = Result(namesExpr).attachTag(tag)
        val call = LetCall(names, newDefnRef, args, false, res)().attachTag(tag)
        Defn(defn.id, defn.name, defn.params, defn.resultNum, call, false)

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

      val jpDefn = Defn(jpId, jpName, stackFrame, resultNum, newNode, false)

      val jmp = Jump(jpDefnRef, stackFrame.map(Expr.Ref(_))).attachTag(tag)
      val newDefn = Defn(newId, newName, stackFrame, resultNum, jmp, defnsNoJp.find { _.isTailRec }.isDefined )

      jpDefnRef.defn = Left(jpDefn)
      newDefnRef.defn = Left(newDefn)

      (defnsNoJp.map { d => transformDefn(d) } + newDefn + jpDefn, newDefn)
  
  private def partition(defns: Set[Defn]): List[ScComponent] = 
    val nodeMap: Map[Int, DefnNode] = defns.foldLeft(Map.empty)((m, d) => m + (d.id -> DefnNode(d)))
    partitionNodes(nodeMap).map(_.removeMetadata)

  private def optimizeParition(component: ScComponent, classes: Set[ClassInfo]): Set[Defn] =
    val trFn = component.nodes.find { _.isTailRec }.headOption
    val normalCall = filterNormalCalls(component.edges).headOption
    
    (trFn, normalCall) match
      case (Some(fn), Some(call)) => 
        raise(ErrorReport(
          List(
            msg"function `${fn.name}` is not tail-recursive, but is marked as @tailrec" -> fn.loc,
            msg"it could self-recurse through this call, which may not be a tail-call" -> call.loc
          ), 
          true, Diagnostic.Compilation)
        )
      case _ =>

    val (modConsComp, other) = optimizeModCons(component, classes)
    val (trOpt, mergedDefn) = optimizeTailRec(modConsComp, classes)
    other ++ trOpt

  def apply(p: Program) = run(p)

  def run_debug(p: Program): (Program, List[Set[String]]) = 
    val partitions = partition(p.defs)

    val newDefs = partitions.flatMap { optimizeParition(_, p.classes) }.toSet
    val newClasses = p.classes + ID_CTX_CLASS + CTX_CLASS

    // update the definition refs
    newDefs.foreach { defn => resolveRef(defn.body, newDefs, newClasses, true) }
    resolveRef(p.main, newDefs, newClasses, true)

    (Program(newClasses, newDefs, p.main), partitions.map(t => t.nodes.map(f => f.name)))

  def run(p: Program): Program = run_debug(p)._1