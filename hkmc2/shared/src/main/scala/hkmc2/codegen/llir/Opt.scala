package hkmc2
package codegen
package llir

import mlscript.utils.*
import mlscript.utils.shorthands.*
import hkmc2.utils.*
import hkmc2.document.*
import hkmc2.Message.MessageContext

import hkmc2.syntax.Tree
import hkmc2.semantics.*
import hkmc2.codegen.llir.{ Program => LlirProgram, Node, Func }
import hkmc2.codegen.Program
import hkmc2.codegen.cpp.Expr.StrLit

import language.implicitConversions
import annotation.tailrec
import collection.immutable._
import collection.mutable.{HashMap => MutHMap, HashSet => MutHSet, LinkedHashMap => MutLMap, LinkedHashSet => MutLSet}
import scala.collection.mutable.ListBuffer

final case class OptErr(message: String) extends Exception(message)

private def oErrStop(msg: Message)(using Raise) =
  raise(ErrorReport(msg -> N :: Nil,
    source = Diagnostic.Source.Compilation))
  throw OptErr("stopped")

def notBuiltinLetCall(node: Node.LetCall) =
  node.func.nme != "<builtin>"

def notBuiltin(sym: Local) =
  sym.nme != "<builtin>"

def notCallable(sym: Local) =
  sym.nme != "Callable"

def showSym(sym: Local) = s"${sym.nme}$$${sym.uid.toString()}"

final class LlirOpt(using Elaborator.State, Raise)(tl: TraceLogger, freshInt: FreshInt, flags: Set[Str]):
  import tl.{log, trace}

  object DestructUtils:
    @tailrec
    def getFirstDestructed(node: Node): Opt[Local] = node match
      case Node.Result(res) => N
      case Node.Jump(func, args) => N
      case Node.Case(Expr.Ref(scrut), cases, default) => S(scrut)
      case Node.Case(_, _, _) => N
      case Node.Panic(msg) => N
      case Node.LetExpr(name, expr, body) => getFirstDestructed(body)
      case Node.LetMethodCall(names, cls, method, args, body) => N
      case Node.LetCall(names, func, args, body) => N
    
    def isDestructed(node: Node) = getFirstDestructed(node).isDefined

  def newFunSym(name: Str) = BlockMemberSymbol(name, Nil)
  def newTemp = TempSymbol(N, "x")
  val placeHolderSym = TempSymbol(N, "<placeholder>")

  class RenameUtil():
    val map: MutHMap[Local, Local] = MutHMap.empty
    def subst(sym: Local): Local = map.getOrElseUpdate(sym, newTemp)
    def subst(sym: IterableOnce[Local]): Iterator[Local] = sym.iterator.map(subst)
    def substT(sym: TrivialExpr): TrivialExpr = sym.foldRef(x => Expr.Ref(subst(x)))
    def substT(sym: IterableOnce[TrivialExpr]): Iterator[TrivialExpr] = sym.iterator.map(substT)

  class SubstUtil[K, +V](val map: Map[K, V]):
    def subst(k: K) = map.getOrElse(k, oErrStop(s"Key $k not found"))
    def subst(k: IterableOnce[K]): Iterator[V] = k.iterator.map(subst)

  class MapUtil(val map: Map[Local, Local]):
    def subst(k: Local) = map.getOrElse(k, k)
    def subst(k: IterableOnce[Local]): Iterator[Local] = k.iterator.map(subst)
    def substT(sym: TrivialExpr): TrivialExpr = sym.foldRef(x => Expr.Ref(subst(x)))
    def substT(sym: IterableOnce[TrivialExpr]): Iterator[TrivialExpr] = sym.iterator.map(substT)

  case class RefEqNode(node: Node):
    override def equals(that: Any) = 
      that match
      case RefEqNode(thatNode) =>
        node is thatNode
      case _ => false
    override def hashCode = node.hashCode
  type Loc = RefEqNode
  given Conversion[Node, Loc] = RefEqNode(_)

  enum IInfo:
    case Ctor(c: Local)
    case Mixed(i: Set[I])
    case Tuple(n: Int)

  enum EInfo:
    case Pass
    case Des
    case IndDes
    case Sel(cls: Local, fld: Str)

  case class E(loc: Loc, info: EInfo)
  case class I(loc: Loc, info: IInfo)

  implicit object EOrdering extends Ordering[E]:
    override def compare(a: E, b: E) = a.info.toString.compare(b.info.toString)
  implicit object IOrdering extends Ordering[I]:
    override def compare(a: I, b: I) = a.info.toString.compare(b.info.toString)

  object ProgInfo:
    def fromProgram(prog: LlirProgram) =
      ProgInfo(
        activeParams = MutHMap.from(prog.defs.iterator.map(f => f.name -> f.params.map(_ => SortedSet.empty[E]))),
        activeResults = MutHMap.from(prog.defs.iterator.map(f => f.name -> List.fill(f.resultNum)(N))),
        func = MutHMap.from(prog.defs.map(f => f.name -> f)),
        classes = MutHMap.from(prog.classes.map(c => c.name -> c)),
        entry = prog.entry
      )
  
  case class ProgInfo(
    activeParams: MutHMap[Local, Ls[SortedSet[E]]],
    activeResults: MutHMap[Local, Ls[Opt[I]]],
    func: MutHMap[Local, Func],
    classes: MutHMap[Local, ClassInfo],
    entry: Local,
  ):
    def toProgram =
      LlirProgram(classes.values.toSet, func.values.toSet, entry = entry)

    def getActiveParams(func: Local) =
      activeParams.getOrElse(func, oErrStop(s"Function $func with empty activeParams"))

    def getActiveResults(func: Local) =
      activeResults.getOrElse(func, oErrStop(s"Function $func with empty activeResults"))
    
    def getFunc(sym: Local): Func =
      func.getOrElse(sym, oErrStop(s"Function $sym not found"))
    
    def getClass(sym: Local): ClassInfo =
      classes.getOrElse(sym, oErrStop(s"Class $sym not found"))

    def setActiveParams(func: Local, aps: Ls[SortedSet[E]]) = 
      activeParams.update(func, aps)

    def setActiveResults(func: Local, ars: Ls[Opt[I]]) =
      activeResults.update(func, ars)

  private object EliminationAnalysis:
    case class Env(
      val def_count: MutHMap[Local, Int] = MutHMap.empty,
      val elims: MutHMap[Local, MutHSet[E]] = MutHMap.empty,
      val defn: Local,
      val visited: MutHSet[Local] = MutHSet.empty,
    )
  
  private class EliminationAnalysis(info: ProgInfo):
    import EliminationAnalysis.Env
    def addE(sym: Local, e: E)(using env: Env) =
      env.elims.getOrElseUpdate(sym, MutHSet.empty) += e

    def addBackwardE(sym: Local, e: E, newLoc: Loc)(using env: Env) =
      import EInfo.*
      val e2 = e match
        case E(_, Des) | E(_, IndDes) => Some(E(newLoc, IndDes))
        case E(_, Pass) => Some(E(newLoc, Pass))
        case _ => None
      for e2 <- e2 do env.elims.getOrElseUpdate(sym, MutHSet.empty).add(e2)

    def addDef(sym: Local)(using env: Env) =
      env.def_count.update(sym, env.def_count.getOrElse(sym, 0) + 1)

    def fTExprWithLoc(x: TrivialExpr, loc: Loc)(using env: Env): Unit =
      x.iterRef(addE(_, E(loc, EInfo.Pass)))

    def fExprWithLoc(x: Expr, loc: Loc)(using env: Env): Unit = x match
      case Expr.Ref(name) => addE(name, E(loc, EInfo.Pass))
      case Expr.Literal(lit) =>
      case Expr.CtorApp(name, args) => args.foreach(fTExprWithLoc(_, loc))
      case Expr.Select(name, cls, field) => addE(name, E(loc, EInfo.Sel(cls, field)))
      case Expr.BasicOp(name, args) => args.foreach(fTExprWithLoc(_, loc))
      case Expr.AssignField(assignee, _, _, value) => TODO("fExprWithLoc: AssignField")

    def fNode(node: Node)(using env: Env): Unit = 
      def fDef(func: Local, args: Ls[TrivialExpr], funcDefn: Func)(using env: Env) =
        val aps = info.getActiveParams(func)
        args.iterator.zip(aps).foreach:
          case (Expr.Ref(x), ys) => ys.foreach(y => addBackwardE(x, y, node))
          case _ =>
        if !env.visited.contains(func) && notBuiltin(func) then
          env.visited.add(func)
          val funcDefn = info.getFunc(func)
          funcDefn.params.foreach(addDef)
          val newEnv = env.copy(defn = func)
          fNode(funcDefn.body)(using newEnv)
      node match
      case Node.Result(res) => res.foreach(fTExprWithLoc(_, node))
      case Node.Jump(func, args) =>
        args.foreach(fTExprWithLoc(_, node))
        if notBuiltin(func) then
          fDef(func, args, info.getFunc(func))
      case Node.Case(Expr.Ref(scrutinee), cases, default) =>
        addE(scrutinee, E(node, EInfo.Pass))
        addE(scrutinee, E(node, EInfo.Des))
        cases.foreach { case (cls, body) => fNode(body) }
        default.foreach(fNode)
      case Node.Case(_, cases, default) => 
        cases.foreach { case (cls, body) => fNode(body) }
        default.foreach(fNode)
      case Node.Panic(msg) =>
      case Node.LetExpr(name, expr, body) =>
        fExprWithLoc(expr, node)
        addDef(name)
        fNode(body)
      case Node.LetMethodCall(names, cls, method, args, body) =>
        // TODO: LetMethodCall
        fNode(body)
      case Node.LetCall(names, func, args, body) =>
        names.foreach(addDef)
        args.foreach(fTExprWithLoc(_, node))
        if notBuiltin(func) then
          fDef(func, args, info.getFunc(func))
        fNode(body)
      
    def run() =
      var changed = true
      var env = Env(defn = placeHolderSym)
      while changed do
        changed = false
        env = Env(defn = placeHolderSym)
        info.func.values.foreach: func =>
          val old = info.getActiveParams(func.name)
          func.params.foreach(addDef(_)(using env))
          fNode(func.body)(using env)
          val nu = func.params.iterator.map(p => env.elims.getOrElse(p, MutHSet.empty).toSortedSet).toList
          changed |= old != nu
          info.setActiveParams(func.name, nu)
      env

  private object IntroductionAnalysis:
    case class Env(
      intros: MutHMap[Local, I] = MutHMap.empty,
      default_intro: Ls[Opt[I]], // the intro of panic
    )
  
  private class IntroductionAnalysis(info: ProgInfo):
    import IntroductionAnalysis.Env
    def mergeIntros(xs: Ls[Ls[Opt[I]]], loc: Loc): Ls[Opt[I]] =
      trace[Ls[Opt[I]]](s"mergeIntros: $xs"):
        val xst = xs.transpose
        xst.map: ys =>
          val z = ys.flatMap:
            case N => Set.empty[I]
            case S(I(loc, IInfo.Mixed(i))) => i
            case S(i) => Set(i)
          .toSet
          if z.nonEmpty then S(I(loc, IInfo.Mixed(z))) else N

    def addI(sym: Local, i: I)(using env: Env) =
      trace[Unit](s"addI: ${sym.nme}$$${sym.uid.toString()} -> $i"):
        if env.intros.contains(sym) then
          oErrStop(s"Multiple introductions of ${sym.nme}$$${sym.uid.toString()}")
        env.intros.update(sym, i)
    
    
    def addITExpr(te: TrivialExpr, i: I)(using env: Env) = te match
      case Expr.Ref(x) => addI(x, i)
      case _ => ()

    // given the arguments of a function call, we find their intro-info and propagate them to the function's parameters
    def bindIInfo(args: Ls[TrivialExpr], params: Ls[Symbol])(using env: Env) =
      args.iterator.zip(params).foreach:
        case (Expr.Ref(x), p) if env.intros.contains(x) => env.intros.addOne(p -> env.intros(x))
        case _ => ()
    
    def fTExprWithLoc(x: TrivialExpr, loc: Loc)(using env: Env): Opt[I] = x match
      case Expr.Ref(name) => env.intros.get(name)
      case _ => N

    def fExprWithLoc(e: Expr, loc: Loc)(using env: Env): Opt[I] = e match
      case Expr.Ref(sym) => env.intros.get(sym)
      case Expr.CtorApp(cls, args) => S(I(loc, IInfo.Ctor(cls)))
      case _ => N

    def fNode(node: Node)(using env: Env): Ls[Opt[I]] = 
      trace[Ls[Opt[I]]](s"fNode: $node"):
        node match
        case Node.Result(res) => res.map(f => fTExprWithLoc(f, node))
        case Node.Jump(func, args) => 
          info.getActiveResults(func).map:
            case N => N
            case S(I(loc, i)) => S(I(node, i))
        case Node.Case(scrutinee, cases, default) =>
          val casesIntros = cases.map:
            case (Pat.Class(cls), body) =>
              // addITExpr(scrutinee, I(node, IInfo.Ctor(cls)))
              fNode(body)
            case (Pat.Lit(lit), body) => fNode(body)
          default match
            case N => mergeIntros(casesIntros, node)
            case S(x) => mergeIntros(casesIntros :+ fNode(x), node)
        case Node.Panic(msg) => env.default_intro
        case Node.LetExpr(name, expr, body) =>
          for i <- fExprWithLoc(expr, node) do addI(name, i)
          fNode(body)
        case Node.LetMethodCall(names, cls, method, args, body) => fNode(body)
        case Node.LetCall(names, func, args, body) =>
          if notBuiltin(func) then
            val funcDefn = info.getFunc(func)
            val ars = info.getActiveResults(func)
            names.iterator.zip(ars).foreach:
              case (rv, S(I(oldLoc, i))) => addI(rv, I(node, i))
              case _ => ()
          fNode(body)
      
    def run() =
      var changed = true
      var env = Env(default_intro = Nil)
      while changed do
        changed = false
        env = Env(default_intro = Nil)
        info.func.values.foreach: func =>
          val old = info.getActiveResults(func.name)
          val nu = fNode(func.body)(using env.copy(default_intro = List.fill(func.resultNum)(N)))
          assert(old.length == nu.length, s"old: $old, nu: $nu")
          changed |= old != nu
          info.setActiveResults(func.name, nu)
      env

  private class Splitting(info: ProgInfo):
    case class PreFunc(sym: Local, results: Ls[Local], body: PreFuncBody, orig: Func)
    case class PostFunc(sym: Local, params: Ls[Local], body: PostFuncBody, orig: Func)
    case class PreFuncBody(body: Node => Node)
    case class PostFuncBody(body: Node)
  
    case class Env(
      i: IntroductionAnalysis.Env,
      e: EliminationAnalysis.Env,
      possibleSplitting: MutHMap[RefEqNode, (PreFuncBody, PostFuncBody)] = MutHMap.empty,
      workingList: MutLSet[Func] = MutLSet.empty,
    )

    case class SymDDesc(
      knownClass: Local,
      isIndirect: Bool,
      e: E
    )

    case class SDesc(
      argumentsDesc: MutLMap[Local, SymDDesc] = MutLMap.empty,
      firstDestructedSym: Opt[Local] = N,
      mixingProducer: MutLMap[Local, Loc] = MutLMap.empty,
    )

    def symAndIntroOfTExpr(te: TrivialExpr)(using env: Env): Opt[(Local, I)] = te match
      case Expr.Ref(x) => for i <- env.i.intros.get(x) yield (x, i)
      case _ => none
    
    def findProducer(loc: Loc) = loc match
      case RefEqNode(Node.LetCall(_, producer, _, _)) => some(producer)
      case _ => none
    
    // how this function reflects the splitting decision?
    // if argumentsDesc is non-empty, it means the callee is a target of been splitted
    // if mixingProducer is non-empty, it means a call happens before is a mixing producer,
    //   as well as the splitting target
    def checkSTarget(func: Func, args: Ls[TrivialExpr])(using env: Env) =
      val activeParams = info.getActiveParams(func.name)
      val params = func.params
      val argsIntros = args.iterator.map(symAndIntroOfTExpr)
      val firstD = DestructUtils.getFirstDestructed(func.body)
      var argumentsDesc = MutLMap.empty[Local, SymDDesc]
      val mixingProducer = MutLMap.empty[Local, Loc]
      argsIntros.zip(params.iterator.zip(activeParams.iterator)).foreach:
        case ((S((arg, I(loc, IInfo.Ctor(cls))))), (param, elims)) =>
          for e <- elims do e match
            case E(loc, EInfo.Des) => argumentsDesc.update(param, SymDDesc(cls, false, e))
            case E(loc, EInfo.IndDes) => argumentsDesc.update(param, SymDDesc(cls, true, e))
            case _ =>
        case (S((arg, I(loc, IInfo.Mixed(is)))), (p, elims)) =>
          for e <- elims do e match
            case E(_, EInfo.Des | EInfo.IndDes) =>
              // what to do with a mixing producer?
              // it's different with other kinds of splitting
              // 
              // for example, in f0, we have following program:
              //   ... #1
              // let x1 = f1() in
              //   ... #2
              // let x2 = f2(x1) in
              //   ... #3
              // where x1 is `IInfo.Mixed`
              // 
              // what we need to to is splitting f1
              // let ... = f1_pre() in
              // case ... of 
              //   C1(...) => let x1 = f1_post1(...) in
              //              jump f0_post(x1)
              //   C2(...) => let x1' = f1_post2(...) in
              //              jump f0_post(x1')
              // 
              // f0_post will looks like
              //   ... #2
              // let x2 = f2(x1) in
              //   ... #2
              // the problem is how to correctly collect all structures necessary for `f0_post``.
              // as we are traversing over the node chain, we shall accumulate the continuation that with a node hole.
              // 
              // in the example above, when we see f2(x1) and find the producer of x1 should be splitted,
              // we already have the continuation until `... in #1`
              // (we need record the pre-cont before every possible splitting position).
              // though, it's still necessary to obtain `... #2` to `... #3` directly.
              // how to do that? it's just a node following the f1() call, so it's naturally included by the LetCall node
              // it also indicates that yet another kind of context should be carefully maintained.
              // another point is worth noticing that we need to do alpha-renaming after using the pre-cont and post-cont!!!
              val producer = findProducer(loc)
              for p <- producer do 
                mixingProducer.update(p, loc)
            case _ =>
        case _ => ()
      SDesc(argumentsDesc, firstD, mixingProducer)

    def memoCall(callNode: Node.LetCall)(k: Node => Env ?=> Node)(using env: Env): Unit =
      val Node.LetCall(names, func, args, body) = callNode
      env.possibleSplitting.update(RefEqNode(callNode), (PreFuncBody(node => k(node)(using env)), PostFuncBody(body)))

    // there's another strategy to split a callee of functions calls
    // they can be categorized into several kinds:
    // 1. the elimination happens in a nested call
    //    a). the elimination happens in a most-out level, which means it isn't contained by any other case.
    //        so what need to do is simply split the callee into 3 parts, namely pre, call, and post.
    //        this mode is called A mode
    //    b). it's inside a case
    //        it's a little difficult to handle, but if this happens, how about to delegate it to the 3rd case
    //        as we already have a mechanism to handle it.
    // 2. the elimination happens in a nested jump
    //    similar to case 1, but only 2 parts for 2.a, which is called B mode
    // 3. the elimination happens in a case
    //    a). still the case is the outmost one, which is called C mode
    //        in this case, the function is split into 1 + #(case arms) parts
    //    b). it's inside another case
    //        still, split the outmost case first
    // 
    // In any case and sub-case above, it should be guaranteed that the node contains at least one let-call,
    // jump, or case node. Otherwise, the splitting is problematic, which implies a bug in the algorithm.
    
    case class CallShape(
      func: Local,
      returns: Opt[Ls[Local]],
      args: Ls[TrivialExpr],
    )

    case class CaseShape(
      scrutinee: TrivialExpr,
      cases: Ls[(Pat, PostFunc)],
      default: Opt[PostFunc],
    )

    enum SplittingMode:
      case A(pre: PreFunc, post: PostFunc, callS: CallShape)
      case B(pre: PreFunc, callS: CallShape)
      case C(pre: PreFunc, caseS: CaseShape)

    case class ComposeResult(
      k: Node => Node,
      newFunc: Ls[Func],
      invalidFunc: Func
    )

    def renameExpr(expr: Expr)(using s: RenameUtil): Expr = expr match
      case Expr.Ref(sym) => Expr.Ref(s.subst(sym))
      case Expr.Literal(lit) => expr
      case Expr.CtorApp(cls, args) => Expr.CtorApp(cls, s.substT(args).toList)
      case Expr.Select(name, cls, field) => Expr.Select(s.subst(name), cls, field)
      case Expr.BasicOp(name, args) => Expr.BasicOp(name, s.substT(args).toList)
      case Expr.AssignField(assignee, cls, field, value) => Expr.AssignField(s.subst(assignee), cls, field, s.substT(value))
    
    def renameNode(node: Node)(using s: RenameUtil): Node = node match
      case Node.Result(res) => Node.Result(s.substT(res).toList)
      case Node.Jump(func, args) => Node.Jump(func, s.substT(args).toList) 
      case Node.Case(scrutinee, cases, default) =>
        Node.Case(s.substT(scrutinee), cases.map:
          case (pat, body) => pat -> renameNode(body),
          default.map(renameNode(_)))
      case Node.Panic(msg) => Node.Panic(msg)
      case Node.LetExpr(name, expr, body) =>
        val nuName = s.subst(name)
        val nuExpr = renameExpr(expr)
        Node.LetExpr(nuName, nuExpr, renameNode(body))
      case Node.LetMethodCall(names, cls, method, args, body) =>
        val nuNames = names.map(s.subst)
        Node.LetMethodCall(nuNames, cls, method, s.substT(args).toList, renameNode(body))
      case Node.LetCall(names, func, args, body) =>
        val nuNames = names.map(s.subst)
        Node.LetCall(nuNames, func, s.substT(args).toList, renameNode(body))    

    def reComposePreFunc(subst: RenameUtil, preBody: Node => Node, origParams: Ls[Local], preSym: Local, results: Ls[Local]): Func =
      trace[Func](s"reComposePreFunc begin", f => s"reComposePreFunc end: $f"):
        val preParams = subst.subst(origParams)
        val preNode = renameNode(preBody(Node.Result(results.map(Expr.Ref(_)))))(using subst)
        val preFunc = Func(freshInt.make, preSym, preParams.toList, results.length, preNode)
        preFunc

    def reComposePostFunc(subst: RenameUtil, params: Ls[Local], postBody: Node, postSym: Local, resultNum: Int): Func =
      trace[Func](s"reComposePostFunc begin: $params $postBody", f => s"reComposePostFunc end: $f"):
        val postParams = subst.subst(params)
        val postNode = renameNode(postBody)(using subst)
        val postFunc = Func(freshInt.make, postSym, postParams.toList, resultNum, postNode)
        postFunc

    def reComposeWithArgs(sm: SplittingMode, args: Ls[TrivialExpr], returns: Opt[Ls[Local]], knownClass: Opt[Local]): ComposeResult =
      sm match
        case SplittingMode.A(
          PreFunc(preSym, results, PreFuncBody(preBody), orig),
          PostFunc(postSym, params, PostFuncBody(postBody), _),
          CallShape(func, nestedReturns, nestedArgs)) =>
          val preFunc = reComposePreFunc(RenameUtil(), preBody, orig.params, preSym, results)
          val postFunc = reComposePostFunc(RenameUtil(), params, postBody, postSym, orig.resultNum)
          val k = (node: Node) =>
            // alpha rename the nestedReturns, results, nestedArgs, and params
            // since they may be reused in different contexts
            val subst = RenameUtil()
            val nuNestedReturns = subst.subst(nestedReturns.get)
            val nuResults = subst.subst(results)
            val nuNestedArgs = subst.substT(nestedArgs)
            val nuParams = subst.subst(params)
            val tailJump = returns.isEmpty
            Node.LetCall(nuResults.toList, preSym, args, 
              Node.LetCall(nuNestedReturns.toList, func, nuNestedArgs.toList, 
              if tailJump then 
                Node.Jump(postSym, nuParams.map(Expr.Ref(_)).toList)
              else
                val nuReturns = subst.subst(returns.get)
                Node.LetCall(nuReturns.toList, postSym, nuParams.map(Expr.Ref(_)).toList, renameNode(node)(using subst))))
          ComposeResult(k, List(preFunc, postFunc), orig)
        case SplittingMode.B(
          PreFunc(preSym, results, PreFuncBody(preBody), orig),
          CallShape(func, nestedReturns, nestedArgs)) =>
          val preFunc = reComposePreFunc(RenameUtil(), preBody, orig.params, preSym, results)
          val k = (node: Node) =>
            val subst = RenameUtil()
            // there are no nested returns since in original function it's a jump
            val nuResults = subst.subst(results)
            val nuNestedArgs = subst.substT(nestedArgs)
            val tailJump = returns.isEmpty
            Node.LetCall(nuResults.toList, preSym, args, 
              if tailJump then 
                Node.Jump(func, nuNestedArgs.toList)
              else
                val nuReturns = subst.subst(returns.get)
                Node.LetCall(nuReturns.toList, func, nuNestedArgs.toList, renameNode(node)(using subst)))
          ComposeResult(k, List(preFunc), orig)
        case SplittingMode.C(
          PreFunc(preSym, results, PreFuncBody(preBody), orig),
          CaseShape(scrutinee, cases, default)) =>
          val preFunc = reComposePreFunc(RenameUtil(), preBody, orig.params, preSym, results)
          var matchedPat = none[Pat]
    
          val allPostFunc = cases.map:
            case (pat, PostFunc(postSym, params, PostFuncBody(postBody), _)) =>
              val postFunc = reComposePostFunc(RenameUtil(), params, postBody, postSym, orig.resultNum)
              (pat, knownClass) match
                case (Pat.Class(cls), S(cls2)) if cls == cls2 => matchedPat = some(pat)
                case _ =>
              (params, pat, postFunc)
          val defaultPostFunc = default.map:
            case PostFunc(postSym, params, PostFuncBody(postBody), _) =>
              (params, reComposePostFunc(RenameUtil(), params, postBody, postSym, orig.resultNum))

          def tailNodeLetCall(postFunc: Func, postFvs: Ls[Local], node: Node)(using subst: RenameUtil) = 
            // the reason for postFvs instead of postFunc.params is that the later has been renamed
            // so they cannot be correctly renamed with another RenameUtil
            val postArgs = subst.subst(postFvs).map(Expr.Ref(_)).toList
            val subst2 = RenameUtil()
            val nuReturns = subst2.subst(returns.get)
            Node.LetCall(nuReturns.toList, postFunc.name, postArgs, renameNode(node)(using subst2))
          def tailNodeJump(postFunc: Func, postFvs: Ls[Local])(using subst: RenameUtil) = 
            val postArgs = subst.subst(postFvs).map(Expr.Ref(_)).toList
            Node.Jump(postFunc.name, postArgs)
          def tailNodeChoose(postFvs: Ls[Local], postFunc: Func, node: Node)(using subst: RenameUtil) = 
            if returns.isEmpty then tailNodeJump(postFunc, postFvs) else tailNodeLetCall(postFunc, postFvs, node)
          // the supplied node should be trivial, otherwise we actually duplicate stuff here
          val k = (node: Node) =>
            given subst: RenameUtil = RenameUtil()
            val nuResults = subst.subst(results)
            val nuScrutinee = subst.substT(scrutinee)
            val tailJump = returns.isEmpty
            (knownClass, matchedPat) match
            case (None, _) => 
              Node.LetCall(nuResults.toList, preSym, args,
                Node.Case(nuScrutinee, allPostFunc.map:
                  case (args, pat, postFunc) =>
                    pat -> tailNodeChoose(args, postFunc, node),
                  defaultPostFunc.map((args, postFunc) =>
                    tailNodeChoose(args, postFunc, node))))
            case (Some(_), None) =>
              // only keep the default case if there's one
              defaultPostFunc match
                case None => 
                  Node.LetCall(nuResults.toList, preSym, args,
                    Node.Case(nuScrutinee, allPostFunc.map:
                      case (args, pat, postFunc) =>
                        pat -> tailNodeChoose(args, postFunc, node),
                      defaultPostFunc.map((args, postFunc) =>
                        tailNodeChoose(args, postFunc, node))))
                case Some((args2, postFunc)) =>
                  Node.LetCall(nuResults.toList, preSym, args,
                    tailNodeChoose(args2, postFunc, node))
            case (Some(_), Some(matched)) =>
              Node.LetCall(nuResults.toList, preSym, args,
                allPostFunc.flatMap:
                  case (args, pat, postFunc) => if pat == matched then
                    S(tailNodeChoose(args, postFunc, node)) else N
                .head)
          ComposeResult(k, preFunc :: allPostFunc.map(_._3) ++ defaultPostFunc.map(_._2).toList, orig)

    
    def sFunc(func: Func, splitPos: Loc): SplittingMode =
      trace[SplittingMode](s"sFunc: ${func.name |> showSym}, $splitPos"):
        sNode(func.body, splitPos, func)(identity)

    def sNode(node: Node, splitPos: Loc, thisFunc: Func)(acc: Node => Node): SplittingMode = 
      trace[SplittingMode](s"sNode: $node"): 
        node match
        case Node.Result(res) => oErrStop(s"sNode: unexpected Result $res")
        case Node.Jump(func, args) =>
          // B mode
          val sym = newFunSym(s"${thisFunc.name.nme}_pre")
          val pfBody = PreFuncBody(acc)
          val fvs = FreeVarAnalysis(info.func).run(node)
          val results = fvs.toList
          val pf = PreFunc(sym, results, pfBody, thisFunc)
          val cs = CallShape(func, none, args)
          SplittingMode.B(pf, cs)
        case Node.Case(scrutinee, cases, default) =>
          // C mode
          val sym = newFunSym(s"${thisFunc.name.nme}_pre")
          val pfBody = PreFuncBody(acc)
          val fvs = FreeVarAnalysis(info.func).run(node)
          val results = fvs.toList
          val pf = PreFunc(sym, results, pfBody, thisFunc)
          val cases2 = cases.zipWithIndex.map:
            case ((pat, body), i) =>
              val sym = newFunSym(s"${thisFunc.name.nme}_case$i")
              val fvs = FreeVarAnalysis(info.func).run(node)
              val pfBody = PostFuncBody(body)
              val pf = PostFunc(sym, fvs.toList, pfBody, thisFunc)
              (pat, pf)
          val default2 = default.map: node =>
              val sym = newFunSym(s"${thisFunc.name.nme}_default")
              val fvs = FreeVarAnalysis(info.func).run(node)
              val pfBody = PostFuncBody(node)
              val pf = PostFunc(sym, fvs.toList, pfBody, thisFunc)
              pf
          val caseS = CaseShape(scrutinee, cases2, default2)
          SplittingMode.C(pf, caseS)
        case Node.Panic(msg) => oErrStop("sNode: unexpected Panic")
        case Node.LetExpr(name, expr, body) =>
          sNode(body, splitPos, thisFunc)(x => Node.LetExpr(name, expr, x))
        case Node.LetMethodCall(names, cls, method, args, body) =>
          sNode(body, splitPos, thisFunc)(x => Node.LetMethodCall(names, cls, method, args, x))
        case Node.LetCall(names, func, args, body) =>
          if splitPos == RefEqNode(node) then
            // A mode
            val sym = newFunSym(s"${thisFunc.name.nme}_pre")
            val pfBody = PreFuncBody(acc)
            val fvs = FreeVarAnalysis(info.func).run(node)
            val results = fvs.toList
            val pf = PreFunc(sym, results, pfBody, thisFunc)
            val cs = CallShape(func, some(names), args)
            SplittingMode.A(pf, PostFunc(func, names, PostFuncBody(body), thisFunc), cs)
          else
            sNode(body, splitPos, thisFunc)(x => Node.LetCall(names, func, args, x))
    
    // yet another thing is to avoid duplication. once we split a function
    // the sub-components of the function will be wrapped into a new function
    // so the original function should be correspondingly updated.
    def rFunc(orig: Func, sm: SplittingMode)(using env: Env): Unit =
      val s = RenameUtil()
      val nuParams = s.subst(orig.params).toList
      val nuArgs = nuParams.map(Expr.Ref(_)).toList
      val ComposeResult(k, newFuncs, invalidFunc) = reComposeWithArgs(sm, nuArgs, N, N)
      assert(orig.name == invalidFunc.name, s"rFunc: invalidFunc: $invalidFunc, orig: $orig")
      env.workingList.remove(invalidFunc)
      val nuFunc = Func(
        orig.id,
        orig.name,
        nuParams,
        orig.resultNum,
        k(Node.Panic("placeholder here"))
      )
      newFuncs.foreach(f => info.func.update(f.name, f))
      info.func.update(invalidFunc.name, nuFunc)

    def wrapPost(node: Node)(using env: Env, thisFunc: Func): Node =
      val fvs = FreeVarAnalysis(info.func).run(node).toList
      val sym = newFunSym(s"${thisFunc.name.nme}_post")
      val s = RenameUtil()
      val nuBody = renameNode(node)(using s)
      val nuParams = s.subst(fvs).toList
      val nuFunc = Func(freshInt.make, sym, nuParams, thisFunc.resultNum, nuBody)
      info.func.update(sym, nuFunc)
      Node.Jump(sym, fvs.map(Expr.Ref(_)))

    def fNode(node: Node)(k: Node => Env ?=> Node)(using env: Env, thisFunc: Func): Node =
      trace[Node](s"split fNode: $node"):
        node match
        case Node.Result(res) => k(node)
        case Node.Jump(func, args) =>
          val sDesc = checkSTarget(info.getFunc(func), args)
          (sDesc.argumentsDesc.isEmpty, sDesc.mixingProducer.isEmpty) match
            case (true, _) => k(node)
            case (false, _) =>
              val desc = sDesc.argumentsDesc.head
              val (sym, SymDDesc(knownC, isInd, e)) = desc
              val old = info.getFunc(func)
              log(s"splitting: ${old.name |> showSym}")
              val sm = sFunc(info.getFunc(func), e.loc)
              rFunc(old, sm)
              val cr = reComposeWithArgs(sm, args, N, N)
              val nuBody = cr.k(Node.Panic("placeholder here"))
              k(nuBody)
        case Node.Case(scrutinee, cases, default) =>
          symAndIntroOfTExpr(scrutinee) match
            // case Some((scrutinee, I(loc, IInfo.Mixed(i)))) =>
            //   ???
            case _ =>
              val nuCases = cases.map:
                case (p @ Pat.Class(cls), body) =>
                  val old = env.i.intros.put(cls, I(node, IInfo.Ctor(cls)))
                  val nuBody = fNode(body)(identity)
                  for i <- old do env.i.intros.update(cls, i)
                  (p, nuBody)
                case (p @ Pat.Lit(lit), body) => 
                  (p, fNode(body)(identity))
              val dfltCase = default.map(fNode(_)(identity))
              k(Node.Case(scrutinee, nuCases, dfltCase))
        case Node.Panic(msg) => node
        case Node.LetExpr(name, expr, body) =>
          fNode(body): inner =>
            k(Node.LetExpr(name, expr, inner))
        case Node.LetMethodCall(names, cls, method, args, body) =>
          fNode(body): inner =>
            k(Node.LetMethodCall(names, cls, method, args, inner))
        case node @ Node.LetCall(names, func, args, body) =>
          if notBuiltin(func) then
            val sDesc = checkSTarget(info.getFunc(func), args)
            (sDesc.argumentsDesc.isEmpty, sDesc.mixingProducer.isEmpty) match
              case (true, _) =>
                memoCall(node)(k)
                fNode(body): inner =>
                  k(Node.LetCall(names, func, args, inner))
              case (false, _) =>
                val desc = sDesc.argumentsDesc.head
                val (sym, SymDDesc(knownC, isInd, e)) = desc
                val old = info.getFunc(func)
                log(s"splitting: ${old.name |> showSym}")
                val sm = sFunc(info.getFunc(func), e.loc)
                rFunc(old, sm)
                val cr = reComposeWithArgs(sm, args, S(names), N)
                val tail = wrapPost(body)
                val nuBody = cr.k(tail)
                k(nuBody)
              // case (_, false) => ???
          else
            fNode(body): inner =>
              k(Node.LetCall(names, func, args, inner))

    def fFunc(func: Func)(using env: Env): Unit =
      trace[Unit](s"split fFunc: ${func.name |> showSym}"):
        val nuFunc = Func(func.id, func.name, func.params, func.resultNum, fNode(func.body)(identity)(using env, func))
        info.func.update(func.name, nuFunc)
            
    def run() =
      val i = IntroductionAnalysis(info)
      val iEnv = i.run()
      val e = EliminationAnalysis(info)
      val eEnv = e.run()
      val env = Env(iEnv, eEnv)
      env.workingList.addAll(info.func.values)
      log(s"workingList: ${env.workingList.iterator.map(_.name).toList}")
      while env.workingList.nonEmpty do
        val func = env.workingList.head
        env.workingList.remove(func)
        fFunc(func)(using env)

  private class Simplify(info: ProgInfo):
    def simplify =
      val newFuncs = info.func.map:
        case (name, func) =>
          val newBody = removeTrivialCallAndJump(func.body)(using MapUtil(Map.empty))
          func.name -> func.copy(body = newBody)
      info.func.clear()
      info.func.addAll(newFuncs)
      val reachable = ProgDfs(info).dfs(true)
      log(s"reachableFuncs: ${reachable.funcs.map(showSym).toList}")
      log(s"unreachableFuncs: ${info.func.keys.filterNot(reachable.funcs.contains(_)).map(showSym).toList}")
      log(s"reachableClasses: ${reachable.classes.map(showSym).toList}")
      log(s"unreachableClasses: ${info.classes.keys.filterNot(reachable.classes.contains(_)).map(showSym).toList}")
      info.func.filterInPlace((k, _) => reachable.funcs.contains(k))
      info.classes.filterInPlace((k, _) => reachable.classes.contains(k))

    private def removeTrivialCallAndJump(expr: Expr)(using m: MapUtil): Expr = expr match
      case Expr.Ref(name) => Expr.Ref(m.subst(name))
      case Expr.Literal(lit) => expr
      case Expr.CtorApp(cls, args) => Expr.CtorApp(cls, m.substT(args).toList)
      case Expr.Select(name, cls, field) => Expr.Select(m.subst(name), cls, field)
      case Expr.BasicOp(name, args) => Expr.BasicOp(name, m.substT(args).toList)
      case Expr.AssignField(assignee, cls, field, value) => 
        Expr.AssignField(m.subst(assignee), cls, field, m.substT(value))

    private def removeTrivialCallAndJump(node: Node)(using MapUtil): Node = node match
      case Node.Result(res) => Node.Result(summon[MapUtil].substT(res).toList)
      case Node.Jump(func, args) =>
        if notBuiltin(func) then
          val funcDefn = info.getFunc(func)
          val nuArgs = summon[MapUtil].substT(args).toList
          val m = SubstUtil(funcDefn.params.zip(nuArgs).toMap)
          funcDefn.body match
            case Node.Result(res) =>
              Node.Result(res.map(_.foldRef(m.subst)))
            case Node.Jump(func, args) =>
              Node.Jump(func, args.map(_.foldRef(m.subst)))
            case _ => node
        else
          node
      case Node.Case(scrutinee, cases, default) =>
        Node.Case(summon[MapUtil].substT(scrutinee), cases.map:
          case (pat, body) => pat -> removeTrivialCallAndJump(body),
          default.map(removeTrivialCallAndJump(_)))
      case Node.Panic(msg) => node
      case Node.LetExpr(name, expr, body) => 
        val nuExpr = removeTrivialCallAndJump(expr)
        Node.LetExpr(name, nuExpr, removeTrivialCallAndJump(body))
      case Node.LetMethodCall(names, cls, method, args, body) => 
        val nuArgs = summon[MapUtil].substT(args).toList
        Node.LetMethodCall(names, cls, method, nuArgs, removeTrivialCallAndJump(body))
      case Node.LetCall(names, func, args, body) =>
        if notBuiltin(func) then
          val funcDefn = info.getFunc(func)
          val nuArgs = summon[MapUtil].substT(args).toList
          val m = SubstUtil(funcDefn.params.zip(nuArgs).toMap)
          funcDefn.body match
            case Node.Jump(func, args) =>
              Node.LetCall(names, func, args.map(_.foldRef(m.subst)), removeTrivialCallAndJump(body))
            case _ => node
        else
          node

  def run(prog: LlirProgram) =
    val info = ProgInfo.fromProgram(prog)
    if flags.contains("simp") then
      val simp = Simplify(info)
      simp.simplify
    if flags.contains("!split") then
      ()
    else
      val splitting = Splitting(info)
      splitting.run()
    if flags.contains("simp2") then
      val simp = Simplify(info)
      simp.simplify
    info.toProgram

    
  class ProgDfs(info: ProgInfo):
    import Node._
    import Expr._
    
    case class FuncAndClass(funcs: Ls[Local] = Nil, classes: Ls[Local] = Nil):
      def addF(func: Local): FuncAndClass = copy(funcs = func :: funcs)
      def addC(cls: Local): FuncAndClass = copy(classes = cls :: classes)

    case class Buf(funcs: ListBuffer[Local] = ListBuffer.empty, classes: ListBuffer[Local] = ListBuffer.empty)

    private object Successors:
      def find(expr: Expr)(using acc: FuncAndClass): FuncAndClass =
        expr match
          case Ref(sym) => acc
          case Literal(lit) => acc
          case CtorApp(cls, args) => acc.addC(cls)
          case Select(name, cls, field) => acc.addC(cls)
          case BasicOp(name, args) => acc
          case AssignField(assignee, cls, field, value) => acc.addC(cls)

      def find(node: Node)(using acc: FuncAndClass): FuncAndClass =
        node match
          case Result(res) => acc
          case Jump(func, args) => if notBuiltin(func) then acc.addF(func) else acc
          case Case(scrutinee, cases, default) =>
            val acc2 = cases.map(_._2) ++ default.toList
            acc2.foldLeft(acc)((acc, x) => find(x)(using acc))
          case Panic(msg) => acc
          case LetExpr(name, expr, body) => 
            val acc2 = find(expr)
            find(body)(using acc2)
          case LetMethodCall(names, cls, method, args, body) => find(body)(using acc.addC(cls))
          case LetCall(names, func, args, body) => find(body)(using if notBuiltin(func) then acc.addF(func) else acc)

      def find(func: Func): FuncAndClass = find(func.body)(using FuncAndClass())

    private def dfs(using visited: MutHMap[Local, Bool], out: Buf, postfix: Bool)(x: Func): Unit =
      trace[Unit](s"dfs: ${{showSym(x.name)}}"):
        visited.update(x.name, true)
        if !postfix then
          out.funcs += x.name
        val successors = Successors.find(x)
        successors.funcs.foreach:
          y => if !visited(y) then
            dfs(info.getFunc(y))
        successors.classes.foreach: y =>
          if notCallable(y) && !visited(y) then
            dfs(info.getClass(y))
        if postfix then
          out.funcs += x.name

    private def dfs(using visited: MutHMap[Local, Bool], out: Buf, postfix: Bool)(x: ClassInfo): Unit =
      trace[Unit](s"dfs: ${{showSym(x.name)}}"):
        visited.update(x.name, true)
        if !postfix then
          out.classes += x.name
        x.parents.foreach: y =>
          if notCallable(y) && !visited(y) then
            dfs(info.getClass(y))
        x.methods.values.foreach: m =>
          val successors = Successors.find(m.body)(using FuncAndClass())
          successors.funcs.foreach: y =>
            if !visited(y) then
              dfs(info.getFunc(y))
          successors.classes.foreach: y =>
            if notCallable(y) && !visited(y) then
              dfs(info.getClass(y))
        if postfix then
          out.classes += x.name
    
    private def dfs(using visited: MutHMap[Local, Bool], out: Buf, postfix: Bool)(x: Node): Unit =
      trace[Unit](s"dfs: $x"):
        val successors = Successors.find(x)(using FuncAndClass())
        successors.funcs.foreach: y =>
          if !visited(y) then
            dfs(info.getFunc(y))
        successors.classes.foreach: y =>
          if notCallable(y) && !visited(y) then
            dfs(info.getClass(y))

    def dfs(postfix: Bool): FuncAndClass =
      val visited = MutHMap[Local, Bool]()
      val allFuncsClassesMethods = info.func.keys ++ info.classes.iterator.keys
      visited.addAll(allFuncsClassesMethods.map(k => k -> false))
      val out = Buf(ListBuffer.empty, ListBuffer.empty)
      dfs(using visited, out, postfix)(info.func.get(info.entry).get)
      FuncAndClass(out.funcs.toList, out.classes.toList)

