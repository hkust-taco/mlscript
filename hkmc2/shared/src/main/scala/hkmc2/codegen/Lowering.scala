package hkmc2
package codegen

import scala.language.implicitConversions
import scala.annotation.tailrec
import os.{Path as AbsPath, RelPath}

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import semantics.*, ucs.FlatPattern
import hkmc2.{semantics => sem}
import semantics.{Term => st}
import semantics.Term.{Throw => _, *}
import semantics.Elaborator.{State, Ctx, ctx}

import syntax.{Literal, Tree}
import hkmc2.syntax.Fun


abstract class TailOp extends (Result => Block)
object Ret extends TailOp:
  def apply(r: Result): Block = Return(r, implct = false)
object ImplctRet extends TailOp:
  def apply(r: Result): Block =
    r match
    case Value.Lit(Tree.UnitLit(false)) => End()
    case _ => Return(r, implct = true)
object Thrw extends TailOp:
  def apply(r: Result): Block = Throw(r)


// * No longer in meaningful use and could be removed if we don't find a use for it:
class Subst(initMap: Map[Local, Value]):
  val map = initMap
  /*
  def +(kv: (Local, Value)): Subst =
    kv match
    case (ns: NamedSymbol, Value.Ref(ts: TempSymbol)) =>
      ts.nameHints += ns.name
    case _ =>
    Subst(map + kv)
  */
  def apply(v: Value): Value = v match
    case Value.Ref(l) => map.getOrElse(l, v)
    case _ => v
object Subst:
  val empty = Subst(Map.empty)
  def subst(using sub: Subst): Subst = sub
end Subst

import Subst.subst


class Lowering()(using Config, TL, Raise, State, Ctx):
  
  extension (t: Term)
    def instantiated = t match
      case r: Resolvable =>
        tl.trace[Term](s"Expanding term ${r}", post = t => s"~> ${t}"):
          r.expanded
      case t => t
  
  val lowerHandlers: Bool = config.effectHandlers.isDefined
  val lift: Bool = config.liftDefns.isDefined

  private lazy val unreachableFn =
    Select(Value.Ref(State.runtimeSymbol), Tree.Ident("unreachable"))(N)
  
  def unit: Path =
    Select(Value.Ref(State.runtimeSymbol), Tree.Ident("Unit"))(S(State.unitSymbol))
  
  
  def fail(err: ErrorReport): Block =
    raise(err)
    End("error")
  
  
  // type Rcd = (mut: Bool, args: List[RcdArg]) // * Better, but Scala's patmat exhaustiveness chokes on it
  type Rcd = (Bool, List[RcdArg])
  
  def returnedTerm(t: st)(using Subst): Block = term(t)(Ret)
  
  def parentConstructor(cls: Term, args: Ls[Term])(using Subst) = 
    if args.length > 1 then 
      raise:
        ErrorReport(
          msg"Extending a class with multiple parameter lists is not supported" -> Loc(cls :: args) :: Nil,
          source = Diagnostic.Source.Compilation
        )
    lowerCall(
      Value.Ref(State.builtinOpsMap("super")),
      isMlsFun = true,
      args.headOption,
      N, // TODO: location?
    )(c => Return(c, implct = true))
  
  // * Used to work around Scala's @tailrec annotation for those few calls that are not in tail position.
  final def term_nonTail(t: st, inStmtPos: Bool = false)(k: Result => Block)(using Subst): Block =
    term(t: st, inStmtPos: Bool)(k)
  

  @tailrec
  final def splitBlock(stats: Ls[Statement], imps: Ls[Import], funs: Ls[TermDefinition], rest: Ls[Statement])
      : (Ls[Import], Ls[TermDefinition], Ls[Statement])
      =
    stats match
    case (imp: Import) :: stats =>
      splitBlock(stats, imp :: imps, funs, rest)
    case (fun: TermDefinition) :: stats if fun.k is syntax.Fun =>
      splitBlock(stats, imps, fun :: funs, rest)
    case stat :: stats =>
      splitBlock(stats, imps, funs, stat :: rest)
    case Nil =>
      (imps.reverse, funs.reverse, rest.reverse)
  
  
  def block(stats: Ls[Statement], res: Rcd \/ Term)(k: Result => Block)(using Subst): Block =
    // TODO we should also isolate and reorder classes by inheritance topological sort
    val (imps, funs, rest) = splitBlock(stats, Nil, Nil, Nil)
    blockImpl(imps ::: funs ::: rest, res)(k)
  
  def blockImpl(stats: Ls[Statement], res: Rcd \/ Term)(k: Result => Block)(using Subst): Block =
    stats match
    case (t: sem.Term) :: stats =>
      subTerm(t, inStmtPos = true): r =>
        blockImpl(stats, res)(r => k(r))
    case Nil =>
      res match
      case R(res) => term(res)(k)
      case L((mut, flds)) =>
        k(Record(mut, flds.reverse))
    case RcdSpread(bod) :: stats =>
      res match
      case R(_) => wat("RcdField in non-Rcd context", res)
      case L((mut, flds)) =>
        subTerm(bod): l =>
          blockImpl(stats, L((mut, RcdArg(N, l) :: flds)))(k)
    case RcdField(lhs, rhs) :: stats =>
      res match
      case R(_) => wat("RcdField in non-Rcd context", res)
      case L((mut, flds)) =>
        subTerm(lhs): l =>
          subTerm_nonTail(rhs): r =>
            blockImpl(stats, L((mut, RcdArg(S(l), r) :: flds)))(k)
    case (decl @ LetDecl(sym, annotations)) :: (stats @ ((_: DefineVar) :: _)) =>
      reportAnnotations(decl, annotations)
      blockImpl(stats, res)(k)
    case (decl @ LetDecl(sym, annotations)) :: stats =>
      reportAnnotations(decl, annotations)
      blockImpl(DefineVar(sym, Term.Lit(Tree.UnitLit(false))) :: stats, res)(k)
    case DefineVar(sym, rhs) :: stats =>
      term(rhs): r =>
        Assign(sym, r, blockImpl(stats, res)(k))
    case (imp @ Import(sym, path)) :: stats =>
      raise(ErrorReport(
        msg"Imports must be at the top level" ->
        imp.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      blockImpl(stats, res)(k)
    case (d: Declaration) :: stats =>
      d match
      case td: TermDefinition =>
        reportAnnotations(td, td.extraAnnotations)
        td.body match
        case N => // abstract declarations have no lowering
          blockImpl(stats, res)(k)
        case S(bod) =>
          td.k match
          case knd: syntax.Val =>
            assert(td.params.isEmpty)
            subTerm_nonTail(bod)(r =>
              // Assign(td.sym, r,
              //   term(st.Blk(stats, res))(k)))
              Define(ValDefn(td.tsym, td.sym, r),
                blockImpl(stats, res)(k)))
          case syntax.Fun =>
            val (paramLists, bodyBlock) = setupFunctionOrByNameDef(td.params, bod, S(td.sym.nme))
            Define(FunDefn(td.owner, td.sym, paramLists, bodyBlock),
              blockImpl(stats, res)(k))
          case syntax.Ins =>
            // Implicit instances are not parameterized for now.
            assert(td.params.isEmpty)
            subTerm(bod)(r =>
              Define(ValDefn(td.tsym, td.sym, r),
                blockImpl(stats, res)(k)))
          case syntax.LetBind | syntax.ParamBind | syntax.HandlerBind => fail:
            ErrorReport(
              msg"Unexpected declaration kind '${td.k.str}' in lowering" -> td.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
      case cls: ClassLikeDef if cls.sym.defn.exists(_.hasDeclareModifier.isDefined) =>
        // * Declarations have no lowering
        blockImpl(stats, res)(k)
      case cls: ClassDef if cls.moduleCompanion.isDefined =>
        // * Class definitions are pure, but their companions might not be,
        // * as they may contain static initialization code;
        // * therefore, we lower classes at the point where the companion is defined,
        // * if it is defined, rather than at the point where the class is defined.
        reportAnnotations(cls, cls.extraAnnotations)
        blockImpl(stats, res)(k)
      case _defn: ClassLikeDef =>
        val defn = _defn match
          case cls: ClassDef => cls
          case mod: ModuleOrObjectDef if mod.kind is syntax.Mod => // * Currently, both objects and modules are represented as `ModuleOrObjectDef`s
            mod.classCompanion match
            case S(comp) => comp.defn.getOrElse(wat("Module companion without definition", mod.companion))
            case N =>
              ClassDef.Plain(mod.owner, syntax.Cls, new ClassSymbol(Tree.DummyTypeDef(syntax.Cls), mod.sym.id),
                mod.bsym,
                Nil,
                N,
                ObjBody(Blk(Nil, UnitVal())),
                S(mod.sym),
                Nil,
              )
          case _ => _defn
        reportAnnotations(defn, defn.extraAnnotations)
        val (mtds, publicFlds, privateFlds, ctor) = defn match
          case pd: PatternDef => compilePatternMethods(pd)
          case _ => gatherMembers(defn.body)
        val mod = defn.companion match
          case S(sym) =>
            sym.defn match
            case S(mod: ModuleOrObjectDef) =>
              mod.ext match
              case S(ext) => fail:
                ErrorReport(
                  msg"Modules cannot have an extension clause." -> ext.toLoc :: Nil,
                  source = Diagnostic.Source.Compilation
                )
              case N =>
              val (mtds, publicFlds, privateFlds, ctor) =
                gatherMembers(mod.body)
              S(ClsLikeBody(mod.sym, mtds, privateFlds, publicFlds, ctor))
            case _ => N
          case _ => N
        defn.ext match
        case N =>
          Define(
            ClsLikeDefn(defn.owner, defn.sym, defn.bsym, defn.kind, defn.paramsOpt, defn.auxParams, N,
              mtds,
              privateFlds,
              publicFlds,
              End(),
              ctor,
              mod,
            ),
            blockImpl(stats, res)(k))
        case S(ext) =>
          assert(k isnt syntax.Mod) // modules can't extend things and can't have super calls
          subTerm(ext.cls): clsp =>
            val pctor = parentConstructor(ext.cls, ext.args)
            Define(
              ClsLikeDefn(
                defn.owner, defn.sym, defn.bsym, defn.kind, defn.paramsOpt, defn.auxParams, S(clsp),
                mtds, privateFlds, publicFlds, pctor, ctor, mod
              ),
              blockImpl(stats, res)(k)
            )
      case td: TypeDef => // * Type definitions are erased
        blockImpl(stats, res)(k)
  
  
  def lowerCall(fr: Path, isMlsFun: Bool, arg: Opt[Term], loc: Opt[Loc])(k: Result => Block)(using Subst): Block =
    arg match
    case S(a) =>
      lowerCall(fr, isMlsFun, a, loc)(k)
    case N =>
      // * No arguments means a nullary call, e.g., `f()`
      k(Call(fr, Nil)(isMlsFun, true).withLoc(loc))
  def lowerCall(fr: Path, isMlsFun: Bool, arg: Term, loc: Opt[Loc])(k: Result => Block)(using Subst): Block =
    lowerArg(arg)(as => k(Call(fr, as)(isMlsFun, true).withLoc(loc)))
  
  def lowerArg(arg: Term)(k: Ls[Arg] => Block)(using Subst): Block =
    arg match
    case Tup(fs) =>
      if fs.exists(e => e match
        case Spd(false, _) => true // is lazy spread
        case _ => false)
      then
        raise(ErrorReport(
          msg"Lazy spreads are not supported in call arguments" -> arg.toLoc :: Nil, S(arg),
          source = Diagnostic.Source.Compilation))
      args(fs)(as => k(as))
    case _ =>
      // Application arguments that are not tuples represent spreads, as in `f(...arg)`
      subTerm_nonTail(arg): ar =>
        k(Arg(spread = S(true), ar) :: Nil)
  
  @tailrec
  final def term(t: st, inStmtPos: Bool = false)(k: Result => Block)(using Subst): Block =
    tl.log(s"Lowering.term ${t.showDbg.truncate(100, "[...]")}${
      if inStmtPos then " (in stmt)" else ""}${
      t.resolvedSym.fold("")(" – symbol " + _)}")
    
    def warnStmt = if inStmtPos then
      raise:
        WarningReport(msg"Pure expression in statement position" -> t.toLoc :: Nil, S(t))
    
    t.instantiated match
    case st.UnitVal() => k(unit)
    case st.Lit(lit) =>
      warnStmt
      k(Value.Lit(lit))
    case st.Ret(res) =>
      returnedTerm(res)
    case st.Throw(res) =>
      term(res)(Thrw)
    case st.Asc(lhs, rhs) =>
      term(lhs, inStmtPos = inStmtPos)(k)
    case st.Tup(fs) =>
      args(fs)(args => k(Tuple(mut = false, args)))
    case Mut(st.Tup(fs)) =>
      args(fs)(args => k(Tuple(mut = true, args)))
    case st.CtxTup(fs) =>
      // * This case is currently triggered for code such as `f(using 42)`
      args(fs)(args => k(Tuple(mut = false, args)))
    case ref @ st.Ref(sym) =>
      sym match
      case ctx.builtins.source.bms | ctx.builtins.js.bms | ctx.builtins.debug.bms | ctx.builtins.annotations.bms =>
        return fail:
          ErrorReport(
            msg"Module '${sym.nme}' is virtual (i.e., \"compiler fiction\"); cannot be used directly" -> t.toLoc ::
            Nil, S(t), source = Diagnostic.Source.Compilation)
      case sym if sym.asCls.exists(ctx.builtins.virtualClasses) =>
        return fail:
          ErrorReport(
            msg"Symbol '${sym.nme}' is virtual (i.e., \"compiler fiction\"); cannot be used as a term" -> t.toLoc ::
            Nil, S(t), source = Diagnostic.Source.Compilation)
      case _ => ()
      
      sym match
      case sym: BuiltinSymbol =>
        warnStmt
        if sym.binary then
          val t1 = new Tree.Ident("arg1")
          val t2 = new Tree.Ident("arg2")
          val p1 = Param(FldFlags.empty, VarSymbol(t1), N, Modulefulness.none)
          val p2 = Param(FldFlags.empty, VarSymbol(t2), N, Modulefulness.none)
          val ps = PlainParamList(p1 :: p2 :: Nil)
          val bod = st.App(t, st.Tup(List(st.Ref(p1.sym)(t1, 666, N).resolve, st.Ref(p2.sym)(t2, 666, N).resolve))
            (Tree.Tup(Nil // FIXME should not be required (using dummy value)
              )))(
              Tree.App(Tree.Empty(), Tree.Empty()), // FIXME should not be required (using dummy value)
              N,
              FlowSymbol(sym.nme)
            ).resolve
          val (paramLists, bodyBlock) = setupFunctionDef(ps :: Nil, bod, S(sym.nme))
          tl.log(s"Ref builtin $sym")
          assert(paramLists.length === 1)
          return k(Lambda(paramLists.head, bodyBlock).withLocOf(ref))
        if sym.unary then
          val t1 = new Tree.Ident("arg")
          val p1 = Param(FldFlags.empty, VarSymbol(t1), N, Modulefulness.none)
          val ps = PlainParamList(p1 :: Nil)
          val bod = st.App(t, st.Tup(List(st.Ref(p1.sym)(t1, 666, N).resolve))
            (Tree.Tup(Nil // FIXME should not be required (using dummy value)
              )))(
              Tree.App(Tree.Empty(), Tree.Empty()), // FIXME should not be required (using dummy value)
              N,
              FlowSymbol(sym.nme)
            ).resolve
          val (paramLists, bodyBlock) = setupFunctionDef(ps :: Nil, bod, S(sym.nme))
          tl.log(s"Ref builtin $sym")
          assert(paramLists.length === 1)
          return k(Lambda(paramLists.head, bodyBlock).withLocOf(ref))
      case bs: BlockMemberSymbol =>
        bs.defn match
        case S(d) if d.hasDeclareModifier.isDefined =>
          return term(Sel(State.globalThisSymbol.ref().resolve, ref.tree)(S(bs), N).withLocOf(ref).resolve)(k)
        case S(td: TermDefinition) if td.k is syntax.Fun =>
          // * Local functions with no parameter lists are getters
          // * and are lowered to functions with an empty parameter list
          // * (non-local functions are compiled into getter methods selected on some prefix)
          if td.params.isEmpty then
            val l = new TempSymbol(S(t))
            return Assign(l, Call(Value.Ref(bs).withLocOf(ref), Nil)(true, true), k(Value.Ref(l)))
        case S(_) => ()
        case N => () // TODO panic here; can only lower refs to elab'd symbols
      case _ => ()
      warnStmt
      k(subst(Value.Ref(sym).withLocOf(ref)))
    case st.App(ref @ Ref(sym: BuiltinSymbol), arg) =>
      arg match
      case st.Tup(Nil) =>
        if !sym.nullary then raise:
          ErrorReport(
            msg"Expected arguments for builtin operator '${sym.nme}'" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        k(Value.Ref(sym).withLocOf(ref))
      case st.Tup(Fld(FldFlags.benign(), arg, N) :: Nil) =>
        if !sym.unary then raise:
          ErrorReport(
            msg"Builtin '${sym.nme}' is not a unary operator" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg): ar =>
          k(Call(Value.Ref(sym).withLocOf(ref), Arg(N, ar) :: Nil)(true, false))
      case st.Tup(Fld(FldFlags.benign(), arg1, N) :: Fld(FldFlags.benign(), arg2, N) :: Nil) =>
        if !sym.binary then raise:
          ErrorReport(
            msg"Builtin '${sym.nme}' is not a binary operator" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg1): ar1 =>
          val isAnd = sym is State.andSymbol
          val isOr = sym is State.orSymbol
          if isAnd || isOr then
            val lamSym = BlockMemberSymbol("lambda", Nil, false)
            val lamDef = FunDefn(N, lamSym, PlainParamList(Nil) :: Nil, returnedTerm(arg2))
            Define(
              lamDef,
              k(Call(
                Value.Ref(State.runtimeSymbol).selN(Tree.Ident(if isAnd then "short_and" else "short_or")),
                Arg(N, ar1) :: Arg(N, Value.Ref(lamSym)) :: Nil
              )(true, false)))
          else
            subTerm_nonTail(arg2): ar2 =>
              k(Call(Value.Ref(sym).withLocOf(ref), Arg(N, ar1) :: Arg(N, ar2) :: Nil)(true, false))
      case _ => fail:
        ErrorReport(
          msg"Unexpected arguments for builtin symbol '${sym.nme}'" -> arg.toLoc :: Nil, S(arg),
          source = Diagnostic.Source.Compilation)
    case st.TyApp(f, ts) => term(f)(k) // * Type arguments are erased
    case st.App(f, arg) =>
      val isMlsFun = f.resolvedSym.fold(f.isInstanceOf[st.Lam]):
        case _: sem.BuiltinSymbol => true
        case sym: sem.BlockMemberSymbol =>
          sym.trmImplTree.fold(sym.clsTree.isDefined)(_.k is syntax.Fun)
        // Do not perform safety check on `MatchResult` and `MatchFailure`.
        case sym => (sym is State.matchResultClsSymbol) ||
          (sym is State.matchFailureClsSymbol)
      def conclude(fr: Path) = lowerCall(fr, isMlsFun, arg, t.toLoc)(k)
      // * We have to instantiate `f` again because, if `f` is a Sel, the `term`
      // * function is not called again with f. See below `Sel` and `SelProj` cases.
      f.instantiated match
      case t if t.resolvedSym.isDefined && (t.resolvedSym.get is ctx.builtins.js.try_catch) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("try_catch")))
      case t if t.resolvedSym.isDefined && (t.resolvedSym.get is ctx.builtins.debug.printStack) =>
        if !config.effectHandlers.exists(_.debug) then
          return fail:
            ErrorReport(
              msg"Debugging functions are not enabled" ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
        conclude(Value.Ref(State.runtimeSymbol).selSN("raisePrintStackEffect").withLocOf(f))
      case t if t.resolvedSym.isDefined && (t.resolvedSym.get is ctx.builtins.debug.getLocals) =>
        if !config.effectHandlers.exists(_.debug) then
          return fail:
            ErrorReport(
              msg"Debugging functions are not enabled" ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
        conclude(Value.Ref(ctx.builtins.debug.getLocals).withLocOf(f))
      // * Due to whacky JS semantics, we need to make sure that selections leading to a call
      // * are preserved in the call and not moved to a temporary variable.
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(sel.sym).withLocOf(sel))
      case sel @ SelProj(prefix, _, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(sel.sym).withLocOf(sel))
      case _ => subTerm(f)(conclude)
    case h @ Handle(lhs, rhs, as, cls, defs, bod) =>
      if !lowerHandlers then
        return fail:
          ErrorReport(
            msg"Effect handlers are not enabled" ->
            h.toLoc :: Nil,
            source = Diagnostic.Source.Compilation)
      val handlers = defs.map {
        case HandlerTermDefinition(resumeSym, td) => td.body match
          case None => 
            raise(ErrorReport(msg"Handler function definitions cannot be empty" -> td.toLoc :: Nil))
            N
          case Some(bod) =>
            val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))      
            S(Handler(td.sym, resumeSym, paramLists, bodyBlock))
      }.collect{ case Some(v) => v }
      val resSym = TempSymbol(S(t))
      subTerm(rhs): par =>
        subTerms(as): asr =>
          HandleBlock(lhs, resSym, par, asr, cls, handlers,
            term_nonTail(bod)(Ret),
            k(Value.Ref(resSym)))
    case st.Blk(sts, res) => block(sts, R(res))(k)
    case Assgn(lhs, rhs) =>
      lhs match
      case Ref(sym) =>
        subTerm(rhs): r =>
          Assign(sym, r, k(unit))
      case sel @ SynthSel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, nme, r, k(unit))(sel.sym)
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, nme, r, k(unit))(sel.sym)
      case sel @ DynSel(prefix, fld, ai) =>
        subTerm(prefix): p =>
          subTerm_nonTail(fld): f =>
            subTerm_nonTail(rhs): r =>
              AssignDynField(p, f, ai, r, k(unit))
      case _ => fail:
        ErrorReport(
          msg"Unexpected left-hand side in assignment (${lhs.describe})" -> lhs.toLoc :: Nil, S(lhs),
          source = Diagnostic.Source.Compilation)
      
    case st.Lam(params, body) =>
      warnStmt
      val (paramLists, bodyBlock) = setupFunctionDef(params :: Nil, body, N)
      if k.isInstanceOf[TailOp] || bodyBlock.size <= 5
      then k(Lambda(paramLists.head, bodyBlock))
      else
        val lamSym = new BlockMemberSymbol("lambda", Nil, false)
        val lamDef = FunDefn(N, lamSym, paramLists, bodyBlock)
        Define(
          lamDef,
          k(lamSym |> Value.Ref.apply))
    
    /* 
    case t @ st.If(Split.Let(sym, trm, tail)) =>
      // term(st.Blk(semantics.LetDecl(sym) :: semantics.DefineVar(sym, trm) :: Nil, st.If(tail)(t.normalized)))(k)
      term(trm): r =>
        Assign(sym, r, term(st.If(tail)(t.normalized))(k))
    
    // TODO rm
    case st.If(Split.Cons(
      Branch(scrut, Pattern.LitPat(tru @ Tree.BoolLit(true)), Split.Else(thn)),
      restSplit
    )) =>
      
      val elseBranch = restSplit match
        case Split.Else(els) => S(els)
        case Split.Nil => N
      
      elseBranch match
      case S(els) if k.isInstanceOf[Ret] =>
        subTerm(scrut): sr =>
          // Match(sr, Case.Lit(tru) -> term(thn)(k) :: Nil,
          //   Some(term(els)(k)), 
          //   Unreachable
          // )
          Match(sr, Case.Lit(tru) -> term(thn)(k) :: Nil,
            N, 
            term(els)(k)
          )
      case _ =>
        val l = new TempSymbol(S(t))
        subTerm(scrut): sr =>
            Match(sr, Case.Lit(tru) -> subTerm(thn)(r => Assign(l, r, End())) :: Nil,
              elseBranch.map(els => subTerm(els)(r => Assign(l, r, End()))),
              k(Value.Ref(l))
            )
    */
    
    case iftrm: st.IfLike =>
      
      tl.log(s"${iftrm.kw} $iftrm")
      
      val isIf = iftrm.kw match
        case syntax.Keyword.`if` => true
        case syntax.Keyword.`while` => false
      val isWhile = !isIf
      
      var usesResTmp = false
      lazy val l =
        usesResTmp = true
        new TempSymbol(S(t))
      
      lazy val lbl =
        new TempSymbol(S(t))
      
      def go(split: Split, topLevel: Bool)(using Subst): Block = split match
        case Split.Let(sym, trm, tl) =>
          term_nonTail(trm): r =>
            Assign(sym, r, go(tl, topLevel))
        case Split.Cons(Branch(scrut, pat, tail), restSplit) =>
          subTerm_nonTail(scrut): sr =>
            tl.log(s"Binding scrut $scrut to $sr (${summon[Subst].map})")
            // val cse = 
            def mkMatch(cse: Case -> Block) = Match(sr, cse :: Nil,
                S(go(restSplit, topLevel = true)),
                End()
              )
            pat match
              case FlatPattern.Lit(lit) => mkMatch(Case.Lit(lit) -> go(tail, topLevel = false))
              case FlatPattern.ClassLike(ctor, argsOpt, _mode, _refined) =>
                /** Make a continuation that creates the match. */
                def k(ctorSym: ClassLikeSymbol, clsParams: Ls[TermSymbol])(st: Path): Block =
                  val args = argsOpt.map(_.map(_.scrutinee)).getOrElse(Nil)
                  // Normalization should reject cases where the user provides
                  // more sub-patterns than there are actual class parameters.
                  assert(argsOpt.isEmpty || args.length <= clsParams.length, (argsOpt, clsParams))
                  def mkArgs(args: Ls[TermSymbol -> BlockLocalSymbol])(using Subst): Case -> Block = args match
                    case Nil =>
                      Case.Cls(ctorSym, st) -> go(tail, topLevel = false)
                    case (param, arg) :: args =>
                      val (cse, blk) = mkArgs(args)
                      (cse, Assign(arg, Select(sr, new Tree.Ident(param.id.name).withLocOf(arg))(S(param)), blk))
                  mkMatch(mkArgs(clsParams.iterator.zip(args).toList))
                ctor.symbol.flatMap(_.asClsOrMod) match
                  case S(cls: ClassSymbol) if ctx.builtins.virtualClasses contains cls =>
                    // [invariant:0] Some classes (e.g., `Int`) from `Prelude` do
                    // not exist at runtime. If we do lowering on `trm`, backends
                    // (e.g., `JSBuilder`) will not be able to handle the corresponding selections.
                    // In this case the second parameter of `Case.Cls` will not be used.
                    // So we do not elaborate `ctor` when the `cls` is virtual
                    // and use it `Predef.unreachable` here.
                    k(cls, Nil)(unreachableFn)
                  case S(cls: ClassSymbol) => subTerm_nonTail(ctor)(k(cls, cls.tree.clsParams))
                  case S(mod: ModuleOrObjectSymbol) => subTerm_nonTail(ctor)(k(mod, Nil))
                  case N =>
                    // Normalization have already checked the constructor
                    // resolves to a class or module. Branches with unresolved
                    // constructors should have been removed.
                    lastWords("Pattern.ClassLike: constructor is neither a class nor a module")
              case FlatPattern.Tuple(len, inf) => mkMatch(Case.Tup(len, inf) -> go(tail, topLevel = false))
              case FlatPattern.Record(entries) =>
                val objectSym = ctx.builtins.Object
                mkMatch( // checking that we have an object
                  Case.Cls(objectSym, Value.Ref(BuiltinSymbol(objectSym.nme, false, false, true, false))),
                  entries.foldRight(go(tail, topLevel = false)):
                    case ((fieldName, fieldSymbol), blk) =>
                      mkMatch(
                        Case.Field(fieldName, safe = true), // we know we have an object, no need to check again
                        Assign(fieldSymbol, Select(sr, fieldName)(N), blk)
                      )
                )
        case Split.Else(els) =>
          if k.isInstanceOf[TailOp] && isIf then term_nonTail(els)(k)
          else
            term_nonTail(els): r =>
              Assign(l, r,
                if isWhile && !topLevel then Continue(lbl)
                else End()
              )
        case Split.End =>
          Throw(Instantiate(mut = false, Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Error"))(N),
            Value.Lit(syntax.Tree.StrLit("match error")).asArg :: Nil)) // TODO add failed-match scrutinee info
      
      val normalize = ucs.Normalization()
      val normalized = tl.scoped("ucs:normalize"):
        normalize(iftrm.desugared)
      tl.scoped("ucs:normalized"):
        tl.log(s"Normalized:\n${normalized.prettyPrint}")

      if k.isInstanceOf[TailOp] && isIf then go(normalized, topLevel = true)
      else
        val body = if isWhile
          then Label(lbl, go(normalized, topLevel = true), End())
          else go(normalized, topLevel = true)
        Begin(
          body,
          if usesResTmp then k(Value.Ref(l))
          else k(unit) // * it seems this currently never happens
        )
      
    case sel @ Sel(prefix, nme) =>
      setupSelection(prefix, nme, sel.sym)(k)
        
    case sel @ SynthSel(prefix, nme) =>
      // * Not using `setupSelection` as these selections are not meant to be sanity-checked
      subTerm(prefix): p =>
        k(Select(p, nme)(sel.sym))
        
    case DynSel(prefix, fld, ai) =>
      subTerm(prefix): p =>
        subTerm_nonTail(fld): f =>
          k(DynSelect(p, f, ai))
      
      
    case nw @ (_: New | _: DynNew | Mut(_: New | _: DynNew)) =>
      val (mut, cls, as, rft) = nw match
        case New(c, a, r) => (false, c, a, r)
        case Mut(New(c, a, r)) => (true, c, a, r)
        case DynNew(c, a) => (false, c, a, N)
        case Mut(DynNew(c, a)) => (true, c, a, N)
        case _ => spuriousWarning
      subTerm(cls): sr =>
        rft match
        case N =>
          as match
          case Nil =>
            k(Instantiate(mut, sr, Nil))
          case a :: Nil => lowerArg(a): asr =>
            k(Instantiate(mut, sr, asr))
          case a :: as => lowerArg(a): asr =>
            val z = as.foldLeft[Path => Block](k): (acc, arg) => 
              inner =>
                lowerArg(arg): asr2 =>
                  val ts = TempSymbol(N)
                  Assign(ts, Call(inner, asr2)(true, true), acc(Value.Ref(ts)))
            val ts = TempSymbol(N)
            Assign(ts, Instantiate(mut, sr, asr), z(Value.Ref(ts)))
        case S((isym, rft)) =>
          val sym = new BlockMemberSymbol(isym.name, Nil)
          val (mtds, publicFlds, privateFlds, ctor) = gatherMembers(rft)
          val pctor = parentConstructor(cls, as)
          val clsDef = ClsLikeDefn(N, isym, sym, syntax.Cls, N, Nil, S(sr),
            mtds, privateFlds, publicFlds, pctor, ctor, N)
          val inner = new New(sym.ref().resolve, Nil, N)
          Define(clsDef, term_nonTail(if mut then Mut(inner) else inner)(k))
      
    case Try(sub, finallyDo) =>
      val l = new TempSymbol(S(sub))
      TryBlock(
        subTerm_nonTail(sub)(p => Assign(l, p, End())),
        subTerm_nonTail(finallyDo)(_ => End()),
        k(Value.Ref(l))
      )
    
    case Quoted(body) => quote(body)(k)
    
    // * BbML-specific cases: t.Cls#field and mutable operations
    case sp @ SelProj(prefix, _, proj) =>
      setupSelection(prefix, proj, sp.sym)(k)
    case Region(reg, body) =>
      Assign(reg, Instantiate(mut = false, Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Region"))(N), Nil),
        term_nonTail(body)(k))
    case RegRef(reg, value) =>
      plainArgs(reg :: value :: Nil): args =>
        k(Instantiate(mut = false, Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Ref"))(N), args))
    case Drop(ref) =>
      subTerm(ref): _ =>
        k(unit)
    case Deref(ref) =>
      subTerm(ref): r =>
        k(Select(r, Tree.Ident("value"))(N))
    case SetRef(lhs, rhs) =>
      subTerm(lhs): ref =>
        subTerm_nonTail(rhs): value =>
          AssignField(ref, Tree.Ident("value"), value, k(value))(N)
    
    case Mut(Rcd(mut, stats)) =>
      // * Note: I don't think this is supposed to happen...
      block(stats, L(mut -> Nil))(k)
    case Rcd(mut, stats) =>
      block(stats, L(mut -> Nil))(k)
    
    case Annotated(Annot.Untyped, receiver) =>
      term(receiver)(k)
    case Annotated(ann, receiver) =>
      raise(WarningReport(
        msg"This annotation has no effect." -> ann.toLoc ::
        msg"Such annotations are not supported on ${receiver.describe} terms." -> receiver.toLoc :: Nil))
      term(receiver)(k)
    case Missing => fail:
      ErrorReport(
        msg"Cannot compile ${t.describe} term that was not elaborated (maybe elaboration was one in 'lightweight' mode?)" ->
          t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation)
    case _: CompType | _: Neg | _: Term.FunTy | _: Term.Forall | _: Term.WildcardTy | _: Term.Unquoted
    => fail:
      ErrorReport(
        msg"Unexpected term form in expression position (${t.describe})" ->
          t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation)
    case Error => End("error")
    
    // case _ =>
    //   subTerm(t)(k)
  
  def setupTerm(name: Str, args: Ls[Path])(k: Result => Block)(using Subst): Block =
    k(Instantiate(mut = false, Value.Ref(State.termSymbol).selSN(name), args.map(_.asArg)))

  def setupQuotedKeyword(kw: Str): Path =
    Value.Ref(State.termSymbol).selSN("Keyword").selSN(kw)

  def setupSymbol(symbol: Local)(k: Result => Block)(using Subst): Block =
    k(Instantiate(mut = false, Value.Ref(State.termSymbol).selSN("Symbol"),
      Value.Lit(Tree.StrLit(symbol.nme)).asArg :: Nil))

  def quotePattern(p: FlatPattern)(k: Result => Block)(using Subst): Block = p match
    case FlatPattern.Lit(lit) => setupTerm("LitPattern", Value.Lit(lit) :: Nil)(k)
    case _ => // TODO
      fail:
        ErrorReport(
          msg"Unsupported quasiquote pattern type" ->
          p.toLoc :: Nil,
          source = Diagnostic.Source.Compilation
        )
  
  def quoteSplit(split: Split)(k: Result => Block)(using Subst): Block = split match
    case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => quote(scrutinee): r1 =>
      val l1, l2, l3, l4, l5 = new TempSymbol(N)
      blockBuilder.assign(l1, r1)
        .chain(b => quotePattern(pattern)(r2 => Assign(l2, r2, b)))
        .chain(b => quoteSplit(continuation)(r3 => Assign(l3, r3, b)))
        .chain(b => setupTerm("Branch", (l1 :: l2 :: l3 :: Nil).map(s => Value.Ref(s)))(r4 => Assign(l4, r4, b)))
        .chain(b => quoteSplit(tail)(r5 => Assign(l5, r5, b)))
        .rest(setupTerm("Cons", (l4 :: l5 :: Nil).map(s => Value.Ref(s)))(k))
    case Split.Let(sym, term, tail) => setupSymbol(sym): r1 =>
      val l1, l2, l3 = new TempSymbol(N)
      blockBuilder.assign(l1, r1)
        .chain(b => setupTerm("Ref", Value.Ref(l1) :: Nil)(r => Assign(sym, r, b)))
        .chain(b => quote(term)(r2 => Assign(l2, r2, b)))
        .chain(b => quoteSplit(tail)(r3 => Assign(l3, r3, b)))
        .rest(setupTerm("Let", (l1 :: l2 :: l3 :: Nil).map(s => Value.Ref(s)))(k))
    case Split.Else(default) => quote(default): r =>
      val l = new TempSymbol(N)
      Assign(l, r, setupTerm("Else", Value.Ref(l) :: Nil)(k))
    case Split.End => setupTerm("End", Nil)(k)

  lazy val setupFilename: Path =
    val state = summon[State]
    Value.Ref(state.importSymbol).selSN("meta").selSN("url")

  def quote(t: st)(k: Result => Block)(using Subst): Block = t match
    case Lit(lit) =>
      setupTerm("Lit", Value.Lit(lit) :: Nil)(k)
    case Ref(sym) if Elaborator.binaryOps.contains(sym.nme) => // builtin symbols
      val l = new TempSymbol(N)
      setupTerm("Builtin", Value.Lit(Tree.StrLit(sym.nme)) :: Nil)(k)
    case Ref(sym) =>
      k(Value.Ref(sym))
    case SynthSel(Ref(sym: ModuleOrObjectSymbol), name) => // Local cross-stage references
      setupSymbol(sym): r1 =>
        val l1, l2 = new TempSymbol(N)
        Assign(l1, r1, setupTerm("CSRef", Value.Ref(l1) :: setupFilename :: Value.Lit(syntax.Tree.UnitLit(false)) :: Nil)(r2 =>
          Assign(l2, r2, setupTerm("Sel", Value.Ref(l2) :: Value.Lit(syntax.Tree.StrLit(name.name)) :: Nil)(k))
        ))
    case SynthSel(Ref(sym: BlockMemberSymbol), name) => // Multi-file cross-stage references
      (t.toLoc, sym.toLoc) match
        case (S(Loc(_, _, Origin(base, _, _))), S(Loc(_, _, Origin(filename, _, _)))) => setupSymbol(sym): r1 =>
          val l1, l2 = new TempSymbol(N)
          val basePath = base / os.up
          val targetPath = filename
          val relPath = targetPath.relativeTo(basePath).toString
          Assign(l1, r1, setupTerm("CSRef", Value.Ref(l1) :: setupFilename :: Value.Lit(syntax.Tree.StrLit(relPath)) :: Nil)(r2 =>
            Assign(l2, r2, setupTerm("Sel", Value.Ref(l2) :: Value.Lit(syntax.Tree.StrLit(name.name)) :: Nil)(k))
          ))
        case _ => fail:
          ErrorReport(
            msg"Cannot refer to imported module ${sym.nme} due to the lack of path." ->
            t.toLoc :: Nil,
            source = Diagnostic.Source.Compilation
          )
    case Lam(params, body) =>
      def rec(ps: Ls[LocalSymbol & NamedSymbol], ds: Ls[Path])(k: Result => Block)(using Subst): Block = ps match
        case Nil => quote(body): r =>
          val l = new TempSymbol(N)
          val arr = new TempSymbol(N, "arr")
          Assign(
            arr,
            Tuple(mut = false, ds.reverse.map(_.asArg)),
            Assign(l, r, setupTerm("Lam", Value.Ref(arr) :: Value.Ref(l) :: Nil)(k)))
        case sym :: rest =>
          setupSymbol(sym): r =>
            val l = new TempSymbol(N)
            Assign(l, r, setupTerm("Ref", Value.Ref(l) :: Nil): r1 =>
              Assign(sym, r1, rec(rest, Value.Ref(l) :: ds)(k)))
      rec(params.params.map(_.sym), Nil)(k) // TODO: restParam?
    case App(lhs, Tup(rhs)) => quote(lhs): r1 =>
      def rec(es: Ls[Elem], xs: Ls[Path])(k: Result => Block): Block = es match
        case Nil =>
          val arrSym = new TempSymbol(N, "arr")
          Assign(
            arrSym,
            Tuple(mut = false, xs.reverse.map(_.asArg)),
            setupTerm("Tup", Value.Ref(arrSym) :: Nil): r2 =>
              val l1 = new TempSymbol(N)
              val l2 = new TempSymbol(N)
              Assign(l1, r1, Assign(l2, r2, setupTerm("App", Value.Ref(l1) :: Value.Ref(l2) :: Nil)(k)))
          )
        case Fld(_, t, _) :: rest => quote(t): r2 =>
          val l = new TempSymbol(N)
          Assign(l, r2, rec(rest, Value.Ref(l) :: xs)(k))
        case Spd(eager, term) :: rest =>
          fail:
            ErrorReport(
              msg"Unsupported spread in quasiquote application" ->
              term.toLoc :: Nil,
              source = Diagnostic.Source.Compilation
            )
      rec(rhs, Nil)(k)
    case Blk(LetDecl(sym, _) :: DefineVar(sym2, rhs) :: Nil, res) => // Let bindings
      require(sym2 is sym)
      setupSymbol(sym){r1 =>
        val l1, l2, l3, l4, l5 = new TempSymbol(N)
        val arrSym = new TempSymbol(N, "arr")
        blockBuilder.assign(l1, r1)
          .chain(b => setupTerm("Ref", Value.Ref(l1) :: Nil)(r => Assign(sym, r, b)))
          .chain(b => quote(rhs)(r2 => Assign(l2, r2, b)))
          .chain(b => quote(res)(r3 => Assign(l3, r3, b)))
          .chain(b => setupTerm("LetDecl", Value.Ref(l1) :: Nil)(r4 => Assign(l4, r4, b)))
          .chain(b => setupTerm("DefineVar", Value.Ref(l1) :: Value.Ref(l2) :: Nil)(r5 => Assign(l5, r5, b)))
          .assign(arrSym, Tuple(mut = false, (l4 :: l5 :: Nil).map(s => Value.Ref(s).asArg)))
          .rest(setupTerm("Blk", Value.Ref(arrSym) :: Value.Ref(l3) :: Nil)(k))
      }
    case IfLike(syntax.Keyword.`if`, split) => quoteSplit(split): r =>
      val l = new TempSymbol(N)
      Assign(l, r, setupTerm("IfLike", setupQuotedKeyword("If") :: Value.Ref(l) :: Nil)(k))
    case Unquoted(body) => term(body)(k)
    case _ => fail:
      ErrorReport(
        msg"Unsupported quasiquote type ${t.describe}" ->
        t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation
      )
  
  def gatherMembers(clsBody: ObjBody)(using Subst)
  : (Ls[FunDefn], Ls[BlockMemberSymbol -> TermSymbol], Ls[TermSymbol], Block) =
    val mtds = clsBody.methods
      .flatMap: td =>
        td.body.map: bod =>
          val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
          FunDefn(td.owner, td.sym, paramLists, bodyBlock)
    val publicFlds = clsBody.publicFlds.map(f => f.sym -> f.tsym)
    val privateFlds = clsBody.nonMethods.collect:
      case decl @ LetDecl(sym: TermSymbol, annotations) =>
        reportAnnotations(decl, annotations)
        sym
    val ctor =
      term_nonTail(Blk(clsBody.nonMethods, clsBody.blk.res))(ImplctRet)
        // * This is just a minor improvement to get `constructor() {}` instead of `constructor() { null }`
        .mapTail:
          case Return(Value.Lit(syntax.Tree.UnitLit(true)), true) => End()
          case t => t
    (mtds, publicFlds, privateFlds, ctor)
  
  /** Compile the pattern definition into `unapply` and `unapplyStringPrefix`
   *  methods using the `NaiveCompiler`, which transliterate the pattern into
   *  UCS splits that backtrack without any optimizations. */
  def compilePatternMethods(defn: PatternDef)(using Subst):
      // The return type is intended to be consistent with `gatherMembers`
      (Ls[FunDefn], Ls[BlockMemberSymbol -> TermSymbol], Ls[TermSymbol], Block) =
    val compiler = new ups.NaiveCompiler
    val methods = compiler.compilePattern(defn)
    val mtds = methods
      .flatMap: td =>
        td.body.map: bod =>
          val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
          FunDefn(td.owner, td.sym, paramLists, bodyBlock)
    (mtds, Nil, Nil, End())
  
  def args(elems: Ls[Elem])(k: Ls[Arg] => Block)(using Subst): Block =
    val as = elems.map:
      case sem.Fld(sem.FldFlags.benign(), value, N) => R(N -> value)
      case sem.Fld(sem.FldFlags.benign(), idx, S(rhs)) => L(idx -> rhs)
      case arg @ sem.Fld(flags, value, asc) => TODO(s"Other argument forms: $arg")
      case spd: Spd => R(S(spd.eager) -> spd.term)
    // * The straightforward way to lower arguments creates too much recursion depth
    // * and makes Lowering stack overflow when lowering functions with lots of arguments.
    /* 
    def rec(as: Ls[Bool -> st], asr: Ls[Arg]): Block = as match
      case Nil => k(Call(fr, asr.reverse)(isMlsFun, true))
      case (spd, a) :: as =>
        subTerm_nonTail(a): ar =>
          rec(as, Arg(spd, ar) :: asr)
    rec(as, Nil)
    */
    var asr: Ls[Arg] = Nil
    var fsr: Ls[RcdArg] = Nil
    def rec(as: Ls[(Term -> Term) \/ (Opt[Bool] -> st)]): Block = as match
      case Nil => End()
      case R((spd, a)) :: as =>
        subTerm_nonTail(a): ar =>
          asr ::= Arg(spd, ar)
          rec(as)
      case L((idx, t)) :: as =>
        subTerm_nonTail(idx): ir =>
          subTerm_nonTail(t): tr =>
            fsr ::= RcdArg(S(ir), tr)
            rec(as)
    val b = rec(as)
    if fsr.isEmpty then
      Begin(b, k(asr.reverse))
    else
      val rcdSym = new TempSymbol(N, "rcd")
      Begin(
        b,
        Assign(
          rcdSym,
          Record(mut = false, fsr.reverse),
          k((Arg(N, Value.Ref(rcdSym)) :: asr).reverse)))
      
  
  inline def plainArgs(ts: Ls[st])(k: Ls[Arg] => Block)(using Subst): Block =
    subTerms(ts)(asr => k(asr.map(Arg(N, _))))
  
  inline def subTerms(ts: Ls[st])(k: Ls[Path] => Block)(using Subst): Block =
    // @tailrec // TODO
    def rec(as: Ls[st], asr: Ls[Path]): Block = as match
      case Nil => k(asr.reverse)
      case a :: as =>
        subTerm_nonTail(a): ar =>
          rec(as, ar :: asr)
    rec(ts, Nil)
  
  def subTerm_nonTail(t: st, inStmtPos: Bool = false)(k: Path => Block)(using Subst): Block =
    subTerm(t: st, inStmtPos: Bool)(k)
  
  inline def subTerm(t: st, inStmtPos: Bool = false)(k: Path => Block)(using Subst): Block =
    term(t, inStmtPos = inStmtPos):
      case v: Value => k(v)
      case p: Path => k(p)
      case Lambda(params, body) =>
        val lamSym = BlockMemberSymbol("lambda", Nil, false)
        val lamDef = FunDefn(N, lamSym, params :: Nil, body)
        Define(lamDef, k(lamSym |> Value.Ref.apply))
      case r =>
        val l = new TempSymbol(N)
        Assign(l, r, k(l |> Value.Ref.apply))
  
  
  def program(main: st.Blk): Program =
    
    val (imps, funs, rest) = splitBlock(main.stats, Nil, Nil, Nil)
    
    val blk = block(funs ::: rest, R(main.res))(ImplctRet)(using Subst.empty)
    
    val desug = LambdaRewriter.desugar(blk)
    
    val handlerPaths = new HandlerPaths
    val stackSafe = config.stackSafety match
      case N => desug
      case S(sts) => StackSafeTransform(sts.stackLimit, handlerPaths).transformTopLevel(desug)
    val withHandlers = config.effectHandlers.fold(stackSafe): opt =>
      HandlerLowering(handlerPaths, opt).translateTopLevel(stackSafe)
    
    val flattened = withHandlers.flattened
    
    val lifted = 
      if lift then Lifter(S(handlerPaths)).transform(flattened)
      else flattened
    
    val res = MergeMatchArmTransformer.applyBlock(lifted)
    
    Program(
      imps.map(imp => imp.sym -> imp.file),
      res
    )
  
  
  def setupSelection(prefix: Term, nme: Tree.Ident, sym: Opt[FieldSymbol])(k: Result => Block)(using Subst): Block =
    subTerm(prefix): p =>
      val selRes = TempSymbol(N, "selRes")
      k(Select(p, nme)(sym))
  
  final def setupFunctionOrByNameDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
    val physicalParams = paramLists match
      case Nil => ParamList(ParamListFlags.empty, Nil, N) :: Nil
      case ps => ps
    setupFunctionDef(physicalParams, bodyTerm, name)
  
  def setupFunctionDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
    (paramLists, returnedTerm(bodyTerm))
  
  def reportAnnotations(target: Statement, annotations: Ls[Annot]): Unit =
    annotations.foreach:
      case Annot.Untyped => ()
      case annot => raise:
        WarningReport(msg"This annotation has no effect." -> annot.toLoc :: Nil)


trait LoweringSelSanityChecks(using Config, TL, Raise, State)
    extends Lowering:
  
  private val instrument: Bool = config.sanityChecks.isDefined
  
  override def setupSelection(prefix: st, nme: Tree.Ident, sym: Opt[FieldSymbol])(k: Result => Block)(using Subst): Block =
    if !instrument then return super.setupSelection(prefix, nme, sym)(k)
    subTerm(prefix): p =>
      val selRes = TempSymbol(N, "selRes")
      // * We are careful to access `x.f` before `x.f$__checkNotMethod` in case `x` is, eg, `undefined` and
      // * the access should throw an error like `TypeError: Cannot read property 'f' of undefined`.
      val b0 = blockBuilder
        .assign(selRes, Select(p, nme)(sym))
      (if sym.isDefined then
        // * If the symbol is known, the elaborator will have already checked the access [invariant:1]
        b0
      else b0
        .assign(TempSymbol(N, "discarded"), Select(p, Tree.Ident(nme.name+"$__checkNotMethod"))(N)))
        .ifthen(selRes.asPath,
          Case.Lit(syntax.Tree.UnitLit(false)),
          Throw(Instantiate(mut = false, Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Error"))(N),
            Value.Lit(syntax.Tree.StrLit(s"Access to required field '${nme.name}' yielded 'undefined'")).asArg :: Nil))
        )
        .rest(k(selRes.asPath))



trait LoweringTraceLog(instrument: Bool)(using TL, Raise, State)
    extends Lowering:
  
  private def selFromGlobalThis(path: Str*): Path =
      path.foldLeft[Path](Value.Ref(State.globalThisSymbol)):
        (qual, name) => Select(qual, Tree.Ident(name))(N)
    
  private def assignStmts(stmts: (Local, Result)*)(rest: Block) =
    stmts.foldRight(rest):
      case ((sym, res), acc) => Assign(sym, res, acc)
  
  private def pureCall(fn: Path, args: Ls[Arg]): Call =
    Call(fn, args)(true, false)
  
  extension (k: Block => Block)
    def |>: (b: Block): Block = k(b)

  private val traceLogFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("log")
  private val traceLogIndentFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("indent")
  private val traceLogResetFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("resetIndent")
  private val strConcatFn = selFromGlobalThis("String", "prototype", "concat", "call")
  private val inspectFn = selFromGlobalThis("util", "inspect")
  

  override def setupFunctionDef(paramLists: List[ParamList], bodyTerm: st, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
    if instrument then
      val (ps, bod) = handleMultipleParamLists(paramLists, bodyTerm)
      val instrumentedBody = setupFunctionBody(ps, bod, name)
      (ps :: Nil, instrumentedBody)
    else
      super.setupFunctionDef(paramLists, bodyTerm, name)

  def handleMultipleParamLists(paramLists: List[ParamList], bod: Term) =
    def go(paramLists: List[ParamList], bod: Term): (ParamList, Term) =
      paramLists match
        case Nil => ???
        case h :: Nil => (h, bod)
        case h :: t => go(t, Term.Lam(h, bod))
    go(paramLists.reverse, bod)
  
  def setupFunctionBody(params: ParamList, bod: Term, name: Option[Str])(using Subst): Block =
    val enterMsgSym = TempSymbol(N, dbgNme = "traceLogEnterMsg")
    val prevIndentLvlSym = TempSymbol(N, dbgNme = "traceLogPrevIndent")
    val resSym = TempSymbol(N, dbgNme = "traceLogRes")
    val retMsgSym = TempSymbol(N, dbgNme = "traceLogRetMsg")
    val psInspectedSyms = params.params.map(p => TempSymbol(N, dbgNme = s"traceLogParam_${p.sym.nme}") -> p.sym)
    val resInspectedSym = TempSymbol(N, dbgNme = "traceLogResInspected")
    
    val psSymArgs = psInspectedSyms.zipWithIndex.foldRight[Ls[Arg]](Arg(N, Value.Lit(Tree.StrLit(")"))) :: Nil):
      case (((s, p), i), acc) => if i == psInspectedSyms.length - 1
        then Arg(N, Value.Ref(s)) :: acc
        else Arg(N, Value.Ref(s)) :: Arg(N, Value.Lit(Tree.StrLit(", "))) :: acc
    
    assignStmts(psInspectedSyms.map: (pInspectedSym, pSym) =>
      pInspectedSym -> pureCall(inspectFn, Arg(N, Value.Ref(pSym)) :: Nil)
    *) |>:
    assignStmts(
      enterMsgSym -> pureCall(
        strConcatFn,
        Arg(N, Value.Lit(Tree.StrLit(s"CALL ${name.getOrElse("[arrow function]")}("))) :: psSymArgs
      ),
      TempSymbol(N) -> pureCall(traceLogFn, Arg(N, Value.Ref(enterMsgSym)) :: Nil),
      prevIndentLvlSym -> pureCall(traceLogIndentFn, Nil)
    ) |>: 
    term(bod)(r =>
    assignStmts(
      resSym -> r,
      resInspectedSym -> pureCall(inspectFn, Arg(N, Value.Ref(resSym)) :: Nil),
      retMsgSym -> pureCall(
        strConcatFn,
        Arg(N, Value.Lit(Tree.StrLit("=> "))) :: Arg(N, Value.Ref(resInspectedSym)) :: Nil
      ),
      TempSymbol(N) -> pureCall(traceLogResetFn, Arg(N, Value.Ref(prevIndentLvlSym)) :: Nil),
      TempSymbol(N) -> pureCall(traceLogFn, Arg(N, Value.Ref(retMsgSym)) :: Nil)
    ) |>:
      Ret(Value.Ref(resSym))
    )


object TrivialStatementsAndMatch:
  def unapply(b: Block): Opt[(Opt[Block => Block], Match)] =
    def handleAssignAndMatch(
      assign: Block => Block,
      m: Match,
      k: Opt[Block => Block]
    ): Some[(Some[Block => Block], Match)] =
      def newK(r: Block): Block =
        val newR = k.getOrElse(identity: Block => Block)(r)
        assign(newR)
      S(S(newK), m)
    
    b match
      case m: Match => S(N, m)
      case Assign(lhs, rhs: Path, TrivialStatementsAndMatch(k, m)) =>
        handleAssignAndMatch(r => Assign(lhs, rhs, r), m, k)
      case a@AssignField(lhs, nme, rhs: Path, TrivialStatementsAndMatch(k, m)) =>
        handleAssignAndMatch(r => AssignField(lhs, nme, rhs, r)(a.symbol), m, k)
      case AssignDynField(lhs, fld, arrayIdx, rhs: Path, TrivialStatementsAndMatch(k, m)) =>
        handleAssignAndMatch(r =>  AssignDynField(lhs, fld, arrayIdx, rhs, r), m, k)
      case Define(defn, TrivialStatementsAndMatch(k, m)) => 
        handleAssignAndMatch(r => Define(defn, r), m, k)
      case _ => N


object MergeMatchArmTransformer extends BlockTransformer(new SymbolSubst()):
  override def applyBlock(b: Block): Block = super.applyBlock(b) match
    case m@Match(scrut, arms, Some(dflt), rest) =>
      dflt match
        case TrivialStatementsAndMatch(k, Match(scrutRewritten, armsRewritten, dfltRewritten, restRewritten))
          if (scrutRewritten === scrut) && (restRewritten.size * armsRewritten.length) < 10 =>
            val newArms = restRewritten match
              case _: End => armsRewritten
              case _ => armsRewritten.map:
                case (cse, body) =>
                  cse -> Begin(body, restRewritten)
            k.getOrElse(identity: Block => Block)(Match(scrut, arms ::: newArms, dfltRewritten, rest))
        case _ => m
    case b => b
