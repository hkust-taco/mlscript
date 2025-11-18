package hkmc2
package codegen

import scala.language.implicitConversions
import scala.annotation.tailrec
import os.{Path as AbsPath, RelPath}
import sourcecode.Line

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import codegen.Instrumentation

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
class LoweringCtx(initMap: Map[Local, Value], val mayRet: Bool):
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
    case Value.Ref(l, _) => map.getOrElse(l, v)
    case _ => v
object LoweringCtx:
  val empty = LoweringCtx(Map.empty, false)
  def subst(using sub: LoweringCtx): LoweringCtx = sub
  def nestFunc(using sub: LoweringCtx): LoweringCtx = LoweringCtx(sub.map, true)
end LoweringCtx

import LoweringCtx.subst


class Lowering()(using Config, TL, Raise, State, Ctx):
  
  extension (t: Term)
    def instantiated = t match
      case r: Resolvable =>
        tl.trace[Term](s"Expanding term ${r}", post = t => s"~> ${t}"):
          r.expanded
      case t => t
  
  val lowerHandlers: Bool = config.effectHandlers.isDefined
  val lift: Bool = config.liftDefns.isDefined

  lazy val unreachableFn =
    Select(Value.Ref(State.runtimeSymbol), Tree.Ident("unreachable"))(N)
  
  def unit: Path =
    Select(Value.Ref(State.runtimeSymbol), Tree.Ident("Unit"))(S(State.unitSymbol))
  
  def fail(err: ErrorReport): Block =
    raise(err)
    End("error")
  
  
  // type Rcd = (mut: Bool, args: List[RcdArg]) // * Better, but Scala's patmat exhaustiveness chokes on it
  type Rcd = (Bool, List[RcdArg])
  
  def returnedTerm(t: st)(using LoweringCtx): Block = term(t)(Ret)(using LoweringCtx.nestFunc)
  
  def parentConstructor(cls: Term, args: Ls[Term])(using LoweringCtx) = 
    if args.length > 1 then 
      raise:
        ErrorReport(
          msg"Extending a class with multiple parameter lists is not supported" -> Loc(cls :: args) :: Nil,
          source = Diagnostic.Source.Compilation
        )
    lowerCall(
      Value.Ref(State.builtinOpsMap("super")),
      isMlsFun = true,
      isTailCall = false,
      args.headOption,
      N, // TODO: location?
    )(c => Return(c, implct = true))
  
  // * Used to work around Scala's @tailrec annotation for those few calls that are not in tail position.
  final def term_nonTail(t: st, inStmtPos: Bool = false)(k: Result => Block)(using LoweringCtx): Block =
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
  
  
  def block(stats: Ls[Statement], res: Rcd \/ Term)(k: Result => Block)(using LoweringCtx): Block =
    // TODO we should also isolate and reorder classes by inheritance topological sort
    val (imps, funs, rest) = splitBlock(stats, Nil, Nil, Nil)
    blockImpl(imps ::: funs ::: rest, res)(k)
  
  def blockImpl(stats: Ls[Statement], res: Rcd \/ Term)(k: Result => Block)(using LoweringCtx): Block =
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
    case (imp: Import) :: stats =>
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
                blockImpl(stats, res)(k)))(using LoweringCtx.nestFunc)
          case syntax.Fun =>
            val (paramLists, bodyBlock) = setupFunctionOrByNameDef(td.params, bod, S(td.sym.nme))
            Define(FunDefn(td.owner, td.sym, paramLists, bodyBlock)(td.extraAnnotations.contains(Annot.TailRec)),
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
        val bufferableAnnots = defn.annotations.flatMap:
          case Annot.Trm(trm: SynthSel) =>
            if trm.sym.contains(ctx.builtins.annotations.buffered) then
              S(false)
            else if trm.sym.contains(ctx.builtins.annotations.bufferable) then
              S(true)
            else
              N
          case _ => N
        if bufferableAnnots.length > 1 then
          raise(ErrorReport(
            msg"Only one of bufferable annotation is allowed." -> defn.toLoc :: Nil,
            source = Diagnostic.Source.Compilation
          ))
        if bufferableAnnots.length >= 1 then
          if defn.companion.isDefined then
            raise(ErrorReport(
              msg"No companion class is allowed with @buffered or @bufferable." -> defn.toLoc :: Nil,
              source = Diagnostic.Source.Compilation
            ))
        val bufferable = bufferableAnnots.headOption
        val (mtds, publicFlds, privateFlds, ctor) = defn match
          case pd: PatternDef =>
            // Compile the pattern definition into `unapply` and `unapplyStringPrefix`
            // methods using the `SplitCompiler`, which transliterate the pattern into
            // UCS splits that backtrack without any optimizations.
            val compiler = new ups.SplitCompiler
            val methods = compiler.compilePattern(pd)
            // We only need `owner`, `sym`, `params` and `body`
            val mtds = methods.map:
              case (sym, params, split) =>
                val paramLists = params :: Nil
                val bodyBlock = ucs.Normalization(this)(split)(Ret)
                FunDefn(N, sym, paramLists, bodyBlock)(false)
            // The return type is intended to be consistent with `gatherMembers`
            (mtds, Nil, Nil, End())
          case _ => gatherMembers(defn.body)
        val mod = defn.companion match
          case S(sym) =>
            sym.defn match
            case S(mod: ModuleOrObjectDef) =>
              reportAnnotations(mod, mod.extraAnnotations)
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
              bufferable,
            ),
            blockImpl(stats, res)(k))
        case S(ext) =>
          assert(k isnt syntax.Mod) // modules can't extend things and can't have super calls
          subTerm(ext.cls): clsp =>
            val pctor = parentConstructor(ext.cls, ext.args)
            Define(
              ClsLikeDefn(
                defn.owner, defn.sym, defn.bsym, defn.kind, defn.paramsOpt, defn.auxParams, S(clsp),
                mtds, privateFlds, publicFlds, pctor, ctor, mod, bufferable,
              ),
              blockImpl(stats, res)(k)
            )
      case td: TypeDef => // * Type definitions are erased
        blockImpl(stats, res)(k)
  
  
  def lowerCall(fr: Path, isMlsFun: Bool, isTailCall: Bool, arg: Opt[Term], loc: Opt[Loc])(k: Result => Block)(using LoweringCtx): Block =
    arg match
    case S(a) =>
      lowerCall(fr, isMlsFun, isTailCall, a, loc)(k)
    case N =>
      // * No arguments means a nullary call, e.g., `f()`
      k(Call(fr, Nil)(isMlsFun, true, isTailCall).withLoc(loc))
  def lowerCall(fr: Path, isMlsFun: Bool, isTailCall: Bool, arg: Term, loc: Opt[Loc])(k: Result => Block)(using LoweringCtx): Block =
    lowerArg(arg)(as => k(Call(fr, as)(isMlsFun, true, isTailCall).withLoc(loc)))
  
  def lowerArg(arg: Term)(k: Ls[Arg] => Block)(using LoweringCtx): Block =
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
  
  def ref(ref: st.Ref, annots: List[Annot], disamb: Opt[DefinitionSymbol[?]], inStmtPos: Bool)(k: Result => Block)(using LoweringCtx): Block =
    def warnStmt = if inStmtPos then
      raise:
        WarningReport(msg"Pure expression in statement position" -> ref.toLoc :: Nil, S(ref))
    
    val sym = ref.sym
    sym match
      case ctx.builtins.source.bms | ctx.builtins.js.bms | ctx.builtins.wasm.bms | ctx.builtins.debug.bms | ctx.builtins.annotations.bms =>
        return fail:
          ErrorReport(
            msg"Module '${sym.nme}' is virtual (i.e., \"compiler fiction\"); cannot be used directly" -> ref.toLoc ::
            Nil, S(ref), source = Diagnostic.Source.Compilation)
      case sym if sym.asCls.exists(ctx.builtins.virtualClasses) =>
        return fail:
          ErrorReport(
            msg"Symbol '${sym.nme}' is virtual (i.e., \"compiler fiction\"); cannot be used as a term" -> ref.toLoc ::
            Nil, S(ref), source = Diagnostic.Source.Compilation)
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
        val bod = st.App(ref, st.Tup(List(st.Ref(p1.sym)(t1, 666, N).resolve, st.Ref(p2.sym)(t2, 666, N).resolve))
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
        val bod = st.App(ref, st.Tup(List(st.Ref(p1.sym)(t1, 666, N).resolve))
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
      disamb.flatMap(_.defn) match
      case S(_) if bs.asCls.exists(_ is ctx.builtins.Int31) =>
        return term(Sel(State.runtimeSymbol.ref().resolve, ref.tree)(S(bs), N).withLocOf(ref).resolve)(k)
      case S(d) if d.hasDeclareModifier.isDefined =>
        return term(Sel(State.globalThisSymbol.ref().resolve, ref.tree)(S(bs), N).withLocOf(ref).resolve)(k)
      case S(td: TermDefinition) if td.k is syntax.Fun =>
        // * Local functions with no parameter lists are getters
        // * and are lowered to functions with an empty parameter list
        // * (non-local functions are compiled into getter methods selected on some prefix)
        if td.params.isEmpty then
          val l = new TempSymbol(S(ref))
          return Assign(l, Call(Value.Ref(bs, disamb).withLocOf(ref), Nil)(true, true, annots.contains(Annot.TailCall)), k(Value.Ref(l, disamb)))
      case S(_) => ()
      case N => () // TODO panic here; can only lower refs to elab'd symbols
    case _ => ()
    warnStmt
    k(subst(Value.Ref(sym, disamb).withLocOf(ref)))
  
  @tailrec
  final def term(t: st, inStmtPos: Bool = false)(k: Result => Block)(using LoweringCtx): Block =
    tl.log(s"Lowering.term ${t.showDbg.truncate(100, "[...]")}${
      if inStmtPos then " (in stmt)" else ""}${
      t.resolvedSym.fold("")(" – symbol " + _)}")
    
    def warnStmt = if inStmtPos then
      raise:
        WarningReport(msg"Pure expression in statement position" -> t.toLoc :: Nil, S(t))
    
    @tailrec
    def extractAnnots(t: st, acc: List[Annot]): (List[Annot], st) = t match
      case st.Annotated(annot, trm) => extractAnnots(trm.instantiated, annot :: acc)
      case _ => (acc, t)
    
    val insted = t.instantiated
    val (annots, trm) = extractAnnots(insted, Nil)
    reportAnnotations(trm, annots)
    
    trm match
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
    case t @ st.Ref(sym) =>
      ref(t, annots, N, inStmtPos)(k)
    case st.Resolved(t @ st.Ref(bsym), sym) =>
      ref(t, annots, S(sym), inStmtPos)(k)
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
          k(Call(Value.Ref(sym).withLocOf(ref), Arg(N, ar) :: Nil)(true, false, false))
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
            val lamDef = FunDefn(N, lamSym, PlainParamList(Nil) :: Nil, returnedTerm(arg2))(false)
            Define(
              lamDef,
              k(Call(
                Value.Ref(State.runtimeSymbol).selN(Tree.Ident(if isAnd then "short_and" else "short_or")),
                Arg(N, ar1) :: Arg(N, Value.Ref(lamSym, N)) :: Nil
              )(true, false, false)))
          else
            subTerm_nonTail(arg2): ar2 =>
              k(Call(Value.Ref(sym).withLocOf(ref), Arg(N, ar1) :: Arg(N, ar2) :: Nil)(true, false, false))
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
        case sym: sem.TermSymbol => sym.k is syntax.Fun
        // Do not perform safety check on `MatchSuccess` and `MatchFailure`.
        case sym => (sym is State.matchSuccessClsSymbol) ||
          (sym is State.matchFailureClsSymbol)
      def conclude(fr: Path) = lowerCall(fr, isMlsFun, annots.contains(Annot.TailCall), arg, t.toLoc)(k)
      
      val instantiated = f.instantiated
      val instantiatedResolvedBms = instantiated.resolvedSym.flatMap(_.asBlkMember)
      
      // * We have to instantiate `f` again because, if `f` is a Sel, the `term`
      // * function is not called again with f. See below `Sel` and `SelProj` cases.
      instantiated match
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitand) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("bitand")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitnot) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("bitnot")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitor) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("bitor")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.shl) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("shl")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.try_catch) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("try_catch")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.wasm.plus_impl) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("plus_impl")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.Int31) =>
        conclude(Value.Ref(State.runtimeSymbol).selN(Tree.Ident("Int31")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.debug.printStack) =>
        if !config.effectHandlers.exists(_.debug) then
          return fail:
            ErrorReport(
              msg"Debugging functions are not enabled" ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
        conclude(Value.Ref(State.runtimeSymbol).selSN("raisePrintStackEffect").withLocOf(f))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.debug.getLocals) =>
        if !config.effectHandlers.exists(_.debug) then
          return fail:
            ErrorReport(
              msg"Debugging functions are not enabled" ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
        conclude(Value.Ref(ctx.builtins.debug.getLocals, N).withLocOf(f))
      // * Due to whacky JS semantics, we need to make sure that selections leading to a call
      // * are preserved in the call and not moved to a temporary variable.
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(N).withLocOf(sel))
      case Resolved(sel @ Sel(prefix, nme), sym) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(S(sym)).withLocOf(sel))
      case sel @ SelProj(prefix, _, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(N).withLocOf(sel))
      case Resolved(sel @ SelProj(prefix, _, nme), sym) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(S(sym)).withLocOf(sel))
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
            reportAnnotations(td, td.annotations)
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
        val lamDef = FunDefn(N, lamSym, paramLists, bodyBlock)(false)
        Define(
          lamDef,
          k(Value.Ref(lamSym, N)))
    
    
    case iftrm: st.IfLike => ucs.Normalization(this)(iftrm)(k)
    
    case iftrm: st.SynthIf => ucs.Normalization(this)(iftrm)(k)
      
    case sel @ Sel(prefix, nme) =>
      setupSelection(prefix, nme, N)(k)
    case Resolved(sel @ Sel(prefix, nme), sym) =>
      setupSelection(prefix, nme, S(sym))(k)
    
    case sel @ SynthSel(prefix, nme) =>
      // * Not using `setupSelection` as these selections are not meant to be sanity-checked
      subTerm(prefix): p =>
        k(Select(p, nme)(N))
    case Resolved(sel @ SynthSel(prefix, nme), sym) =>
      // * Not using `setupSelection` as these selections are not meant to be sanity-checked
      subTerm(prefix): p =>
        k(Select(p, nme)(S(sym)))
    
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
                  Assign(ts, Call(inner, asr2)(true, true, false), acc(Value.Ref(ts)))
            val ts = TempSymbol(N)
            Assign(ts, Instantiate(mut, sr, asr), z(Value.Ref(ts)))
        case S((isym, rft)) =>
          val sym = new BlockMemberSymbol(isym.name, Nil)
          val (mtds, publicFlds, privateFlds, ctor) = gatherMembers(rft)
          val pctor = parentConstructor(cls, as)
          val clsDef = ClsLikeDefn(N, isym, sym, syntax.Cls, N, Nil, S(sr),
            mtds, privateFlds, publicFlds, pctor, ctor, N, N)
          val inner = new New(sym.ref().resolved(isym), Nil, N)(N)
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
      setupSelection(prefix, proj, N)(k)
    case Resolved(sp @ SelProj(prefix, _, proj), sym) =>
      setupSelection(prefix, proj, S(sym))(k)
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
  
  def setupTerm(name: Str, args: Ls[Path])(k: Result => Block)(using LoweringCtx): Block =
    k(Instantiate(mut = false, Value.Ref(State.termSymbol).selSN(name), args.map(_.asArg)))

  def setupQuotedKeyword(kw: Str): Path =
    Value.Ref(State.termSymbol).selSN("Keyword").selSN(kw)

  def setupSymbol(symbol: Local)(k: Result => Block)(using LoweringCtx): Block =
    k(Instantiate(mut = false, Value.Ref(State.termSymbol).selSN("Symbol"),
      Value.Lit(Tree.StrLit(symbol.nme)).asArg :: Nil))

  def quotePattern(p: FlatPattern)(k: Result => Block)(using LoweringCtx): Block = p match
    case FlatPattern.Lit(lit) => setupTerm("LitPattern", Value.Lit(lit) :: Nil)(k)
    case _ => // TODO
      fail:
        ErrorReport(
          msg"Unsupported quasiquote pattern type" ->
          p.toLoc :: Nil,
          source = Diagnostic.Source.Compilation
        )
  
  def quoteSplit(split: Split)(k: Result => Block)(using LoweringCtx): Block = split match
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

  def quote(t: st)(k: Result => Block)(using LoweringCtx): Block = t match
    case Lit(lit) =>
      setupTerm("Lit", Value.Lit(lit) :: Nil)(k)
    case Ref(sym) if Elaborator.binaryOps.contains(sym.nme) => // builtin symbols
      val l = new TempSymbol(N)
      setupTerm("Builtin", Value.Lit(Tree.StrLit(sym.nme)) :: Nil)(k)
    case Resolved(Ref(sym), disamb) =>
      k(Value.Ref(sym, S(disamb)))
    case Ref(sym) =>
      k(Value.Ref(sym, N))
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
      def rec(ps: Ls[LocalSymbol & NamedSymbol], ds: Ls[Path])(k: Result => Block)(using LoweringCtx): Block = ps match
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
    case IfLike(syntax.Keyword.`if`, split) => quoteSplit(split.getExpandedSplit): r =>
      val l = new TempSymbol(N)
      Assign(l, r, setupTerm("IfLike", setupQuotedKeyword("If") :: Value.Ref(l) :: Nil)(k))
    case Unquoted(body) => term(body)(k)
    case _ => fail:
      ErrorReport(
        msg"Unsupported quasiquote type ${t.describe}" ->
        t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation
      )
  
  def gatherMembers(clsBody: ObjBody)(using LoweringCtx)
  : (Ls[FunDefn], Ls[BlockMemberSymbol -> TermSymbol], Ls[TermSymbol], Block) =
    val mtds = clsBody.methods
      .flatMap: td =>
        td.body.map: bod =>
          val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
          reportAnnotations(td, td.extraAnnotations)
          FunDefn(td.owner, td.sym, paramLists, bodyBlock)(td.extraAnnotations.contains(Annot.TailRec))
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
  
  def args(elems: Ls[Elem])(k: Ls[Arg] => Block)(using LoweringCtx): Block =
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
      
  
  inline def plainArgs(ts: Ls[st])(k: Ls[Arg] => Block)(using LoweringCtx): Block =
    subTerms(ts)(asr => k(asr.map(Arg(N, _))))
  
  inline def subTerms(ts: Ls[st])(k: Ls[Path] => Block)(using LoweringCtx): Block =
    // @tailrec // TODO
    def rec(as: Ls[st], asr: Ls[Path]): Block = as match
      case Nil => k(asr.reverse)
      case a :: as =>
        subTerm_nonTail(a): ar =>
          rec(as, ar :: asr)
    rec(ts, Nil)
  
  def subTerm_nonTail(t: st, inStmtPos: Bool = false)(k: Path => Block)(using LoweringCtx): Block =
    subTerm(t: st, inStmtPos: Bool)(k)
  
  inline def subTerm(t: st, inStmtPos: Bool = false)(k: Path => Block)(using LoweringCtx): Block =
    term(t, inStmtPos = inStmtPos):
      case v: Value => k(v)
      case p: Path => k(p)
      case Lambda(params, body) =>
        val lamSym = BlockMemberSymbol("lambda", Nil, false)
        val lamDef = FunDefn(N, lamSym, params :: Nil, body)(false)
        Define(lamDef, k(Value.Ref(lamSym, N)))
      case r =>
        val l = new TempSymbol(N)
        Assign(l, r, k(l |> Value.Ref.apply))
  
  
  def program(main: st.Blk): Program =
    
    val (imps, funs, rest) = splitBlock(main.stats, Nil, Nil, Nil)
    
    val blk = block(funs ::: rest, R(main.res))(ImplctRet)(using LoweringCtx.empty)
    
    val desug = LambdaRewriter.desugar(blk)
    
    val handlerPaths = new HandlerPaths
    
    val (withHandlers, doUnwindPaths) = config.effectHandlers.fold((desug, Map.empty)): opt =>
      HandlerLowering(handlerPaths, opt).translateTopLevel(desug)
      
    val stackSafe = config.stackSafety match
      case N => withHandlers
      case S(sts) => StackSafeTransform(sts.stackLimit, handlerPaths, doUnwindPaths).transformTopLevel(withHandlers)
    
    val flattened = stackSafe.flattened
    
    val lifted = 
      if lift then Lifter(S(handlerPaths)).transform(flattened)
      else flattened
    
    val bufferable = BufferableTransform().transform(lifted)
    
    val merged = MergeMatchArmTransformer.applyBlock(bufferable)

    val res = 
      if config.stageCode then Instrumentation(using summon).applyBlock(merged)
      else merged
    
    Program(
      imps.map(imp => imp.sym -> imp.str),
      res
    )
  
  
  def setupSelection(prefix: Term, nme: Tree.Ident, disamb: Opt[DefinitionSymbol[?]])(k: Result => Block)(using LoweringCtx): Block =
    subTerm(prefix): p =>
      k(Select(p, nme)(disamb))
  
  final def setupFunctionOrByNameDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using LoweringCtx): (List[ParamList], Block) =
    val physicalParams = paramLists match
      case Nil => ParamList(ParamListFlags.empty, Nil, N) :: Nil
      case ps => ps
    setupFunctionDef(physicalParams, bodyTerm, name)
  
  def setupFunctionDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using LoweringCtx): (List[ParamList], Block) =
    (paramLists, returnedTerm(bodyTerm))
  
  def reportAnnotations(target: Statement, annotations: Ls[Annot]): Unit =
    def warn(annot: Annot, msg: Opt[Message] = N) = raise:
      msg match
        case S(value) => WarningReport(value -> annot.toLoc :: Nil)
        case N =>  WarningReport(msg"This annotation has no effect." -> annot.toLoc :: Nil)
    annotations.foreach:
      case Annot.Untyped => ()
      case a @ Annot.TailRec =>
        target match
          case TermDefinition(body = S(bod), k = syntax.Fun) => warn(a, S(msg"Tail call optimization is not yet implemented."))
          case TermDefinition(k = syntax.Fun) => warn(a, S(msg"Only functions with a body may be marked as @tailrec."))
          case _ => warn(a)
        
      case Annot.Modifier(syntax.Keyword("staged")) => ()
      case annot => warn(annot)

  def reportAnnotations(receiver: Term, annotations: Ls[Annot]): Unit =
    def warn(annot: Annot, msg: Opt[Message] = N) =
      val message = msg match
        case None => msg"This annotation is not supported on ${receiver.describe} terms."
        case Some(value) => value
      raise:
        WarningReport(
          msg"This annotation has no effect." -> annot.toLoc ::
          message -> receiver.toLoc :: Nil)
    
    annotations.foreach:
      case Annot.Untyped => ()
      case a @ Annot.TailCall => receiver match
        case st.App(Ref(_: BuiltinSymbol), _) => warn(a, S(msg"The @tailcall annotation has no effect on calls to built-in symbols."))
        case st.App(_, _) => warn(a, S(msg"Tail call optimization is not yet implemented."))
        case st.Resolved(_, defnSym) => defnSym.defn match
          case S(td: TermDefinition) if (td.k is syntax.Fun) && td.params.isEmpty => warn(a, S(msg"Tail call optimization is not yet implemented."))
          case _ => warn(a)
        case _ => warn(a)
      case annot => warn(annot)

trait LoweringSelSanityChecks(using Config, TL, Raise, State)
    extends Lowering:
  
  private val instrument: Bool = config.sanityChecks.isDefined
  
  override def setupSelection(prefix: st, nme: Tree.Ident, disamb: Opt[DefinitionSymbol[?]])(k: Result => Block)(using LoweringCtx): Block =
    if !instrument then return super.setupSelection(prefix, nme, disamb)(k)
    subTerm(prefix): p =>
      val selRes = TempSymbol(N, "selRes")
      // * We are careful to access `x.f` before `x.f$__checkNotMethod` in case `x` is, eg, `undefined` and
      // * the access should throw an error like `TypeError: Cannot read property 'f' of undefined`.
      val b0 = blockBuilder
        .assign(selRes, Select(p, nme)(disamb))
      (if disamb.isDefined then
        // * If the symbol is known, the resolver will have already checked the access [invariant:1]
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
    Call(fn, args)(true, false, false)
  
  extension (k: Block => Block)
    def |>: (b: Block): Block = k(b)

  private val traceLogFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("log")
  private val traceLogIndentFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("indent")
  private val traceLogResetFn = Value.Ref(State.runtimeSymbol).selSN("TraceLogger").selSN("resetIndent")
  private val strConcatFn = selFromGlobalThis("String", "prototype", "concat", "call")
  private val inspectFn = selFromGlobalThis("util", "inspect")
  

  override def setupFunctionDef(paramLists: List[ParamList], bodyTerm: st, name: Option[Str])
      (using LoweringCtx): (List[ParamList], Block) =
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
  
  def setupFunctionBody(params: ParamList, bod: Term, name: Option[Str])(using LoweringCtx): Block =
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
    )(using LoweringCtx.nestFunc)


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
