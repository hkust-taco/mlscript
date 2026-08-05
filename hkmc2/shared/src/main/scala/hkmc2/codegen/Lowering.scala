package hkmc2
package codegen

import scala.language.implicitConversions
import scala.annotation.tailrec
import os.{Path as AbsPath, RelPath}
import sourcecode.Line

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import codegen.ReflectionInstrumenter

import semantics.*, ucs.FlatPattern
import hkmc2.{semantics => sem}
import semantics.{Term => st}
import semantics.Term.{Throw => _, Label => _, Break => _, Continue => _, *}
import semantics.Elaborator.{State, Ctx, ctx}

import syntax.{Literal, Tree, SpreadKind}
import hkmc2.syntax.{Fun, Keyword, LetBind, MutVal}


abstract class TailOp extends (Result => Block)
object Ret extends TailOp:
  def apply(r: Result): Block = Return(r)
object ImplctRet extends TailOp:
  def apply(r: Result): Block =
    r match
    case Value.Lit(Tree.UnitLit(false)) => End()
    case _ => Return(r)
object Thrw extends TailOp:
  def apply(r: Result): Block = Throw(r)


class LoweringCtx(
  initMap: Map[ValueSymbol, Value], // No longer in meaningful use and could be removed if we don't find a use for it
  val mayRet: Bool, // For rewriting while loop into tail recursive function, represent whether an explicit return is legal in the current block
  private val definedSymsDuringLowering: collection.mutable.Set[ScopedSymbol] // used to create Scoped blocks
):
  val map = initMap
  def collectScopedSym(s: ScopedSymbol) = definedSymsDuringLowering.add(s)
  def collectScopedSyms(s: ScopedSymbol*) = definedSymsDuringLowering.addAll(s)
  def registerTempSymbol(trm: Option[Term], dbgNme: Str = "tmp")(using State) =
    val tmp = new TempSymbol(trm, dbgNme)
    definedSymsDuringLowering.add(tmp)
    tmp
  def getCollectedSym: collection.Set[ScopedSymbol] = definedSymsDuringLowering
  /*
  def +(kv: (Symbol, Value)): Subst =
    kv match
    case (ns: NamedSymbol, Value.SimpleRef(ts: TempSymbol)) =>
      ts.nameHints += ns.name
    case _ =>
    Subst(map + kv)
  */
  def apply(v: Value): Value = v match
    case Value.SimpleRef(l) => map.getOrElse(l, v)
    case _ => v
object LoweringCtx:
  def loweringCtx(using sub: LoweringCtx): LoweringCtx = sub
  def empty =
    LoweringCtx(Map.empty, mayRet = false, collection.mutable.Set.empty)
  def nestFunc(using sub: LoweringCtx): LoweringCtx =
    LoweringCtx(sub.map, mayRet = true, sub.definedSymsDuringLowering)
  def nestScoped(using sub: LoweringCtx): LoweringCtx =
    LoweringCtx(sub.map, sub.mayRet, collection.mutable.Set.empty)
end LoweringCtx

import LoweringCtx.loweringCtx


object Lowering:
  
  def compError: Block =
    Throw(Value.Lit(Tree.StrLit("This code cannot be run as its compilation yielded an error.")))
  
  def fail(err: ErrorReport)(using Raise): Block =
    raise(err)
    compError
  
import Lowering.*

class Lowering()(using Config, TL, Raise, State, Ctx, SymbolPrinter):
  
  extension (t: Term)
    def instantiated = t match
      case r: Resolvable =>
        tl.trace[Term](s"Expanding term ${r}", post = t => s"~> ${t}"):
          r.expanded
      case t => t
  
  val lowerHandlers: Bool = config.effectHandlers.isDefined

  private lazy val wasmBinaryIntrinsicMap: Map[Str, Str] = Map(
    "+" -> "plus_impl",
    "-" -> "minus_impl",
    "*" -> "times_impl",
    "/" -> "div_impl",
    "%" -> "mod_impl",
    "===" -> "eq_impl",
    "!==" -> "neq_impl",
    "<" -> "lt_impl",
    "<=" -> "le_impl",
    ">" -> "gt_impl",
    ">=" -> "ge_impl"
  )
  private lazy val wasmUnaryIntrinsicMap: Map[Str, Str] = Map(
    "-" -> "neg_impl",
    "+" -> "pos_impl",
    "!" -> "not_impl"
  )
  private def wasmIntrinsicPath(sym: BuiltinSymbol, unary: Bool): Opt[Path] =
    if config.target is CompilationTarget.Wasm then
      val map = if unary then wasmUnaryIntrinsicMap else wasmBinaryIntrinsicMap
      map.get(sym.nme).map(name => State.wasmSymbol.asSimpleRef.selN(Tree.Ident(name)))
    else N
  private lazy val wasmIntrinsicSymbols: Set[BlockMemberSymbol] = Set(
    ctx.builtins.wasm.plus_impl,
    ctx.builtins.wasm.minus_impl,
    ctx.builtins.wasm.times_impl,
    ctx.builtins.wasm.div_impl,
    ctx.builtins.wasm.mod_impl,
    ctx.builtins.wasm.eq_impl,
    ctx.builtins.wasm.neq_impl,
    ctx.builtins.wasm.lt_impl,
    ctx.builtins.wasm.le_impl,
    ctx.builtins.wasm.gt_impl,
    ctx.builtins.wasm.ge_impl,
    ctx.builtins.wasm.neg_impl,
    ctx.builtins.wasm.pos_impl,
    ctx.builtins.wasm.not_impl
  )

  lazy val unreachableFn =
    Select(State.runtimeSymbol.asSimpleRef, Tree.Ident("unreachable"))(S(State.unreachableSymbol))(false)
  
  def unit: Path =
    Select(State.runtimeSymbol.asSimpleRef, Tree.Ident("Unit"))(S(State.unitSymbol))(false)
  
  private def memberIdent(nme: Tree.Ident, sym: Opt[MemberSymbol]): Tree.Ident =
    sym match
    case S(sym) =>
      new Tree.Ident(sym.nme).withLocOf(nme)
    case N =>
      symbolicSuffixBase(nme.name) match
      case S(base) =>
        new Tree.Ident(base).withLocOf(nme)
      case N =>
        nme

  private def definitionIdent(nme: Tree.Ident, sym: DefinitionSymbol[?]): Tree.Ident =
    new Tree.Ident(sym.nme).withLocOf(nme)

  // type Rcd = (mut: Bool, args: List[RcdArg]) // * Better, but Scala's patmat exhaustiveness chokes on it
  type Rcd = (Bool, List[RcdArg])
  
  def returnedTerm(t: st)(using LoweringCtx): Block = term(t)(Ret)(using LoweringCtx.nestFunc)
  
  def parentConstructor(parentClsPath: Path, cls: Term, args: Ls[Term])(using LoweringCtx) =
    lowerSuperCtorCall(
      parentClsPath,
      State.builtinOpsMap("super").asSimpleRef,
      isMlsFun = true,
      args,
      N, // TODO: location?
    )(c => Assign(NoSymbol, c, End()))
  
  // * Used to work around Scala's @tailrec annotation for those few calls that are not in tail position.
  final def term_nonTail(t: st, inStmtPos: Bool = false)(k: Result => Block)(using LoweringCtx): Block =
    term(t, inStmtPos = inStmtPos)(k)
  

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
  
  
  def block(stats: Ls[Statement], res: Rcd \/ Term, inStmtPos: Bool = false)
        (k: Result => Block)(using LoweringCtx): Block =
    // TODO we should also isolate and reorder classes by inheritance topological sort
    val (imps, funs, rest) = splitBlock(stats, Nil, Nil, Nil)
    
    def blockImpl(stats: Ls[Statement], res: Rcd \/ Term)(using LoweringCtx): Block =
      stats match
      case (t: sem.Term) :: stats =>
        term(t, inStmtPos = true)(Assign.discard(_, blockImpl(stats, res)))
      case Nil =>
        res match
        case R(res) => term(res, inStmtPos = inStmtPos)(k)
        case L((mut, flds)) =>
          k(Record(mut, flds.reverse))
      case RcdSpread(bod) :: stats =>
        res match
        case R(_) => wat("RcdField in non-Rcd context", res)
        case L((mut, flds)) =>
          subTerm(bod): l =>
            blockImpl(stats, L((mut, RcdArg(N, l) :: flds)))
      case RcdField(lhs, rhs) :: stats =>
        res match
        case R(_) => wat("RcdField in non-Rcd context", res)
        case L((mut, flds)) =>
          subTerm(lhs): l =>
            subTerm_nonTail(rhs): r =>
              blockImpl(stats, L((mut, RcdArg(S(l), r) :: flds)))
      case (decl @ LetDecl(sym, annotations)) :: stats =>
        reportAnnotations(decl, annotations)
        if sym.asTrm.forall(_.owner.isEmpty) then
          sym match
          case sym: ScopedSymbol => loweringCtx.collectScopedSym(sym)
          case sym => lastWords(s"tried to collect non-scoped local symbol ${sym.showDbg}")
        blockImpl(stats, res)
      case DefineVar(sym, rhs) :: stats =>
        term(rhs): r =>
          defineSymbol(sym, r, blockImpl(stats, res))
      case (_: SetConfig) :: stats =>
        // Config changes are handled at the program level; skip during block lowering
        blockImpl(stats, res)
      case (imp: Import) :: stats =>
        raise(ErrorReport(
          msg"Imports must be at the top level" ->
          imp.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        blockImpl(stats, res)
      case (d: Declaration) :: stats =>
        d match
        case td: TermDefinition =>
          reportAnnotations(td, td.extraAnnotations)
          if td.owner.isEmpty && td.hasDeclareModifier.isEmpty then
            loweringCtx.collectScopedSym(td.sym)
          td.body match
          case N => // abstract declarations have no lowering
            blockImpl(stats, res)
          case S(bod) =>
            td.k match
            case knd: syntax.Val =>
              assert(td.params.isEmpty)
              val cfgOverride = td.extraAnnotations.collectFirst:
                case Annot.Config(modify) => modify(config)
              subTerm_nonTail(bod)(r =>
                // Assign(td.sym, r,
                //   term(st.Blk(stats, res))(k)))
                Define(ValDefn(td.tsym, td.sym, r)(cfgOverride, td.annotations),
                  blockImpl(stats, res)))(using LoweringCtx.nestFunc)
            case syntax.Fun =>
              val (paramLists, bodyBlock) = setupFunctionOrByNameDef(td.params, bod, S(td.sym.nme))
              val cfgOverride = td.extraAnnotations.collectFirst:
                case Annot.Config(modify) => modify(config)
              Define(FunDefn(td.owner, td.sym, td.tsym, paramLists, bodyBlock)(cfgOverride, td.annotations),
                blockImpl(stats, res))
            case syntax.LetBind | syntax.HandlerBind => fail:
              ErrorReport(
                msg"Unexpected declaration kind '${td.k.str}' in lowering" -> td.toLoc :: Nil,
                source = Diagnostic.Source.Compilation)
        case cls: ClassLikeDef if cls.sym.defn.exists(_.hasDeclareModifier.isDefined) =>
          // * Declarations have no lowering
          blockImpl(stats, res)
        case cls: ClassDef if cls.moduleCompanion.isDefined =>
          // * Class definitions are pure, but their companions might not be,
          // * as they may contain static initialization code;
          // * therefore, we lower classes at the point where the companion is defined,
          // * if it is defined, rather than at the point where the class is defined.
          reportAnnotations(cls, cls.extraAnnotations)
          blockImpl(stats, res)
        case _defn: ClassLikeDef =>
          if _defn.owner.isEmpty then loweringCtx.collectScopedSym(_defn.bsym)
          val defn = _defn match
            case cls: ClassDef => cls
            case mod: ModuleOrObjectDef if mod.kind is syntax.Mod => // * Currently, both objects and modules are represented as `ModuleOrObjectDef`s
              mod.classCompanion match
              case S(comp) => comp.defn.getOrElse(wat("Module companion without definition", mod.companion))
              case N =>
                val stagedAnnots = mod.annotations.collect: 
                  case Annot.Modifier(Keyword.`staged`) => Annot.Modifier(Keyword.`staged`) 
                ClassDef.Plain(mod.owner, syntax.Cls, new ClassSymbol(Tree.DummyTypeDef(syntax.Cls), mod.sym.id),
                  mod.bsym,
                  Nil,
                  N,
                  ObjBody(Blk(Nil, UnitVal())),
                  S(mod.sym),
                  stagedAnnots,
                  Nil,
                  N,
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
          // Forbid @buffered classes from having a main parameter list
          bufferable.foreach: isBufferable =>
            if !isBufferable && defn.paramsOpt.isDefined then
              raise(ErrorReport(
                msg"Buffered classes must not have a main parameter list; use `constructor(...)` syntax instead." -> defn.toLoc :: Nil,
                source = Diagnostic.Source.Compilation
              ))
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
                  val bodyBlock = inScopedBlock(ucs.Normalization(this)(split)(Ret))
                  FunDefn.withFreshSymbol(N, sym, paramLists, bodyBlock)(configOverride = N, annotations = Nil)
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
                S(ClsLikeBody(mod.sym, mtds, privateFlds, publicFlds, ctor, mod.annotations))
              case _ => N
            case _ => N
          defn.ext match
          case N =>
            val cfgOverride = defn.extraAnnotations.collectFirst:
              case Annot.Config(modify) => modify(config)
            Define(
              ClsLikeDefn(defn.owner, defn.sym, defn.bsym, defn.ctorSym, defn.kind, defn.paramsOpt, defn.auxParams, N,
                mtds,
                privateFlds,
                publicFlds,
                End(),
                ctor,
                mod,
                bufferable,
              )(cfgOverride, defn.annotations),
              blockImpl(stats, res))
          case S(ext) =>
            assert(k isnt syntax.Mod) // modules can't extend things and can't have super calls
            val cfgOverride = defn.extraAnnotations.collectFirst:
              case Annot.Config(modify) => modify(config)
            subTerm(ext.cls): clsp =>
              val pctor = inScopedBlock(parentConstructor(clsp, ext.cls, ext.args))
              Define(
                ClsLikeDefn(
                  defn.owner, defn.sym, defn.bsym, defn.ctorSym, defn.kind, defn.paramsOpt, defn.auxParams, S(clsp),
                  mtds, privateFlds, publicFlds, pctor, ctor, mod, bufferable,
                )(cfgOverride, defn.annotations),
                blockImpl(stats, res)
              )
        case td: TypeDef => // * Type definitions are erased
          blockImpl(stats, res)
    
    blockImpl(imps ::: funs ::: rest, res)
  
  def getClassParamLists(cls: Path): Ls[ParamList] =
    cls.targetSymbol match
    case S(clsSym: ClassSymbol) =>
      clsSym.defn.map(clsDef => clsDef.paramsOpt.toList ::: clsDef.auxParams).getOrElse(Nil)
    case _ => Nil
  
  // * Lowers the `super(...)(...)` call we get from the `extends C(...)(...)` syntax
  def lowerSuperCtorCall(parentClsPth: Path, fr: Path, isMlsFun: Bool, args: List[Term], loc: Opt[Loc])(k: Result => Block)(using LoweringCtx): Block =
    val ctorParamLists = getClassParamLists(parentClsPth)
    args match
    case _ :: _ =>
      def zipArgs(remainingParamss: Ls[ParamList], args: Ls[Term], acc: Ls[Ls[Arg]]): Block = (remainingParamss, args) match
        case (_ :: remainingParamss2, arg :: remainingArgs) => lowerArgs(arg): as =>
          zipArgs(remainingParamss2, remainingArgs, as ne_:: acc)
        case (Nil, arg :: remainingArgs) =>
          if remainingArgs.isEmpty then
            raise(ErrorReport(
              msg"Too many parameter lists for parent class" -> loc :: Nil,
              source = Diagnostic.Source.Compilation))
          lowerArgs(arg): as =>
            zipArgs(Nil, remainingArgs, as ne_:: acc)
        case (remainingParamss2, Nil) =>
          if !remainingParamss2.isEmpty then
            raise(ErrorReport(
              msg"Extending a partially applied class is not supported" -> loc :: Nil,
              source = Diagnostic.Source.Compilation))
          k(Call(fr, acc.reverse.ne_!)(CallMetadata(isMlsFun, true, Nil)).withLoc(loc))
      zipArgs(ctorParamLists, args, Nil)
    case Nil =>
      if !ctorParamLists.isEmpty then
        raise(ErrorReport(
          msg"Extending a partially applied class is not supported" -> loc :: Nil,
          source = Diagnostic.Source.Compilation))
      // * No arguments to a super ctor means a nullary call, e.g., `extends C` means `extends C()`
      k(Call(fr, Nil ne_:: Nil)(CallMetadata(isMlsFun, true, Nil)).withLoc(loc))
  
  /** Lower a call with multiple argument lists into `Call` nodes,
    * trying to group as many as possible into a single one
    * when they correspond to parameter lists of the same callee. */
  def lowerMultiCall(fr: Path, isMlsFun: Bool, annotations: Ls[Annot], args: Ls[Term], loc: Opt[Loc])(k: Result => Block)(using LoweringCtx): Block =
    def zipArgs(remainingParamss: Ls[ParamList], remainingArgss: Ls[Term], acc: Ls[Ls[Arg]], mayRaiseEffects: Bool): Block =
      (remainingParamss, remainingArgss) match
      case (ps :: remainingParams, args :: remainingArgs) =>
        lowerArgs(args)(as => zipArgs(remainingParams, remainingArgs, as :: acc, mayRaiseEffects))
      case (Nil, Nil) =>
        k(Call(fr, acc.reverse.ne_!)(CallMetadata(isMlsFun, mayRaiseEffects, annotations)).withLoc(loc))
      case (Nil, args :: remainingArgss) =>
        acc.reverse match
        case Nil => lowerRemainingCalls(fr, args, remainingArgss, annotations, loc)(k)
        case acc: NELs[Ls[Arg]] =>
          val tmp = loweringCtx.registerTempSymbol(N, "baseCall")
          val call = Call(fr, acc)(CallMetadata(isMlsFun, mayRaiseEffects, Nil)).withLoc(loc)
          Assign(tmp, call, lowerRemainingCalls(tmp.asSimpleRef, args, remainingArgss, annotations, loc)(k))
      case (_ :: _, Nil) =>
        k(Call(fr, acc.reverse.ne_!)(CallMetadata(isMlsFun, mayRaiseEffects, annotations)).withLoc(loc))
    fr.targetSymbol match
    case S(fs: TermSymbol) =>
      fs.defn match
      case S(td: TermDefinition) =>
        zipArgs(td.params, args, Nil, fs.mayRaiseEffects)
      case _ => zipArgs(Nil, args, Nil, fs.mayRaiseEffects)
    case _ => zipArgs(Nil, args, Nil, true)
  
  def lowerRemainingCalls(base: Path, args: Term, remainingArgss: Ls[Term], annotations: Ls[Annot], loc: Opt[Loc])
        (k: Result => Block)(using LoweringCtx): Block =
    lowerArgs(args): as =>
      val call = Call(base, as ne_:: Nil)(CallMetadata(false, true, annotations)).withLoc(loc)
      remainingArgss match
      case Nil => k(call)
      case args :: remainingArgss =>
        val tmp = loweringCtx.registerTempSymbol(N, "callPrefix")
        Assign(tmp, call,
          lowerRemainingCalls(tmp.asSimpleRef, args, remainingArgss, annotations, loc)(k))
  
  /** Lower an instantiation with multiple argument lists into `Instantiate` and `Call` nodes,
    * trying to group as many as possible into a single `Instantiate`
    * when they correspond to constructor parameter lists of the same class.
    * If fewer argument lists are provided than constructor parameter lists, eta-expands
    * the missing ones with fresh lambdas (avoiding reliance on mutable JS class curry semantics). */
  def lowerMultiInstantiate(mut: Bool, cls: Path, args: Ls[Term], annotations: Ls[Annot])(k: Result => Block)(using LoweringCtx): Block =
    // Nullary instantiations are represented with one empty argument list, matching existing `Instantiate` usage.
    def buildInstantiate(argss: Ls[Ls[Arg]]): Instantiate =
      Instantiate(mut, cls, if argss.isEmpty then Nil :: Nil else argss)(InstantiateMetadata(annotations))
    // * Zip constructor param lists with argument lists, accumulating lowered args.
    // * Consumes one argument list per constructor param list; when all ctor params are
    // * consumed but extra args remain, falls back to `Call` nodes on the result.
    // * When args run out before ctor params are consumed, eta-expands the remaining ones.
    def zipArgs(remainingCtorParamss: Ls[ParamList], remainingArgss: Ls[Term], acc: Ls[Ls[Arg]]): Block =
      (remainingCtorParamss, remainingArgss) match
      case (ps :: remainingParams, args :: remainingArgs) =>
        lowerArgs(args)(as => zipArgs(remainingParams, remainingArgs, as :: acc))
      case (Nil, Nil) =>
        k(buildInstantiate(acc.reverse))
      case (Nil, args :: remainingArgss) =>
        val tmp = loweringCtx.registerTempSymbol(N, "baseInst")
        Assign(tmp, buildInstantiate(acc.reverse),
          lowerRemainingCalls(tmp.asSimpleRef, args, remainingArgss, annotations, N)(k))
      case (remainingParamss, Nil) =>
        // * Eta-expand missing argument lists by creating lambdas for each remaining param list.
        // * This makes partial `new C(args...)` explicit instead of relying on the JS class curry.
        def etaExpand(remainingParamss: Ls[ParamList], accArgss: Ls[Ls[Arg]]): Result =
          remainingParamss match
          case Nil => buildInstantiate(accArgss)
          case ps :: rest =>
            val freshSyms = ps.params.map(p => new VarSymbol(new Tree.Ident(p.sym.nme)))
            softTODO(ps.restParam.isEmpty, "Eta expanding rest parameters in constructor definitions is not yet supported")
            val freshParams = (ps.params zip freshSyms).map((p, s) => Param(p.flags, s, N, p.modulefulness))
            val freshParamList = ParamList(ps.flags, freshParams, N)
            val freshArgs = freshSyms.map(s => Arg(N, s.asSimpleRef))
            Lambda(freshParamList, Return(etaExpand(rest, accArgss :+ freshArgs)))(Nil)
        k(etaExpand(remainingParamss, acc.reverse))
    // * Resolve the class definition to get the constructor param lists.
    // * The class path typically resolves to a TermSymbol (the constructor function),
    // * so we also look up the owner InnerSymbol via TermDefinition#owner.
    // * Note: apparently, this can also be accessed through TermDefinition#companionClass
    // * (what Copilot initially used), which is weird.
    val ctorParamLists = getClassParamLists(cls)
    if ctorParamLists.isEmpty then
      // * Need to specially handle no-param classes
      args match
      case Nil =>
        k(buildInstantiate(Nil))
      case args :: remainingArgss =>
        lowerArgs(args): as =>
          remainingArgss match
          case Nil =>
            k(buildInstantiate(as :: Nil))
          case remainingArgss =>
            val tmp = loweringCtx.registerTempSymbol(N, "baseInst")
            Assign(tmp, buildInstantiate(as :: Nil),
              lowerRemainingCalls(tmp.asSimpleRef, remainingArgss.head, remainingArgss.tail, annotations, N)(k))
    else zipArgs(ctorParamLists, args, Nil)
  
  def lowerArgs(arg: Term)(k: Ls[Arg] => Block)(using LoweringCtx): Block =
    arg match
    case Tup(fs) =>
      if fs.exists(e => e match
        case Spd(SpreadKind.Lazy, _) => true // is lazy spread
        case _ => false)
      then
        raise(ErrorReport(
          msg"Lazy spreads are not supported in call arguments" -> arg.toLoc :: Nil, S(arg),
          source = Diagnostic.Source.Compilation))
      args(fs)(as => k(as))
    case _ =>
      // Application arguments that are not tuples represent spreads, as in `f(...arg)`
      subTerm_nonTail(arg): ar =>
        k(Arg(spread = S(SpreadKind.Eager), ar) :: Nil)
  
  def warnPureExprInStmtPos(loc: Opt[Loc], extraInfo: => Opt[Any] = N)(using Line): Unit =
    raise:
      WarningReport(msg"Pure expression in statement position" -> loc :: Nil, extraInfo,
        source = Diagnostic.Source.Compilation)

  private def assignSymbol(target: Symbol, diagnostic: Symbol, rhs: Result, rest: Block, loco: Opt[Loc])(using LoweringCtx): Block =
    def nope = fail:
      ErrorReport(
        msg"Cannot assign to ${diagnostic match
            case sym: BlockMemberSymbol => sym.describe
            case sym => "symbol"
          } '${diagnostic.nme}'" -> loco
          :: diagnostic.toLoc.match
            case s @ S(_) => msg"Defined here:" -> s :: Nil
            case N => Nil,
        source = Diagnostic.Source.Compilation,
        extraInfo = S(target.getClass))
    target match
    case sym: TermSymbol if (sym.k is MutVal) || (sym.k is LetBind) =>
      sym.owner match
      case S(owner) => AssignField(owner.asThis, sym.id, rhs, rest)(S(sym))
      case N => nope
    case sym: LocalVarSymbol => Assign(sym, rhs, rest)
    case sym => nope
  
  private def defineSymbol(sym: Symbol, rhs: Result, rest: Block)(using LoweringCtx): Block =
    sym match
    case sym: TermSymbol =>
      sym.owner match
      case S(owner) => AssignField(owner.asThis, sym.id, rhs, rest)(S(sym))
      case N => lastWords(s"tried to define top-level symbol ${sym.showDbg} in a local scope")
    case sym: LocalVarSymbol =>
      Assign(sym, rhs, rest)
    case sym =>
      lastWords(s"tried to define non-variable symbol ${sym.showDbg}")
  
  private def isImplicitNullaryCall(defnSym: DefinitionSymbol[?]): Bool =
    defnSym.defn.exists:
      case td: TermDefinition => (td.k is syntax.Fun) && td.params.isEmpty
      case _ => false
  
  def ref(ref: st.Ref, annots: List[Annot], disamb: Opt[DefinitionSymbol[?]], inStmtPos: Bool)(k: Result => Block)(using LoweringCtx): Block =
    def warnStmt = if inStmtPos then warnPureExprInStmtPos(ref.toLoc, S(ref))
    
    val sym = ref.sym
    sym match
      case
          ctx.builtins.source.bms
        | ctx.builtins.js.bms
        | ctx.builtins.wasm.bms
        | ctx.builtins.debug.bms
        | ctx.builtins.annotations.bms
      =>
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
        return k(Lambda(paramLists.head, bodyBlock)(Nil).withLocOf(ref))
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
        return k(Lambda(paramLists.head, bodyBlock)(Nil).withLocOf(ref))
    case bs: BlockMemberSymbol =>
      disamb.flatMap(_.defn) match
      case S(d) if d.hasDeclareModifier.isDefined =>
        val sel = SynthSel(State.globalThisSymbol.ref().resolve, ref.tree)(S(bs), FlowSymbol.synthSel(ref.tree.name), N, N).withLocOf(ref).resolve
        return disamb.fold(term(sel)(k))(d => term(st.Resolved(sel, d)(N))(k))
        // * Note: the alternative below, which might seem more appealing,
        // * works but does not instrument the selection to check for `undefined`!
        // return k(Value.Ref(State.globalThisSymbol).sel(ref.tree, bs).withLocOf(ref))
      case S(td: TermDefinition) if isImplicitNullaryCall(td.tsym) =>
        // * Functions defined in local scopes with no parameter lists are getters
        // * and are lowered to functions with an empty parameter list
        // * (non-local functions are compiled into getter methods selected on some prefix)
        if isImplicitNullaryCall(td.tsym) then
          return k(Call(
              bs.asMemberRef(disamb.get).withLocOf(ref), Nil ne_:: Nil
            )(CallMetadata(isMlsFun = true, mayRaiseEffects = true, annots)))
      case S(td: TermDefinition) =>
        td.tsym.owner match
        case S(owner) =>
          // * With the current Elaborator semantics, selections are already inserted for most things;
          // * the current case can only happen if `td` is a let binding defined in some object owner.
          softAssert(td.k is syntax.LetBind, s"Expected a let binding, got a ${td.k.str} ($td)")
          return k(Select(owner.asThis, td.tsym.id)(S(td.tsym))(false).withLocOf(ref))
        case N => ()
      case S(_) => ()
      case N => () // TODO panic here; can only lower refs to elab'd symbols
    case sym: TermSymbol =>
      sym.owner match
      case S(owner) =>
        warnStmt
        val sel = Select(owner.asThis, sym.id)(S(sym))(false)
        return k(sel.withLocOf(ref))
      case N => ()
    case _ => ()
    warnStmt
    (sym, disamb) match
      case (sym: SimpleSymbol, _) =>
        k(loweringCtx(sym.asSimpleRef.withLocOf(ref)))
      case (sym: BlockMemberSymbol, _) =>
        k(loweringCtx(sym.asMemberRef(disamb.orElse(sym.asPrincipal).get).withLocOf(ref)))
      case (sym: InnerSymbol, _) =>
        k(loweringCtx(sym.asThis.withLocOf(ref)))
      case (sym, disamb) =>
        lastWords(s"Unexpected symbol kind ${sym.getClass.getSimpleName}: $sym")
  
  @tailrec
  final def term(t: st, inStmtPos: Bool = false)(k: Result => Block)(using LoweringCtx): Block =
    tl.log(s"Lowering.term ${t.showDbg.truncate(100, "[...]")}${
      if inStmtPos then " (in stmt)" else ""}${
      t.resolvedSym.fold("")(" – symbol " + _)}")
    
    def warnStmt = if inStmtPos then warnPureExprInStmtPos(t.toLoc, S(t))
    
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
      if lit =/= Tree.UnitLit(false) then warnStmt
      k(Value.Lit(lit))
    case st.Ret(res) =>
      returnedTerm(res)
    case st.Throw(res) =>
      term(res)(Thrw)
    case st.Label(label, result, body, hasNonLocalContinueDispatch) =>
      def hasLocalContinue(term: st): Bool = term match
        case st.Continue(`label`) => true
        case _ => term.subTerms.iterator.exists(hasLocalContinue)
      loweringCtx.collectScopedSym(result)
      val bodyBlock =
        if !hasNonLocalContinueDispatch then
          term_nonTail(body)(r => Assign(result, r, Break(label)))
        else
          val bodyResult = loweringCtx.registerTempSymbol(N, "labelBodyResult")
          val isContinue = loweringCtx.registerTempSymbol(N, "labelContinueDispatch")
          term_nonTail(body): r =>
            Assign(
              bodyResult,
              r,
              Assign(
                isContinue,
                Call(
                  State.builtinOpsMap("===").asSimpleRef,
                  (bodyResult.asSimpleRef.asArg :: State.runtimeSymbol.asSimpleRef.selSN("Continue").asArg :: Nil) ne_:: Nil,
                )(CallMetadata.defaultMlsFun),
                Match(
                  isContinue.asSimpleRef,
                  (Case.Lit(Tree.BoolLit(true)) -> Continue(label)) :: Nil,
                  S(Assign(result, bodyResult.asSimpleRef, Break(label))),
                  End("label continue-sentinel dispatch")
                )
              )
            )
      Label(
        label,
        loop = hasLocalContinue(body),
        bodyBlock,
        k(result.asSimpleRef)
      )
    case st.Break(label, result, value) =>
      value match
        case S(v) => term(v)(r => Assign(result, r, Break(label)))
        case N => Assign(result, Value.Lit(Tree.UnitLit(false)), Break(label))
    case st.Continue(label) =>
      Continue(label)
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
      ref(t, annots, N, inStmtPos = inStmtPos)(k)
    case st.Resolved(t @ st.Ref(bsym), sym) =>
      ref(t, annots, S(sym), inStmtPos = inStmtPos)(k)
    case st.App(ref @ Ref(sym: BuiltinSymbol), arg) =>
      arg match
      case st.Tup(Nil) =>
        if !sym.nullary then raise:
          ErrorReport(
            msg"Expected arguments for builtin operator '${sym.nme}'" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        k(sym.asSimpleRef.withLocOf(ref))
      case st.Tup(Fld(FldFlags.benign(), arg, N) :: Nil) =>
        if !sym.unary then raise:
          ErrorReport(
            msg"Builtin '${sym.nme}' is not a unary operator" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg): ar =>
          val target = wasmIntrinsicPath(sym, unary = true)
            .getOrElse(sym.asSimpleRef.withLocOf(ref))
          k(Call(target, (Arg(N, ar) :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))
      case st.Tup(Fld(FldFlags.benign(), arg1, N) :: Fld(FldFlags.benign(), arg2, N) :: Nil) =>
        if !sym.binary then raise:
          ErrorReport(
            msg"Builtin '${sym.nme}' is not a binary operator" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg1): ar1 =>
          def mkBooleanMatch(isAnd: Bool): Block =
            val posLit = Tree.BoolLit(isAnd)
            val negLit = Tree.BoolLit(!isAnd)
            if k.isInstanceOf[TailOp] then Match(
              ar1,
              (Case.Lit(posLit) -> term_nonTail(arg2)(k)) :: Nil,
              S(k(Value.Lit(negLit))),
              Unreachable("tail operation in branches"),
            ) else
              val ts = loweringCtx.registerTempSymbol(N)
              Match(
                ar1,
                (Case.Lit(posLit) -> term_nonTail(arg2)(Assign(ts, _, End()))) :: Nil,
                S(Assign(ts, Value.Lit(negLit), End())),
                k(ts.asSimpleRef),
              )
          sym match
          case State.andSymbol => mkBooleanMatch(true)
          case State.orSymbol => mkBooleanMatch(false)
          case _ =>
            subTerm_nonTail(arg2): ar2 =>
              val target = wasmIntrinsicPath(sym, unary = false)
                .getOrElse(sym.asSimpleRef.withLocOf(ref))
              k(Call(target, (Arg(N, ar1) :: Arg(N, ar2) :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))
      case _ => fail:
        ErrorReport(
          msg"Unexpected arguments for builtin symbol '${sym.nme}'" -> arg.toLoc :: Nil, S(arg),
          source = Diagnostic.Source.Compilation)
    case st.TyApp(f, ts) => term(f)(k) // * Type arguments are erased
    case st.App(f, arg) =>
      
      // Collect chains of App nodes: `f(a)(b)(c)` → (f, [a, b, c])
      // This allows lowering curried calls as a single `Call` with multiple arg lists.
      @tailrec
      def collectAppChain(expr: st, args: Ls[Term]): (st, Ls[Term]) =
        expr.instantiated match
        case st.App(inner, innerArg) => collectAppChain(inner, innerArg :: args)
        case st.TyApp(inner, _) => collectAppChain(inner, args) // type args are erased
        case expr => (expr, args)
      val (baseF, allArgs) = collectAppChain(f, arg :: Nil)
      
      val isMlsFun = baseF.resolvedSym.fold(baseF.isInstanceOf[st.Lam]):
        case _: sem.BuiltinSymbol => true
        case sym: sem.BlockMemberSymbol =>
          sym.trmImplTree.fold(sym.clsTree.isDefined)(_.k is syntax.Fun)
        case sym: sem.TermSymbol =>
          (sym.k is syntax.Fun) && sym.defn.forall(!_.hasDeclareModifier.isDefined)
        // Do not perform safety check on `MatchSuccess` and `MatchFailure`.
        case sym => (sym is State.matchSuccessClsSymbol) ||
          (sym is State.matchFailureClsSymbol)
      
      def conclude(fr: Path) =
        lowerMultiCall(fr, isMlsFun, annots, allArgs, t.toLoc)(k)
      
      // * We have to instantiate `f` again because, if `f` is a Sel, the `term`
      // * function is not called again with f. See below `Sel` and `SelProj` cases.
      // * Note: now the instantiation is done by `collectAppChain`.
      val instantiated = baseF
      val instantiatedResolvedBms = instantiated.resolvedSym.flatMap(_.asBlkMember)
      
      instantiated match
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitand) =>
        conclude(State.runtimeSymbol.asSimpleRef.selN(Tree.Ident("bitand")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitnot) =>
        conclude(State.runtimeSymbol.asSimpleRef.selN(Tree.Ident("bitnot")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.bitor) =>
        conclude(State.runtimeSymbol.asSimpleRef.selN(Tree.Ident("bitor")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.shl) =>
        conclude(State.runtimeSymbol.asSimpleRef.selN(Tree.Ident("shl")))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.js.try_catch) =>
        conclude(State.runtimeSymbol.asSimpleRef.selN(Tree.Ident("try_catch")))
      case t if t.resolvedSym.exists {
        case sym: BlockMemberSymbol => wasmIntrinsicSymbols.contains(sym)
        case _ => false
      } =>
        val sym = t.resolvedSym.get.asInstanceOf[BlockMemberSymbol]
        conclude(State.wasmSymbol.asSimpleRef.selN(Tree.Ident(sym.nme)))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.debug.printStack) =>
        if !config.effectHandlers.exists(_.debug) then
          return fail:
            ErrorReport(
              msg"Debugging functions are not enabled" ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
        conclude(State.runtimeSymbol.asSimpleRef.selSN("raisePrintStackEffect").withLocOf(baseF))
      case t if instantiatedResolvedBms.exists(_ is ctx.builtins.scope.locally) =>
        // scope.locally only applies to the innermost call; extra args are applied on top
        if allArgs.length > 1 then
          subTerm(baseF)(conclude)
        else
          arg match
          case Tup(Fld(FldFlags.benign(), body, N) :: Nil) =>
            LoweringCtx.nestScoped.givenIn:
              val res = block(Nil, R(body))(k)
              val scopedSyms = loweringCtx.getCollectedSym
              // Put the Scoped in the rest, so that the returned result can be found correctly
              Scoped(scopedSyms, res)
          case _ => return fail:
            ErrorReport(
              msg"Unsupported form for scope.locally." ->
              t.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
      // * Due to whacky JS semantics, we need to make sure that selections leading to a call
      // * are preserved in the call and not moved to a temporary variable.
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(N)(false).withLocOf(sel))
      case Resolved(sel @ Sel(prefix, nme), sym) =>
        subTerm(prefix): p =>
          conclude(Select(p, definitionIdent(nme, sym))(S(sym))(false).withLocOf(sel))
      case sel @ SelProj(prefix, _, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(N)(false).withLocOf(sel))
      case Resolved(sel @ SelProj(prefix, _, nme), sym) =>
        subTerm(prefix): p =>
          conclude(Select(p, definitionIdent(nme, sym))(S(sym))(false).withLocOf(sel))
      case _ => subTerm(baseF)(conclude)
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
      loweringCtx.collectScopedSym(lhs)
      val resSym = loweringCtx.registerTempSymbol(S(t))
      subTerm(rhs): par =>
        subTerms(as): asr =>
          HandleBlock(lhs, resSym, par, asr, cls, handlers,
            inScopedBlock(returnedTerm(bod)),
            k(resSym.asSimpleRef))
    case st.Blk(sts, res) => block(sts, R(res), inStmtPos = inStmtPos)(k)
    case Assgn(lhs, rhs) =>
      // * An assignment LHS is an l-value: normal term lowering would read the
      // * selected field, possibly with access instrumentation, while here we
      // * need the selected prefix/name/symbol in order to emit `AssignField`.
      // * Still, resolver expansions matter: `Resolved(lhs, sym)` carries the
      // * disambiguated member symbol needed for private fields and overloads.
      val (target, resolvedSelectionSymbol) = lhs.instantiated match
        case Resolved(inner, sym) => inner -> S(sym)
        case target => target -> N
      target match
      case Ref(sym) =>
        subTerm(rhs): r =>
          assignSymbol(resolvedSelectionSymbol.getOrElse(sym), sym, r, k(unit), trm.toLoc)
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, nme, r, k(unit))(resolvedSelectionSymbol)
      case sel @ SynthSel(prefix, nme) =>
        // * See the doc in the `term` case for `SynthSel` for why we fall back to `sel.sym` here
        val sym = resolvedSelectionSymbol match
          case S(sym) => S(sym)
          case N => sel.sym match
            case S(sym: DefinitionSymbol[?]) => S(sym)
            case _ => N
        softAssert(sym.nonEmpty, s"Missing symbol for synthetic assignment target ${sel.showDbg}")
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, memberIdent(nme, sel.sym), r, k(unit))(sym)
      case sel @ DynSel(prefix, fld, ai) =>
        subTerm(prefix): p =>
          subTerm_nonTail(fld): f =>
            subTerm_nonTail(rhs): r =>
              AssignDynField(p, f, ai, r, k(unit))
      case sel @ SelProj(prefix, _, proj) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, memberIdent(proj, sel.sym), r, k(unit))(resolvedSelectionSymbol)
      case _ => fail:
        ErrorReport(
          msg"Unexpected left-hand side in assignment (${lhs.describe})" -> lhs.toLoc :: Nil, S(lhs),
          source = Diagnostic.Source.Compilation)
      
    case st.Lam(params, body) =>
      warnStmt
      val (paramLists, bodyBlock) = setupFunctionDef(params :: Nil, body, N)
      if k.isInstanceOf[TailOp] || bodyBlock.size <= 5
      then k(Lambda(paramLists.head, bodyBlock)(Nil))
      else
        val lamSym = new BlockMemberSymbol("lambda", Nil, false)
        loweringCtx.collectScopedSym(lamSym)
        val lamDef = FunDefn.withFreshSymbol(N, lamSym, paramLists, bodyBlock)(configOverride = N, annotations = Nil)
        Define(
          lamDef,
          k(lamDef.asPath))
    
    
    case iftrm: st.IfLike => ucs.Normalization(this)(iftrm)(k)
    
    case iftrm: st.SynthIf => ucs.Normalization(this)(iftrm)(k)

    case whltrm: st.SynthWhile => ucs.Normalization(this)(whltrm)(k)
      
    case sel @ Sel(prefix, nme) =>
      setupSelection(prefix, nme, N)(k)
    case Resolved(sel @ Sel(prefix, nme), sym) =>
      setupSelection(prefix, nme, S(sym))(k)
    
    case sel @ SynthSel(prefix, nme) =>
      // * Not using `setupSelection` as these selections are not meant to be sanity-checked
      // * Unlike source `Sel`s, compiler-synthesized selections may carry a known
      // * member symbol directly in `sel.sym` without being wrapped in `Resolved`.
      // * This reflects the current IR convention: `sel.sym` records the selected
      // * member/representative, while `Resolved(sel, sym)` records a disambiguated
      // * definition when one exists. Do not use this fallback for ordinary `Sel`
      // * lowering unless that convention is changed at the source.
      subTerm(prefix): p =>
        k(Select(p, memberIdent(nme, sel.sym))(sel.sym.collect:
          case s: DefinitionSymbol[?] => s
        )(false))
    case Resolved(sel @ SynthSel(prefix, nme), sym) =>
      // * Not using `setupSelection` as these selections are not meant to be sanity-checked
      subTerm(prefix): p =>
        k(Select(p, definitionIdent(nme, sym))(S(sym))(false))
    
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
        case N => lowerMultiInstantiate(mut, sr, as, annots)(k)
        case S((isym, rft)) =>
          val sym = new BlockMemberSymbol(isym.name, Nil)
          loweringCtx.collectScopedSym(sym)
          val (mtds, publicFlds, privateFlds, ctor) = gatherMembers(rft)
          val pctor = parentConstructor(sr, cls, as)
          val clsDef = ClsLikeDefn(N, isym, sym, N, syntax.Cls, N, Nil, S(sr),
            mtds, privateFlds, publicFlds, pctor, ctor, N, N)(N, Nil)
          val inner = new New(sym.ref().resolved(isym), Nil, N)(N)
          Define(clsDef, term_nonTail(if mut then Mut(inner) else inner)(k))
      
    case Try(sub, finallyDo) =>
      val l = loweringCtx.registerTempSymbol(S(sub))
      TryBlock(
        subTerm_nonTail(sub)(p => Assign(l, p, End())),
        subTerm_nonTail(finallyDo)(_ => End()),
        k(l.asSimpleRef)
      )
    
    case Quoted(body) => quote(body)(k)
    
    // * InvalML-specific cases: t.Cls#field and mutable operations
    case sp @ SelProj(prefix, _, proj) =>
      setupSelection(prefix, proj, N)(k)
    case Resolved(sp @ SelProj(prefix, _, proj), sym) =>
      setupSelection(prefix, proj, S(sym))(k)
    case Resolved(inner, sym) => TODO(s"lowering for Resolved($inner)")
    case Region(reg, body) =>
      loweringCtx.collectScopedSym(reg)
      Assign(reg, Instantiate(mut = true, Select(State.globalThisSymbol.asThis, Tree.Ident("Region"))(N)(false), Nil :: Nil)(InstantiateMetadata.empty),
        term_nonTail(body)(k))
    case RegRef(reg, value) =>
      plainArgs(reg :: value :: Nil): args =>
        k(Instantiate(mut = true, Select(State.globalThisSymbol.asThis, Tree.Ident("Ref"))(N)(false), args :: Nil)(InstantiateMetadata.empty))
    case Drop(ref) =>
      subTerm(ref): _ =>
        k(unit)
    case Deref(ref) =>
      subTerm(ref): r =>
        k(Select(r, Tree.Ident("value"))(N)(false))
    case SetRef(lhs, rhs) =>
      subTerm(lhs): ref =>
        subTerm_nonTail(rhs): value =>
          AssignField(ref, Tree.Ident("value"), value, k(value))(N)
    
    case Mut(Rcd(mut, stats)) => // TODO: warn when in statement position
      // * Note: I don't think this is supposed to happen...
      block(stats, L(mut -> Nil))(k)
    case Rcd(mut, stats) => // TODO: warn when in statement position
      block(stats, L(mut -> Nil))(k)
    
    case Missing => fail:
      ErrorReport(
        msg"Cannot compile ${t.describe} term that was not elaborated (maybe elaboration was one in 'lightweight' mode?)" ->
          t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation)
    case _: CompType | _: Neg | _: Term.FunTy | _: Term.Forall | _: Term.WildcardTy | _: Term.Unquoted | _: LeadingDotSel | _: Term.Constrained | _: Term.Annotated
    => fail:
      ErrorReport(
        msg"Unexpected term form in expression position (${t.describe})" ->
          t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation)
    case Error() => compError
    
    // case _ =>
    //   subTerm(t)(k)
  
  def setupTerm(name: Str, args: Ls[Path])(k: Result => Block)(using LoweringCtx): Block =
    k(Instantiate(mut = false, State.termSymbol.asSimpleRef.selSN(name), args.map(_.asArg) :: Nil)(InstantiateMetadata.empty))

  def setupQuotedKeyword(kw: Str): Path =
    State.termSymbol.asSimpleRef.selSN("Keyword").selSN(kw)

  def setupSymbol(symbol: ValueSymbol)(k: Result => Block)(using LoweringCtx): Block =
    k(Instantiate(mut = false, State.termSymbol.asSimpleRef.selSN("Symbol"),
      (Value.Lit(Tree.StrLit(symbol.nme)).asArg :: Nil) :: Nil)(InstantiateMetadata.empty))

  def quotePattern(p: FlatPattern)(k: Result => Block)(using LoweringCtx): Block = p match
    case FlatPattern.Lit(lit) => setupTerm("LitPattern", Value.Lit(lit) :: Nil)(k)
    case _ => // TODO
      fail:
        ErrorReport(
          msg"Unsupported quasiquote pattern type" ->
          p.toLoc :: Nil,
          source = Diagnostic.Source.Compilation
        )
  
  def quoteSplit(split: Split, splitTmps: Map[SplitSymbol, TempSymbol])(k: Result => Block)(using LoweringCtx): Block = split match
    case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => quote(scrutinee): r1 =>
      val l1, l2, l3, l4, l5 = loweringCtx.registerTempSymbol(N)
      blockBuilder.assign(l1, r1)
        .chain(b => quotePattern(pattern)(r2 => Assign(l2, r2, b)))
        .chain(b => quoteSplit(continuation, splitTmps)(r3 => Assign(l3, r3, b)))
        .chain(b => setupTerm("Branch", (l1 :: l2 :: l3 :: Nil).map(s => s.asSimpleRef))(r4 => Assign(l4, r4, b)))
        .chain(b => quoteSplit(tail, splitTmps)(r5 => Assign(l5, r5, b)))
        .rest(setupTerm("Cons", (l4 :: l5 :: Nil).map(s => s.asSimpleRef))(k))
    case Split.Let(sym: LocalVarSymbol, term, tail) => setupSymbol(sym): r1 =>
      loweringCtx.collectScopedSym(sym)
      val l1, l2, l3 = loweringCtx.registerTempSymbol(N)
      blockBuilder.assign(l1, r1)
        .chain(b => setupTerm("Ref", l1.asSimpleRef :: Nil)(r => Assign(sym, r, b)))
        .chain(b => quote(term)(r2 => Assign(l2, r2, b)))
        .chain(b => quoteSplit(tail, splitTmps)(r3 => Assign(l3, r3, b)))
        .rest(setupTerm("Let", (l1 :: l2 :: l3 :: Nil).map(s => s.asSimpleRef))(k))
    case Split.Else(default) => quote(default): r =>
      val l = loweringCtx.registerTempSymbol(N)
      Assign(l, r, setupTerm("Else", l.asSimpleRef :: Nil)(k))
    case Split.End => setupTerm("End", Nil)(k)
    case Split.LetSplit(sym, tail) =>
      val tmp =  loweringCtx.registerTempSymbol(N, sym.nme + "_splitTmp")
      val splitTmps2 = splitTmps + (sym -> tmp)
      setupSymbol(tmp): r1 =>
        val l1, l2, l3 = loweringCtx.registerTempSymbol(N)
        blockBuilder.assign(l1, r1)
          .chain(b => Assign(tmp, l1.asSimpleRef, b))
          .chain(b => quoteSplit(sym.body, splitTmps2)(r2 => Assign(l2, r2, b)))
          .chain(b => quoteSplit(tail, splitTmps2)(r3 => Assign(l3, r3, b)))
          .rest(setupTerm("LetSplit", (l1 :: l2 :: l3 :: Nil).map(s => s.asSimpleRef))(k))
    case Split.UseSplit(sym) => setupTerm("UseSplit", splitTmps(sym).asSimpleRef :: Nil)(k)

  lazy val setupFilename: Path =
    val state = summon[State]
    state.importSymbol.asSimpleRef.selSN("meta").selSN("url")

  def quote(t: st)(k: Result => Block)(using LoweringCtx): Block = t match
    case Lit(lit) =>
      setupTerm("Lit", Value.Lit(lit) :: Nil)(k)
    case Ref(sym) if Elaborator.binaryOps.contains(sym.nme) => // builtin symbols
      val l = loweringCtx.registerTempSymbol(N)
      setupTerm("Builtin", Value.Lit(Tree.StrLit(sym.nme)) :: Nil)(k)
    case Resolved(Ref(sym), disamb) =>
      sym match
        case sym: BlockMemberSymbol => k(sym.asMemberRef(disamb))
        case sym: SimpleSymbol => k(sym.asSimpleRef)
        case sym => lastWords(s"Unexpected symbol kind ${sym.getClass.getSimpleName}: $sym")
    case Ref(sym: ValueSymbol) => k(sym.asPath)
    case Ref(sym) => lastWords(s"Unexpected symbol kind ${sym.getClass.getSimpleName}: $sym")
    case SynthSel(Ref(sym: ModuleOrObjectSymbol), name) => // Module/object cross-stage references
      setupSymbol(sym): r1 =>
        val l1, l2 = loweringCtx.registerTempSymbol(N)
        Assign(l1, r1, setupTerm("CSRef", l1.asSimpleRef :: setupFilename :: Value.Lit(syntax.Tree.UnitLit(false)) :: Nil)(r2 =>
          Assign(l2, r2, setupTerm("Sel", l2.asSimpleRef :: Value.Lit(syntax.Tree.StrLit(name.name)) :: Nil)(k))
        ))
    case SynthSel(Ref(sym: BlockMemberSymbol), name) => // Multi-file cross-stage references
      if config.qqEnabled then fail:
        ErrorReport(
            msg"Cross-stage reference to ${sym.nme}.${name.name} is only allowed in compiled files due to the lack of `import.meta` in REPL mode." ->
            t.toLoc :: Nil,
            source = Diagnostic.Source.Compilation
          )
      else (t.toLoc, sym.toLoc) match
        case (S(Loc(_, _, Origin(base, _, _))), S(Loc(_, _, Origin(filename, _, _)))) => setupSymbol(sym): r1 =>
          val l1, l2 = loweringCtx.registerTempSymbol(N)
          val basePath = base.up
          val targetPath = filename
          val relPath = targetPath.relativeTo(basePath).map(_.toString).getOrElse(targetPath.toString)
          Assign(l1, r1, setupTerm("CSRef", l1.asSimpleRef :: setupFilename :: Value.Lit(syntax.Tree.StrLit(relPath)) :: Nil)(r2 =>
            Assign(l2, r2, setupTerm("Sel", l2.asSimpleRef :: Value.Lit(syntax.Tree.StrLit(name.name)) :: Nil)(k))
          ))
        case _ => fail:
          ErrorReport(
            msg"Cannot refer to imported module ${sym.nme} due to the lack of path." ->
            t.toLoc :: Nil,
            source = Diagnostic.Source.Compilation
          )
    case Lam(params, body) =>
      def rec(ps: Ls[VarSymbol], ds: Ls[Path])(k: Result => Block)(using LoweringCtx): Block = ps match
        case Nil => quote(body): r =>
          val l = loweringCtx.registerTempSymbol(N)
          val arr = loweringCtx.registerTempSymbol(N, "arr")
          Assign(
            arr,
            Tuple(mut = false, ds.reverse.map(_.asArg)),
            Assign(l, r, setupTerm("Lam", arr.asSimpleRef :: l.asSimpleRef :: Nil)(k)))
        case sym :: rest =>
          loweringCtx.collectScopedSym(sym)
          setupSymbol(sym): r =>
            val l = loweringCtx.registerTempSymbol(N)
            Assign(l, r, setupTerm("Ref", l.asSimpleRef :: Nil): r1 =>
              Assign(sym, r1, rec(rest, l.asSimpleRef :: ds)(k)))
      rec(params.params.map(_.sym), Nil)(k) // TODO: restParam?
    case App(lhs, Tup(rhs)) => quote(lhs): r1 =>
      def rec(es: Ls[Elem], xs: Ls[Path])(k: Result => Block): Block = es match
        case Nil =>
          val arrSym = loweringCtx.registerTempSymbol(N, "arr")
          Assign(
            arrSym,
            Tuple(mut = false, xs.reverse.map(_.asArg)),
            setupTerm("Tup", arrSym.asSimpleRef :: Nil): r2 =>
              val l1 = loweringCtx.registerTempSymbol(N)
              val l2 = loweringCtx.registerTempSymbol(N)
              Assign(l1, r1, Assign(l2, r2, setupTerm("App", l1.asSimpleRef :: l2.asSimpleRef :: Nil)(k)))
          )
        case Fld(_, t, _) :: rest => quote(t): r2 =>
          val l = loweringCtx.registerTempSymbol(N)
          Assign(l, r2, rec(rest, l.asSimpleRef :: xs)(k))
        case Spd(eager, term) :: rest =>
          fail:
            ErrorReport(
              msg"Unsupported spread in quasiquote application" ->
              term.toLoc :: Nil,
              source = Diagnostic.Source.Compilation
            )
      rec(rhs, Nil)(k)
    case Blk(LetDecl(sym: LocalVarSymbol, _) :: DefineVar(sym2, rhs) :: Nil, res) => // Let bindings
      require(sym2 is sym)
      loweringCtx.collectScopedSym(sym)
      setupSymbol(sym){r1 =>
        val l1, l2, l3, l4, l5 = loweringCtx.registerTempSymbol(N)
        val arrSym = loweringCtx.registerTempSymbol(N, "arr")
        blockBuilder.assign(l1, r1)
          .chain(b => setupTerm("Ref", l1.asSimpleRef :: Nil)(r => Assign(sym, r, b)))
          .chain(b => quote(rhs)(r2 => Assign(l2, r2, b)))
          .chain(b => quote(res)(r3 => Assign(l3, r3, b)))
          .chain(b => setupTerm("LetDecl", l1.asSimpleRef :: Nil)(r4 => Assign(l4, r4, b)))
          .chain(b => setupTerm("DefineVar", l1.asSimpleRef :: l2.asSimpleRef :: Nil)(r5 => Assign(l5, r5, b)))
          .assign(arrSym, Tuple(mut = false, (l4 :: l5 :: Nil).map(s => s.asSimpleRef.asArg)))
          .rest(setupTerm("Blk", arrSym.asSimpleRef :: l3.asSimpleRef :: Nil)(k))
      }
    case IfLike(_, IfLikeForm.ReturningIf, split) => quoteSplit(split.getExpandedSplit, Map.empty): r =>
      val l = loweringCtx.registerTempSymbol(N)
      Assign(l, r, setupTerm("IfLike", setupQuotedKeyword("If") :: l.asSimpleRef :: Nil)(k))
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
          val cfgOverride = td.extraAnnotations.collectFirst:
            case Annot.Config(modify) => modify(config)
          FunDefn(td.owner, td.sym, td.tsym, paramLists, bodyBlock)(cfgOverride, td.annotations)
    val publicFlds = clsBody.publicFlds.collect:
      case f if !f.tsym.isPrivate =>
        f.sym -> f.tsym
    val privateFlds = clsBody.nonMethods.collect:
      case decl @ LetDecl(sym: TermSymbol, annotations) =>
        reportAnnotations(decl, annotations)
        sym
      case td: TermDefinition if td.tsym.isPrivate =>
        td.tsym
    val ctor =
      inScopedBlock:
        term_nonTail(Blk(clsBody.nonMethods, clsBody.blk.res), inStmtPos = true)(Assign.discard(_, End()))
    
    (mtds, publicFlds, privateFlds, ctor)
  
  def args(elems: Ls[Elem])(k: Ls[Arg] => Block)(using LoweringCtx): Block =
    val as = elems.map:
      case sem.Fld(sem.FldFlags.benign(), value, N) => R(N -> value)
      case sem.Fld(sem.FldFlags.benign(), idx, S(rhs)) => L(idx -> rhs)
      case arg @ sem.Fld(flags, value, asc) => TODO(s"Other argument forms: $arg")
      case spd: Spd => R(S(spd.k) -> spd.term)
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
    def rec(as: Ls[(Term -> Term) \/ (Opt[SpreadKind] -> st)]): Block = as match
      case Nil => End()
      case R((spd, a)) :: as =>
        subTerm_nonTail(a):
          ensureOnce: (ar: Path) =>
              asr ::= Arg(spd, ar)
              rec(as)
      case L((idx, t)) :: as =>
        subTerm_nonTail(idx): ir =>
          subTerm_nonTail(t):
            ensureOnce: (tr: Path) =>
              fsr ::= RcdArg(S(ir), tr)
              rec(as)
    val b = rec(as)
    if fsr.isEmpty then
      Begin(b, k(asr.reverse))
    else
      val rcdSym = loweringCtx.registerTempSymbol(N, "rcd")
      Begin(
        b,
        Assign(
          rcdSym,
          Record(mut = false, fsr.reverse),
          k((Arg(N, rcdSym.asSimpleRef) :: asr).reverse)))
      
  
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
    subTerm(t, inStmtPos = inStmtPos)(k)
  
  inline def subTerm(t: st, inStmtPos: Bool = false)(k: Path => Block)(using LoweringCtx): Block =
    term(t, inStmtPos = inStmtPos):
      case v: Value => k(v)
      case p: Path => k(p)
      case lam @ Lambda(params, body) =>
        val lamSym = BlockMemberSymbol("lambda", Nil, false)
        loweringCtx.collectScopedSym(lamSym)
        val lamDef = FunDefn.withFreshSymbol(N, lamSym, params :: Nil, body)(configOverride = N, annotations = lam.annot)
        Define(lamDef, k(lamDef.asPath))
      case r =>
        val l = loweringCtx.registerTempSymbol(N)
        Assign(l, r, k(l |> Value.SimpleRef.apply))
  
  
  def program(main: st.Blk, symbolsToPreserve: Set[BoundSymbol]): Program =
    
    val (imps, funs, rest) = splitBlock(main.stats, Nil, Nil, Nil)
    
    val blk =
      inScopedBlockExcept(symbolsToPreserve)(using LoweringCtx.empty):
        block(funs ::: rest, R(main.res))(ImplctRet)
    
    Program(
      imps.map(imp => imp.sym -> imp.str),
      blk
    )
  
  
  def setupSelection(prefix: Term, nme: Tree.Ident, disamb: Opt[DefinitionSymbol[?]])(k: Result => Block)(using LoweringCtx): Block =
    subTerm(prefix): p =>
      k(Select(p, disamb.fold(memberIdent(nme, N))(definitionIdent(nme, _)))(disamb)(
        !disamb.isDefined
        // * ^ We assume that resolved selections are well-behaved (will not yield undefined or debind a method)
        // || disamb.exists(_.defn.exists(_.hasDeclareModifier.isEmpty)) // * This checks `declare` members, which is normally unwanted
      ))
  
  final def setupFunctionOrByNameDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using LoweringCtx): (List[ParamList], Block) =
    val physicalParams = paramLists match
      case Nil => ParamList(ParamListFlags.empty, Nil, N) :: Nil
      case ps => ps
    setupFunctionDef(physicalParams, bodyTerm, name)
  
  def inScopedBlock(using LoweringCtx)(mkBlock: LoweringCtx ?=> Block): Block =
    inScopedBlockExcept(Set.empty)(mkBlock)
  def inScopedBlockExcept(syms: Set[BoundSymbol])(using LoweringCtx)(mkBlock: LoweringCtx ?=> Block): Block =
    LoweringCtx.nestScoped.givenIn:
      val body = mkBlock
      val scopedSyms = loweringCtx.getCollectedSym.filterNot(syms)
      Scoped(scopedSyms, body)
  
  def setupFunctionDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using LoweringCtx): (List[ParamList], Block) =
    val scopedBody = inScopedBlock(returnedTerm(bodyTerm))
    (paramLists, scopedBody)
  
  
  // TODO: reduce duplication between the two `reportAnnotations`
  
  def reportAnnotations(target: Statement, annotations: Ls[Annot]): Unit =
    def warn(annot: Annot, msg: Opt[Message] = N) = raise:
      msg match
        case S(value) => WarningReport(value -> annot.toLoc :: Nil)
        case N => WarningReport(msg"This annotation has no effect." -> annot.toLoc :: Nil)
    annotations.foreach:
      case Annot.Untyped => ()
      case a @ (Annot.TailRec | Annot.Inline | Annot.NoInline | Annot.Generator) =>
        val annot = a match
          case Annot.TailRec => "@tailrec"
          case Annot.Inline => "@inline"
          case Annot.NoInline => "@noInline"
          case Annot.Generator => "@generator"
        target match
          case TermDefinition(body = S(bod), k = syntax.Fun) => ()
          case TermDefinition(k = syntax.Fun) => warn(a, S(msg"Only functions with a body may be marked as $annot."))
          case _ => warn(a)
      case Annot.Modifier(syntax.Keyword.`public` | syntax.Keyword.`private` | syntax.Keyword.`virtual`) => ()
      case Annot.Modifier(syntax.Keyword("staged")) => ()
      case Annot.MayNotRaiseEffects => ()
      case _: Annot.Config => () // Config annotations are handled during FunDefn creation
      case annot => warn(annot)
  
  def reportAnnotations(receiver: Term, annotations: Ls[Annot]): Unit =
    def warn(annot: Annot, msg: Opt[Message] = N) =
      val message = msg match
        case N => msg"This annotation is not supported on ${receiver.describe} terms."
        case S(value) => value
      raise:
        WarningReport(
          msg"This annotation has no effect." -> annot.toLoc ::
          message -> receiver.toLoc :: Nil)
    
    annotations.foreach:
      case Annot.Untyped => ()
      case annot: Annot.Trm => receiver match
        case st.App(Ref(_: BuiltinSymbol), _) => warn(annot)
        case st.App(_, _) | New(_, _, _) | DynNew(_, _) | Mut(_: New | _: DynNew) => ()
        case st.Resolved(_, defnSym) if isImplicitNullaryCall(defnSym) => ()
        case _ => warn(annot)
      case a @ Annot.TailCall => receiver match
        case st.App(Ref(_: BuiltinSymbol), _) => warn(a, S(msg"The @tailcall annotation has no effect on calls to built-in symbols."))
        case st.App(_, _) => ()
        case st.Resolved(_, defnSym) if isImplicitNullaryCall(defnSym) => ()
        case _ => warn(a)
      case annot => warn(annot)


trait LoweringTraceLog(instrument: Bool)(using TL, Raise, State)
    extends Lowering:
  
  private def selFromGlobalThis(path: Str*): Path =
      path.foldLeft[Path](State.globalThisSymbol.asThis):
        (qual, name) => Select(qual, Tree.Ident(name))(N)(false)
    
  private def assignStmts(stmts: (Assignable, Result)*)(rest: Block) =
    stmts.foldRight(rest):
      case ((sym, res), acc) => Assign(sym, res, acc)
  
  private def pureCall(fn: Path, args: Ls[Arg]): Result =
    Call(fn, args ne_:: Nil)(CallMetadata.defaultMlsFun)
  
  extension (k: Block => Block)
    def |>: (b: Block): Block = k(b)

  private val traceLogFn = State.runtimeSymbol.asSimpleRef.selSN("TraceLogger").selSN("log")
  private val traceLogIndentFn = State.runtimeSymbol.asSimpleRef.selSN("TraceLogger").selSN("indent")
  private val traceLogResetFn = State.runtimeSymbol.asSimpleRef.selSN("TraceLogger").selSN("resetIndent")
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
  
  def setupFunctionBody(params: ParamList, bod: Term, name: Option[Str])(using LoweringCtx): Block = inScopedBlock:
    val enterMsgSym = loweringCtx.registerTempSymbol(N, dbgNme = "traceLogEnterMsg")
    val prevIndentLvlSym = loweringCtx.registerTempSymbol(N, dbgNme = "traceLogPrevIndent")
    val resSym = loweringCtx.registerTempSymbol(N, dbgNme = "traceLogRes")
    val retMsgSym = loweringCtx.registerTempSymbol(N, dbgNme = "traceLogRetMsg")
    val psInspectedSyms = params.params.map(p => loweringCtx.registerTempSymbol(N, dbgNme = s"traceLogParam_${p.sym.nme}") -> p.sym)
    val resInspectedSym = loweringCtx.registerTempSymbol(N, dbgNme = "traceLogResInspected")
    
    
    val psSymArgs = psInspectedSyms.zipWithIndex.foldRight[Ls[Arg]](Arg(N, Value.Lit(Tree.StrLit(")"))) :: Nil):
      case (((s, p), i), acc) => if i == psInspectedSyms.length - 1
        then Arg(N, s.asSimpleRef) :: acc
        else Arg(N, s.asSimpleRef) :: Arg(N, Value.Lit(Tree.StrLit(", "))) :: acc
    
    val tmp1, tmp2, tmp3 = loweringCtx.registerTempSymbol(N)
    
    assignStmts(psInspectedSyms.map: (pInspectedSym, pSym) =>
      pInspectedSym -> pureCall(inspectFn, Arg(N, pSym.asSimpleRef) :: Nil)
    *) |>:
    assignStmts(
      enterMsgSym -> pureCall(
        strConcatFn,
        Arg(N, Value.Lit(Tree.StrLit(s"CALL ${name.getOrElse("[arrow function]")}("))) :: psSymArgs
      ),
      tmp1 -> pureCall(traceLogFn, Arg(N, enterMsgSym.asSimpleRef) :: Nil),
      prevIndentLvlSym -> pureCall(traceLogIndentFn, Nil)
    ) |>: 
    term(bod)(r =>
    assignStmts(
      resSym -> r,
      resInspectedSym -> pureCall(inspectFn, Arg(N, resSym.asSimpleRef) :: Nil),
      retMsgSym -> pureCall(
        strConcatFn,
        Arg(N, Value.Lit(Tree.StrLit("=> "))) :: Arg(N, resInspectedSym.asSimpleRef) :: Nil
      ),
      tmp2 -> pureCall(traceLogResetFn, Arg(N, prevIndentLvlSym.asSimpleRef) :: Nil),
      tmp3 -> pureCall(traceLogFn, Arg(N, retMsgSym.asSimpleRef) :: Nil)
    ) |>:
      Ret(resSym.asSimpleRef)
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
    case Assign(lhs, rhs, TrivialStatementsAndMatch(k, m)) if rhs.isPure =>
      handleAssignAndMatch(r => Assign(lhs, rhs, r), m, k)
    case Define(defn, TrivialStatementsAndMatch(k, m)) if defn.isPure =>
      handleAssignAndMatch(r => Define(defn, r), m, k)
    case _ => N


object MergeMatchArmTransformer extends BlockTransformer(SymbolSubst.Id):
  override def applyBlock(b: Block): Block = super.applyBlock(b) match
    case m @ Match(scrut, arms, Some(dflt), rest) =>
      dflt match
      case TrivialStatementsAndMatch(k, Match(scrutRewritten, armsRewritten, dfltRewritten, restRewritten))
        if (scrutRewritten === scrut) && (restRewritten.size * armsRewritten.length) < 10 =>
          val newArms = restRewritten match
            case _: End => armsRewritten
            case _ => armsRewritten.map:
              case (cse, body) =>
                cse -> Begin(body, restRewritten)
          k.getOrElse(identity[Block]):
            Match(scrut, arms ::: newArms,
              dfltRewritten.fold(restRewritten)(Begin(_, restRewritten)) |> some, rest)
      case _ => m
    case b => b
