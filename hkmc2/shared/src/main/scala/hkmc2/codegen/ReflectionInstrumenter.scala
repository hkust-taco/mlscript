package hkmc2
package codegen

import utils.*
import hkmc2.Message.MessageContext

import scala.collection.mutable.{HashMap, HashSet}
import scala.util.chaining.*

import hkmc2.utils.*, shorthands.*

import semantics.*
import semantics.Elaborator.{State, Ctx, ctx}

import syntax.{Keyword, Literal, Tree}
import hkmc2.syntax.Tree.Ident

// it should be possible to cache some common constructions (End, Option) into the context
// this avoids having to rebuild the same shapes everytime they are needed
// allowMultipleParamList: bypasses error from instrumenting user functions with multiple parameter lists
case class Context(cache: HashMap[Path | Symbol, Path], allowMultipleParamList: Bool = false):
  def getCache(p: Path | Symbol): Option[Path] = cache.get(p)
  def addCache(p: Path | Symbol, v: Path): Context = Context(cache.clone() += (p -> v), allowMultipleParamList)
  def delCache(p: Path | Symbol): Context = Context(cache.clone() -= p, allowMultipleParamList)
  override def clone(): Context = Context(cache.clone(), allowMultipleParamList)

object Context:
  def apply(allowMultipleParamList: Bool): Context = Context(new HashMap(), allowMultipleParamList)

extension [A, B](ls: Iterable[(A => B) => B])
  def collectApply(f: Ls[A] => B): B =
    // defer applying k while prepending new elements to the list
    ls.foldRight((_: Ls[A] => B)(Nil))((headCont, tailCont) =>
      k =>
        headCont: head =>
          tailCont: tail =>
            k(head :: tail),
    )(f)

extension [A](xs: Ls[Context => ((A, Context) => Block) => Block])
  def chainContext(using ctx: Context)(k: (Ls[A], Context) => Block): Block =
    xs.foldRight((ctx: Context) => (k: (Ls[A], Context) => Block) => k(Nil, ctx))((head, tail) =>
      ctx =>
        k =>
          head(ctx): (head, ctx) =>
            tail(ctx): (tail, ctx) =>
              k(head :: tail, ctx),
    )(ctx)(k)

type ArgWrappable = Path | ValueSymbol

def asArg(x: ArgWrappable): Arg = x match
  case p: Path => p.asArg
  case l: ValueSymbol => l.asPath.asArg

// null and undefined are missing
def toValue(lit: Str | Int | BigDecimal | Bool): Value =
  val l = lit match
    case i: Int => Tree.IntLit(i)
    case b: Bool => Tree.BoolLit(b)
    case s: Str => Tree.StrLit(s)
    case n: BigDecimal => Tree.DecLit(n)
  Value.Lit(l)

// helpers for constructing Block
object Helpers:
  def assign(using State)(res: Result, symName: Str = "tmp")(k: Path => Block): Block =
    // TODO: skip assignment if res: Path?
    val sym = new TempSymbol(N, symName)
    Scoped(Set(sym), Assign(sym, res, k(sym.asSimpleRef)))

  def tuple(using State)(elems: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    assign(Tuple(false, elems.map(asArg)), symName)(k)

  def ctor(using State)(cls: Path, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    assign(Instantiate(false, cls, Ls(args.map(asArg)))(InstantiateMetadata.empty), symName)(k)

  def call(using State)(fun: Path, args: Ls[ArgWrappable], isMlsFun: Bool = true, symName: Str = "tmp")(k: Path => Block): Block =
    assign(Call(fun, args.map(asArg) ne_:: Nil)(CallMetadata(isMlsFun, false, Nil)), symName)(k)

// transform fields of a class from private to public
class DataClassTransformer(using State) extends BlockTransformer(SymbolSubst.Id):
  import Helpers._

  // add val flag to each param
  override def applyParamList(ps: ParamList) =
    ps.copy(params = ps.params.map(param => param.copy(flags = param.flags.copy(isVal = true))))

  override def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block) =
    val addSyms = defn.privateFields.map(f => (BlockMemberSymbol(f.name, Nil, false), f))
    val privateFields = addSyms.map({case (b, f) => f.name -> (b, f)}).toMap

    val paramsOpt = defn.paramsOpt.map(applyParamList)
    val auxParams = defn.auxParams.map(applyParamList)

    class PrivateFieldDefnRemover extends BlockTransformer(SymbolSubst.Id):
      override def applyPath(p: Path)(k: Path => Block) = p match
        // remove outdated definition symbols for private fields
        case s @ Select(Value.This(cls), Tree.Ident(n)) if cls == defn.isym && privateFields.get(n).isDefined => k(s.copy()(N))
        case _ => k(p)

    // change private field initializations to public
    val publicInitTransformer = new PrivateFieldDefnRemover:
      override def applyBlock(b: Block) = b match
        case AssignField(l @ Value.This(cls), Tree.Ident(n), r, rest) if cls == defn.isym =>
          privateFields.get(n) match
            case S((b, t)) =>
              applyResult(r): r =>
                assign(r): p =>
                  Define(ValDefn(t, b, p)(N, Nil), applyBlock(rest))
            case N => super.applyBlock(b)
        case _ => super.applyBlock(b)
    // only turn AssignField declarations for private fields to ValDefn for public fields
    val ctor = publicInitTransformer.applyBlock(defn.ctor)
    val methods = defn.methods.map((new PrivateFieldDefnRemover).applyFunDefn)
    
    val newDefn = defn.copy(
      paramsOpt = paramsOpt,
      auxParams = auxParams,
      publicFields = addSyms ++ defn.publicFields,
      privateFields = Nil,
      ctor = ctor,
      methods = methods,
    )(defn.configOverride, defn.annotations)

    k(newDefn)

// replaces VarSymbols using map
class VarSymSubst(map: Map[VarSymbol, VarSymbol]) extends SymbolSubst:
  override def mapVarSym(l: VarSymbol): VarSymbol = map.getOrElse(l, l)

// transform Block to Block IR so that it can be instrumented in mlscript
class ReflectionInstrumenter(using State, Raise, Ctx) extends BlockTransformer(SymbolSubst.Id):
  import Helpers._
  // scope holds bindings of variables, and the ModuleOrObjectSymbol/ClassSymbols collected are later used for redirection
  val scope = Scope.empty(Scope.Cfg.default)
  // recover `defn` for when `sym.defn` is `None`, when the definition was generated by other compiler passes
  val defnMap = HashMap[DefinitionSymbol[? <: ClassLikeDef], ClsLikeDefn]()

  def getDefn(l: DefinitionSymbol[? <: ClassLikeDef]) =
    l.defn.orElse(defnMap.get(l)).get
  
  // helpers for constructing Block IR

  def blockMod(name: Str) = summon[State].blockSymbol.asSimpleRef.selSN(name)
  def optionMod(name: Str) = summon[State].optionSymbol.asSimpleRef.selSN(name)
  def helperMod(name: Str) = summon[State].specializeHelpersSymbol.asSimpleRef.selSN(name)

  def blockCtor(name: Str, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    call(blockMod(name), args, true, symName)(k)
  def optionSome(arg: ArgWrappable, symName: Str = "tmp")(k: Path => Block): Block =
    call(optionMod("Some"), Ls(arg), true, symName)(k)
  def optionNone(symName: Str = "tmp")(k: Path => Block): Block =
    assign(optionMod("None"), symName)(k)

  def blockCall(name: Str, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    call(blockMod(name), args, symName = symName)(k)

  // linking functions defined in MLscipt

  def fnPrintCode(p: Path)(k: Block): Block =
    val printCodeFun = blockMod("Printer").selSN("class").selSN("default").selSN("printCode")
    // discard result, we only care about side effect
    call(printCodeFun, Ls(p))(_ => k)

  def fnConcat(p1: Path, p2: Path, symName: String = "concat")(k: Path => Block): Block =
    blockCall("concat", Ls(p1, p2), symName)(k)

  // transformation helpers

  // preserveName overrides the renaming of symbols within the function
  // if sym is ClassSymbol, we may need pOpt to link to the path pointing to the value of the symbol
  def transformSymbol(sym: MaybeSymbol, preserveName: Bool = false, pOpt: Option[Path] = N, symName: Str = "sym")(using ctx: Context)(k: (Path, Context) => Block): Block =
    sym match
      case sym: Symbol => transformSymbol(sym, preserveName, pOpt, symName)(k)
      // the symbol will never be referenced, so no need to cache it
      case _: NoSymbol => blockCtor("NoSymbol", Nil, symName)(k(_, ctx))
  
  def transformSymbol(sym: Symbol, preserveName: Bool, pOpt: Option[Path], symName: Str)(using ctx: Context)(k: (Path, Context) => Block): Block =
    def cachedK(p: Path, ctx: Context) =
      k(p, ctx.addCache(sym, p))
    def checkMap(mapType: Str, key: Path, p: Path, ctx: Context) =
      call(State.runtimeSymbol.asPath.selSN("SymbolMap").selSN(mapType), Ls(key, p))(cachedK(_, ctx))
    ctx.getCache(sym).map(cachedK(_, ctx)).getOrElse:
      // reserve name to scope to avoid shadowing by other symbols
      val rename = sym match
        case _ if pOpt.isDefined => false
        case _ if preserveName => scope.allocateOrGetName(sym); false
        // non-top-level classes
        case c: ClassSymbol if c.defn.exists(_.owner.isDefined) => false
        // top-level user-defined staged classes
        case c: ClassSymbol if c.defn.exists(defn => defn.owner.isEmpty && defn.hasStagedModifier.isDefined) => false
        // avoid name collision
        case _: TempSymbol | _: LocalVarSymbol | _: BaseTypeSymbol => true
        // FIXME: there may be more types of symbols that need to be renamed during staging
        case b: BlockMemberSymbol =>
          if !b.nameIsMeaningful then scope.allocateOrGetName(sym)
          false
        case _: BuiltinSymbol => false
        case t: TermSymbol if t.defn.exists(_.sym.asTrm.isDefined) && (t.k is syntax.Fun) => false
        case _ => false
      val name = if rename then scope.allocateOrGetName(sym) else sym.nme
      sym match
        case t: TermSymbol if t.defn.exists(_.sym.asClsOrMod.isDefined) =>
          // no need to perform caching for redirecting call
          transformSymbol(t.defn.get.sym.asClsOrMod.get, rename, pOpt, symName)(k)
        case clsSym: ClassSymbol if Elaborator.ctx.builtins.virtualClasses(clsSym) =>
          blockCtor("VirtualClassSymbol", Ls(toValue(name)), symName)(checkMap("checkClassMap", toValue(name), _, ctx))
        case baseSym: BaseTypeSymbol =>
          util.boundary:
            val (owner, bsym, paramsOpt, auxParams, ctorSym) = (baseSym.defn, defnMap.get(baseSym)) match
              case (S(defn), _) => (defn.owner, defn.bsym, defn.paramsOpt, defn.auxParams, defn.ctorSym)
              case (_, S(defn: ClsLikeDefn)) => (defn.owner, defn.sym, defn.paramsOpt, defn.auxParams, defn.ctorSym)
              // FIXME: hack to patch in staging for returning the object Unit.
              case _ if baseSym == State.unitSymbol => (N, baseSym, N, Nil, N)
              case _ =>
                raise(ErrorReport(msg"Unable to infer parameters from symbol in staged module, which are necessary to reconstruct class instances: ${sym.toString()}" -> baseSym.toLoc :: Nil))
                util.boundary.break(End())
            
            val path = (pOpt, owner, ctorSym) match
              case (S(p), _, _) => p
              case (N, S(owner), _) => owner.asThis.selSN(baseSym.nme)
              case (N, N, S(ctorSym)) => bsym.asBlkMember.get.asMemberRef(ctorSym)
              case _ => bsym.asBlkMember.get.asMemberRef(baseSym.asClsOrMod.get)

            baseSym match
              case _: ClassSymbol =>
                transformParamsOpt(paramsOpt): (paramsOpt, ctx) =>
                  auxParams.map(ps => ctx => transformParamList(ps)(using ctx)).chainContext: (auxParams, ctx) =>
                    tuple(auxParams): auxParams =>
                      blockCtor("ConcreteClassSymbol", Ls(toValue(name), path, paramsOpt, auxParams, toValue(rename)), symName)(checkMap("checkClassMap", path, _, ctx))
              case _: ModuleOrObjectSymbol =>
                blockCtor("ModuleSymbol", Ls(toValue(name), path, toValue(rename)), symName)(checkMap("checkModuleMap", path, _, ctx))
        case _ =>
          blockCtor("Symbol", Ls(toValue(name)), symName)(cachedK(_, ctx))

  def transformOption[A](xOpt: Opt[A], f: A => ((Path, Context) => Block) => Block)(using Context)(k: (Path, Context) => Block): Block = xOpt match
    case S(x) => f(x)((p, ctx) => optionSome(p)(k(_, ctx)))
    case N => optionNone()(k(_, summon))

  // instrumentation rules

  def ruleEnd(symName: String = "end")(k: Path => Block): Block =
    blockCtor("End", Ls(), symName)(k)

  def ruleBranches(x: Path, p: Path, arms: Ls[Case -> Block], dflt: Opt[Block], symName: String = "branches")(using Context)(k: (Path, Context) => Block): Block =
    def applyRuleBranch(cse: Case, block: Block)(f: Path => Context => Block)(ctx: Context): Block =
      transformCase(cse): cse =>
        transformBlock(block)(using ctx.addCache(p, x)): (y, ctx) =>
          blockCtor("Arm", Ls(cse, y)): cde =>
            f(cde)(ctx.delCache(p))

    (arms.map(applyRuleBranch).collectApply(_: Ls[Path] => Context => Block)(summon)): arms =>
      ctx =>
        tuple(arms): arms =>
          ruleEnd(): e =>
            def dfltStaged(k: (Path, Context) => Block) = dflt match
              case S(dflt) =>
                transformBlock(dflt)(using ctx.addCache(p, x)): (dflt, ctx) =>
                  optionSome(dflt)(k(_, ctx.delCache(p)))
              case N => optionNone()(k(_, ctx))
            dfltStaged: (dflt, ctx) =>
              blockCtor("Match", Ls(x, arms, dflt, e), symName)(k(_, ctx))

  // transformations of Block

  def transformPath(p: Path)(using ctx: Context)(k: (Path, Context) => Block): Block =
    // rulePath
    ctx.getCache(p).map(k(_, ctx)).getOrElse:
      p match
        case Value.SimpleRef(l) =>
          transformSymbol(l): (sym, ctx) =>
            blockCtor("ValueSimpleRef", Ls(sym), "var")(k(_, ctx))
        case Value.MemberRef(bms, disamb) =>
          transformSymbol(disamb): (sym, ctx) =>
            blockCtor("ValueMemberRef", Ls(sym), "var")(k(_, ctx))
        case l: Value.Lit =>
          blockCtor("ValueLit", Ls(l), "lit")(k(_, ctx))
        case Value.This(sym) =>
          transformSymbol(sym): (sym, ctx) =>
            blockCtor("ValueThis", Ls(sym))(k(_, ctx))
        case s @ Select(p, Tree.Ident(name)) =>
          transformPath(p): (x, ctx) =>
            s.symbol match
              case S(sym) => transformSymbol(sym, true, pOpt = S(s))(using ctx)((sym, ctx) => blockCtor("Select", Ls(x, sym), "sel")(k(_, ctx)))
              case N => blockCtor("Symbol", Ls(toValue(name)))(sym => blockCtor("Select", Ls(x, sym), "sel")(k(_, ctx)))
        case DynSelect(qual, fld, arrayIdx) =>
          transformPath(qual): (x, ctx) =>
            transformPath(fld)(using ctx): (y, ctx) =>
              blockCtor("DynSelect", Ls(x, y, toValue(arrayIdx)), "dynsel")(k(_, ctx))

  def transformResult(r: Result)(using ctx: Context)(k: (Path, Context) => Block): Block = r match
    case p: Path => transformPath(p)(k)
    case Tuple(mut, elems) =>
      if mut then raise(ErrorReport(msg"Mutable tuples not supported in staged module." -> r.toLoc :: Nil))
      transformArgs(elems): (xs, ctx) =>
        tuple(xs.map(_._1)): codes =>
          blockCtor("Tuple", Ls(codes), "tup")(k(_, ctx))
    case Instantiate(mut, cls, argss) =>
      if mut then raise(ErrorReport(msg"Mutable instantiations not supported in staged module." -> r.toLoc :: Nil))
      argss match
        case Nil =>
          raise(ErrorReport(msg"Instantiate with no argument lists not supported in staged module." -> r.toLoc :: Nil))
          End()
        case args :: Nil =>
          transformArgs(args): (xs, ctx) =>
            transformPath(cls)(using ctx): (cls, ctx) =>
              tuple(xs.map(_._1)): codes =>
                blockCtor("Instantiate", Ls(cls, codes), "inst")(k(_, ctx))
        case args :: restArgss =>
          raise(ErrorReport(msg"Instantiate with multiple argument lists not supported in staged module." -> r.toLoc :: Nil))
          End()
    // desugar Runtime.Tuple.get into Select
    case Call(fun, Ls(Arg(_, scrut), Arg(_, Value.Lit(Tree.IntLit(idx)))) :: _) if fun == Value.SimpleRef(State.runtimeSymbol).selSN("Tuple").selSN("get") =>
      transformPath(Select(scrut, Tree.Ident(idx.toString()))(N))(k)
    case Call(fun, argss) =>
      argss match
        case args :: Nil =>
          transformPath(fun): (stagedFun, ctx) =>
            transformArgs(args)(using ctx): (args, ctx) =>
              tuple(args.map(_._1)): tup =>
                blockCtor("Call", Ls(stagedFun, tup), "app")(k(_, ctx))
        case args :: restArgss =>
          raise(ErrorReport(msg"Call with multiple argument lists not supported in staged module." -> r.toLoc :: Nil))
          End()
    case _ =>
      raise(ErrorReport(msg"Other Results not supported in staged module: ${r.getClass.toString()}" -> r.toLoc :: Nil))
      End()

  def transformArg(a: Arg)(using Context)(k: ((Path, Bool), Context) => Block): Block =
    val Arg(spread, value) = a
    if spread.isDefined then raise(ErrorReport(msg"Spread parameters are not supported in staged module." -> value.toLoc :: Nil))
    transformPath(value): (value, ctx) =>
      blockCtor("Arg", Ls(value)): cde =>
        k((cde, spread.isDefined), ctx)

  def transformArgs(args: Ls[Arg])(using Context)(k: (Ls[(Path, Bool)], Context) => Block): Block =
    args.map(a => ctx => transformArg(a)(using ctx)).chainContext(k)

  // maintain parameter names in instrumented code
  def transformParamList(ps: ParamList)(using ctx: Context)(k: (Path, Context) => Block) =
    ps.params.map(p => (ctx: Context) => (k: (Path, Context) => Block) =>
        transformOption(p.flags.reflConstraint, {
          case ReflectionConstraint.Dynamic => k => blockCtor("Dynamic", Nil)(k(_, ctx))
          case ReflectionConstraint.Static => k => blockCtor("Static", Nil)(k(_, ctx))
        })(using ctx): (constraint, ctx) =>
          transformSymbol(p.sym, true)(using ctx): (sym, ctx) =>
            blockCtor("Param", Ls(constraint, sym))(k(_, ctx))
      ).chainContext((ps, ctx) => tuple(ps)(k(_, ctx)))

  def transformParamsOpt(pOpt: Opt[ParamList])(using ctx: Context)(k: (Path, Context) => Block) =
    transformOption(pOpt, transformParamList)(k)

  def transformParams(params: Ls[ParamList])(using Context)(k: (Path, Context) => Block) =
    params.map(ps => ctx => transformParamList(ps)(using ctx)).chainContext((p, ctx) => tuple(p)(k(_, ctx)))

  def transformCase(cse: Case)(using Context)(k: Path => Block): Block = cse match
    case Case.Lit(lit) => blockCtor("Lit", Ls(Value.Lit(lit)))(k)
    case Case.Cls(cls, path) =>
      transformSymbol(cls): (cls, ctx) =>
        transformPath(path)(using ctx): (path, ctx) =>
          blockCtor("Cls", Ls(cls, path))(k)
    case Case.Tup(len, inf) =>
      if inf then raise(ErrorReport(msg"Spread parameters are not supported in staged module: ${cse.toString()}" -> N :: Nil))
      blockCtor("Tup", Ls(toValue(len)))(k)
    case Case.Field(name, safe) =>
      raise(ErrorReport(msg"Case.Field not supported in staged module." -> name.toLoc :: Nil))
      End()

  def transformBlock(b: Block)(using ctx: Context)(k: (Path, Context) => Block): Block = b match
    case Return(res) =>
      transformResult(res): (x, ctx) =>
        blockCtor("Return", Ls(x), "return")(k(_, ctx))
    case Assign(x, r, b) =>
      transformResult(r): (y, ctx) =>
        transformSymbol(x): (xSym, ctx) =>
          blockCtor("ValueSimpleRef", Ls(xSym)): xStaged =>
            (Assign(x, xStaged, _)):
              val nextCtx = ctx.clone()
              given Context = x match
                case NoSymbol => nextCtx
                case x: ValueSymbol => nextCtx.addCache(x.asPath, xStaged)
              transformBlock(b): (z, ctx) =>
                blockCtor("Assign", Ls(xSym, y, z), "assign")(k(_, ctx))
    case assign @ AssignField(lhs, nme, r, rest) =>
      // TODO: Improve. This is a kludge to allow private field initialization in modules;
      //    Ideally, we should just properly reflect these as the private field assignments they are
      assign.symbol match
        case S(ts: TermSymbol) if ts.isPrivate =>
          transformResult(r): (y, ctx) =>
            transformSymbol(ts)(using ctx): (xSym, ctx) =>
              blockCtor("ValueSimpleRef", Ls(xSym)): xStaged =>
                  given Context = ctx.addCache(Select(lhs, nme)(S(ts)), xStaged)
                  transformBlock(rest): (z, ctx) =>
                    blockCtor("Assign", Ls(xSym, y, z), "assign")(k(_, ctx))
        case _ =>
          raise:
            ErrorReport(msg"Field assignment is not supported in staged modules: ${nme.name}" -> N :: Nil)
          End()
    case Define(cls: ClsLikeDefn, rest) =>
      assert(cls.companion.isEmpty, "nested module not supported")
      transformSymbol(cls.isym): (c, ctx) =>
        // staging the methods within the module
        cls.methods.map(defn => ctx => transformFunDefn(defn)(using ctx)).chainContext(using ctx): (methods, ctx) =>
          tuple(methods): methods =>
            optionNone(): none => // TODO: handle companion object
              blockCtor("ClsLikeDefn", Ls(c, methods, none)): cls =>
                transformBlock(rest)(using ctx): (p, ctx) =>
                  blockCtor("Define", Ls(cls, p))(k(_, ctx))
    case Define(v: ValDefn, rest) =>
      // TODO: only allow ValDefn inside ctors
      transformOption(v.tsym.owner, transformSymbol(_)): (owner, ctx) =>
        transformSymbol(v.sym)(using ctx): (sym, ctx) =>
          transformPath(v.rhs)(using ctx): (rhs, ctx) =>
            transformBlock(rest)(using ctx): (p, ctx) =>
              blockCtor("ValDefn", Ls(owner, sym, rhs)): v =>
                blockCtor("Define", Ls(v, p))(k(_, ctx))
    case End(_) => ruleEnd()(k(_, ctx))
    case Match(p, ks, dflt, rest) =>
      transformPath(p): (x, ctx) =>
        ruleBranches(x, p, ks, dflt)(using ctx): (stagedMatch, ctx) =>
          transformBlock(rest)(using ctx): (z, ctx) =>
            fnConcat(stagedMatch, z, "match")(k(_, ctx))
    case Begin(sub, rest) =>
      // TODO: This is untested as there is no test case that generates the Begin block yet
      transformBlock(sub): (sub, ctx) =>
        transformBlock(rest)(using ctx): (rest, ctx) =>
          fnConcat(sub, rest)(k(_, ctx))
    case Scoped(syms, body) =>
      syms.toList.sortBy(_.uid).map(s => ctx => transformSymbol(s)(using ctx)).chainContext(using ctx): (symsStaged, ctx) =>
        tuple(symsStaged): tup =>
          transformBlock(body)(using ctx): (body, ctx) =>
            blockCtor("Scoped", Ls(tup, body))(b => Scoped(syms, k(b, ctx)))
    case Define(_: FunDefn, _) =>
      raise(ErrorReport(msg"Nested function definitions are not supported in staged modules. Try enabling :ftc." -> N :: Nil))
      End()
    case _: Label | _: Break =>
      raise(ErrorReport(msg"Other Blocks not supported in staged module: ${b.getClass.toString()}." -> N :: Nil))
      End()
    case _ =>
      raise(ErrorReport(msg"Other Blocks not supported in staged module: ${b.getClass.toString()}" -> N :: Nil))
      End()

  def transformFunDefn(f: FunDefn)(using Context)(k: (Path, Context) => Block): Block =
    // maintain parameter names in instrumented code
    transformSymbol(f.sym): (sym, ctx) =>
      if f.params.length > 1 && !ctx.allowMultipleParamList then
        raise(ErrorReport(msg":ftc must be enabled to desugar functions with multiple parameter lists." -> f.sym.toLoc :: Nil))
      transformParams(f.params)(using ctx): (paramList, ctx) =>
        transformBlock(f.body)(using ctx): (body, ctx) =>
          blockCtor("FunDefn", Ls(sym, paramList, body))(k(_, ctx))

  def stageMethod(f: FunDefn, ctx: Context = Context(false)): FunDefn =
    val stageSymName = f.sym.nme + "_instr"
    val stageSym = BlockMemberSymbol(stageSymName, Nil, false)

    // turn into fundefn
    val dSym = TermSymbol(f.dSym.k, f.dSym.owner, Tree.Ident(stageSymName))
    val argSyms = f.params.flatMap(_.params).map(_.sym)
    val newBody = transformFunDefn(f)(using ctx)((block, _) => Return(block))

    FunDefn.withFreshSymbol(f.dSym.owner, stageSym, Ls(PlainParamList(Nil)), newBody)(f.configOverride, f.annotations)

  def refreshParamList(ps: ParamList) = 
    PlainParamList(ps.params.map(p => Param.simple(VarSymbol(Tree.Ident(p.sym.nme)))))

  def genMethod(cache: Path, classFun: Bool)(f: FunDefn, stagedPath: Path) =
    val genSymName = f.sym.nme + "_gen"
    val sym = BlockMemberSymbol(genSymName, Nil, false)
    val dSym = TermSymbol(f.dSym.k, f.dSym.owner, Tree.Ident(genSymName))

    // refresh parameters
    val funParams = f.params.map(refreshParamList)
    val params = if classFun then PlainParamList(Param.simple(VarSymbol(Tree.Ident("cls"))) :: Nil) :: funParams else funParams
    val body = params.map(ps => tuple(ps.params.map(_.sym))).collectApply: tups =>
      tuple(tups): args =>
        call(helperMod("specialize"), Ls(cache, toValue(f.sym.nme), stagedPath, args)): res =>
          Return(res)
    FunDefn.withFreshSymbol(f.dSym.owner, sym, params, body)(f.configOverride, f.annotations)
  
  def stageCtor(ctorFun: FunDefn): FunDefn = 
    // refresh VarSymbols for ctor
    val paramSymMap = ctorFun.params.map(_.params.map(x => x.sym -> VarSymbol(x.sym.id))).flatten.toMap
    // refresh symbols after copying parameter list
    val paramRewrite = new BlockTransformer(VarSymSubst(paramSymMap))
    stageMethod(paramRewrite.applyFunDefn(ctorFun), Context(true))

  case class StagingCfg(ownerSym: DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol, modSym: InnerSymbol, nestedPropagates: Ls[Path], codegenClasses: Ls[BlockMemberSymbol]):
    val forClass = ownerSym != modSym
    val suffix = "$" + scope.allocateOrGetName(ownerSym)
    val cacheNme = (if forClass then "class$" else "") + "cache" + suffix
    val generatorMapNme = (if forClass then "class$" else "") + "generatorMap" + suffix

  def stageMethods(cfg: StagingCfg)(methods: Ls[FunDefn]): (FunDefn, Ls[FunDefn], Block => Block) =
    import cfg._
    // for storing specialized functions in each staged module
    val cacheSym = BlockMemberSymbol(cacheNme, Nil, true)
    val cacheTsym = TermSymbol(syntax.ImmutVal, S(modSym), Tree.Ident(cacheNme))
    val cachePath = modSym.asPath.selSN(cacheNme)
    val generatorMapSym = BlockMemberSymbol(generatorMapNme, Nil, true)
    val generatorMapTsym = TermSymbol(syntax.ImmutVal, S(modSym), Tree.Ident(generatorMapNme))

    // TODO: remove generator function for ctor, we only need the staged function
    val (stagedMethods, generatorMethods, generatorEntries) = methods.map(f =>
      val staged = stageMethod(f)
      val stagedPath = modSym.asPath.selSN(staged.sym.nme)
      val gen = genMethod(cachePath, forClass)(f, stagedPath)

      (
        staged,
        gen,
        tuple(Ls(toValue(f.sym.nme), modSym.asPath.selSN(gen.sym.nme)))
      )
    ).unzip3
    val reservedNames = getDefn(ownerSym) match
      case ownerDefn: semantics.ClassLikeDef =>
        val ownerParamNames = (ownerDefn.paramsOpt.toList ++ ownerDefn.auxParams)
          .flatMap(_.params.map(_.sym.nme))
        (ownerDefn.body.members.keys.toList ++ ownerParamNames).distinct
      case ownerDefn: ClsLikeDefn =>
        val ownerParamNames = (ownerDefn.paramsOpt.toList ++ ownerDefn.auxParams)
          .flatMap(_.params.map(_.sym.nme))
        val ownerFieldNames = ownerDefn.publicFields.map(_._1.nme) ++ ownerDefn.privateFields.map(_.nme)
        (ownerDefn.methods.map(_.sym.nme) ++ ownerFieldNames ++ ownerParamNames).distinct
    val reservedNameValues = reservedNames.map(name => (k: Path => Block) => k(toValue(name)))

    // initialize cache for the module
    def cacheDecl(rest: Block) =
      val pOpt = if !forClass then S(ownerSym.asThis) else N
      
      transformSymbol(ownerSym, pOpt = pOpt)(using Context(false)): (stagedSym, _) =>
        ctor(State.globalThisSymbol.asPath.selSN("Map"), Nil): cacheMap =>
          reservedNameValues.collectApply: defs =>
            tuple(defs): reservedNames =>
              ctor(State.globalThisSymbol.asPath.selSN("Set"), Ls(reservedNames)): nameSet =>
                ctor(helperMod("FunCache"), Ls(stagedSym, cacheMap, nameSet)): funCache =>
                  Define(ValDefn(cacheTsym, cacheSym, funCache)(N, Nil), rest)

    def generatorMapDecl(rest: Block) =
      generatorEntries.collectApply: defs =>
        tuple(defs): tup =>
          ctor(State.globalThisSymbol.asPath.selSN("Map"), Ls(tup)): map =>
            Define(ValDefn(generatorMapTsym, generatorMapSym, map)(N, Nil), rest)
    
    val propFunDef =
      val sym = BlockMemberSymbol("propagate", Nil)
      val params = PlainParamList(Nil)
      val body = call(State.shapeSetSymbol.asPath.selSN("mkDyn"), Nil, isMlsFun = true, symName = "tmp_dyn"): dynVal =>
        def callGenCont(rest: Block) =
          generatorMethods.foldRight(rest)((gen, rest) =>
            val genPath = modSym.asPath.selSN(gen.sym.nme)
            val params = gen.params.map(_.params.map(_ => dynVal))
            params.foldRight((_: Path) => rest)
              ((args, k) => call(_, args, true, "gen_call")(k))
              (genPath)
          )
        nestedPropagates.foldRight(callGenCont(End()))((path, rest) =>
          call(path.selSN("propagate"), Nil, isMlsFun = true, symName = "tmp")(_ => rest)
        )
      FunDefn.withFreshSymbol(S(modSym), sym, params :: Nil, body)(N, Nil)

    def genOutputBody(sourceSym: VarSymbol, psym: VarSymbol) =
      call(modSym.asPath.selSN(propFunDef.sym.nme), Nil, true, "tmp"): _ =>
        tuple(codegenClasses): codegenClasses =>
          call(blockMod("codegen"), Ls(toValue(modSym.nme), cachePath, sourceSym, psym, codegenClasses), true, "tmp")(_ => End())
    val entryFunDef =
      val sym = BlockMemberSymbol("generate", Nil)
      val sourceSym = VarSymbol(Ident("source"))
      val psym = VarSymbol(Ident("path"))
      val params = PlainParamList(Param.simple(sourceSym) :: Param.simple(psym) :: Nil)
      FunDefn.withFreshSymbol(S(modSym), sym, params :: Nil, genOutputBody(sourceSym, psym))(N, Nil)
    
    val toCodeDef =
      val sym = BlockMemberSymbol("toCode", Nil)
      val params = PlainParamList(Nil)
      val body = tuple(codegenClasses): codegenClasses =>
        call(blockMod("toCode"), Ls(toValue(modSym.nme), cachePath, codegenClasses), true, "tmp")(Return(_))
      FunDefn.withFreshSymbol(S(modSym), sym, params :: Nil, body)(N, Nil)

    // grab all defn seen so far
    // TODO: this could be reduced to only contain all the symbols used within the module
    val previousStageValues = if forClass then Nil else
      scope.getBindings.toList.collect[(ClassSymbol | ModuleOrObjectSymbol, String)]({ // FIXME: this `toList` should be removed, but now we lose some of the values without it.
        case (m: ModuleOrObjectSymbol, s) if m != State.unitSymbol && m != ownerSym => (m, s)
        case (c: ClassSymbol, s) if !Elaborator.ctx.builtins.virtualClasses(c) && c != ownerSym => (c, s)
      }).map((key, nme) =>
        val name = nme + "$" + scope.allocateOrGetName(ownerSym)
        val tsym = TermSymbol(syntax.ImmutVal, S(modSym), Tree.Ident(name))
        val sym = BlockMemberSymbol(name, Nil)

        // reconstructs the Path from the top-level to the current symbol
        // TODO: we may be able to avoid matching on PatternDef if we kept a map from the symbol to its elaborated path during instrumentation of the symbol
        def reconstruct(s: DefinitionSymbol[? <: ModuleOrObjectDef | ClassDef] & InnerSymbol): Path =
          s.defn.orElse(defnMap.get(key)) match
            case S(defn) =>
              val owner: Option[InnerSymbol] = defn match
                case l: (ModuleOrObjectDef | ClassDef) => l.owner
                case l: ClsLikeDefn => l.owner
                case pd: PatternDef =>
                  raise(ErrorReport(msg"Unexpected PatternDef when constructing full path of symbol." -> pd.toLoc :: Nil))
                  N
              owner match
              case S(owner: DefinitionSymbol[ModuleOrObjectDef | ClassDef]) =>
                Select(reconstruct(owner), Tree.Ident(s.nme))(N)
              case N => defn match
                case l: (ModuleOrObjectDef | ClassDef) => Value.MemberRef(l.bsym, s)
                case l: ClsLikeDefn => Value.MemberRef(l.sym, s)
                case pd: PatternDef =>
                  raise(ErrorReport(msg"Unexpected PatternDef when constructing full path of symbol." -> pd.toLoc :: Nil))
                  Value.Lit(Tree.UnitLit(false))
            case N =>
              // TODO: get this case to trigger, where the symbol has no definition and isn't collected in defnMap
              raise(ErrorReport(msg"Cannot recover definition from symbol" -> s.toLoc :: Nil))
              Value.This(s)
        (tsym, sym, reconstruct(key))
      )

    def previousStageDecl(b: Block) =
      previousStageValues.iterator.foldRight(b)({ case ((tsym, sym, key), acc) =>
        Define(ValDefn(tsym, sym, key)(N, Nil), acc)
      })
    
    (entryFunDef, propFunDef :: toCodeDef :: stagedMethods ++ generatorMethods, b => cacheDecl(generatorMapDecl(previousStageDecl(b))))

  override def applyObjBody(companion: ClsLikeBody) =
    if companion.isStaged then
      // staged modules
      val (sym, ctor, methods) = (companion.isym, companion.ctor, companion.methods)
      // avoid name clash of cache and generator map for derived staged classes
      val modSym = sym
      val ctorFun = FunDefn.withFreshSymbol(S(modSym), BlockMemberSymbol("ctor$", Nil, false), Ls(PlainParamList(Nil)), ctor)(N, Nil)
      val newCtorFun = stageCtor(ctorFun)

      // collect top-level staged classes to be printed in the next stage
      class UsedStagedClassesCollector extends BlockTraverser:
        val used: HashSet[BlockMemberSymbol] = new HashSet()
        override def applySymbol(sym: Symbol) = sym match
          case c: ClassSymbol if c.defn.exists(defn => defn.hasStagedModifier.isDefined && defn.owner.isEmpty) =>
            used += c.defn.get.bsym
          case _ => ()
      val collector = (new UsedStagedClassesCollector)
      collector.applyCompanionModule(companion)
      val codegenClasses = collector.used

      val defn = sym.defn match
        case S(defn) => defn
        case N => raise(ErrorReport(msg"No definition found for staged module." -> sym.toLoc :: Nil)); return companion
      val nestedPropagates = defn.body.blk.stats.collect:
        case cls: ClassDef if cls.hasStagedModifier.isDefined =>
          modSym.asPath.sel(Tree.Ident(cls.sym.nme), cls.sym)
      
      val cfg = new StagingCfg(companion.isym, modSym, nestedPropagates, codegenClasses.toList)
      val (entryFun, newMethods, cont) = stageMethods(cfg)(methods)

      companion.copy(
        methods = entryFun :: newCtorFun :: newMethods,
        ctor = Begin(applyBlock(companion.ctor), cont(End())),
      )
    else super.applyObjBody(companion)

  // lazy is needed for ctx.builtins.Function
  lazy val firstClassFunc = State.globalThisSymbol.asThis.sel(Tree.Ident("Function"), ctx.builtins.Function)

  override def applyBlock(b: Block): Block = b match
    // Lifter adds private variables after lifting function classes after FirstClassFunctionTransformer, but we need the variables to be public for staging
    case Define(defn: ClsLikeDefn, rest) if defn.isStaged && defn.parentPath.exists(_ == firstClassFunc) && !defn.sym.nameIsMeaningful && !defn.privateFields.isEmpty => 
      (new DataClassTransformer).applyClsLikeDefn(defn): defn =>
        applyBlock(Define(defn, rest))
    // staged classes
    case Define(defn: ClsLikeDefn, rest) if defn.isStaged =>
      if !defn.privateFields.isEmpty then
        raise(ErrorReport(msg"Staged classes with private fields are not supported." -> defn.sym.toLoc :: Nil))
        return End()
      
      // stage the companion module first, to avoid staging the new functions we add to the companion module
      val companion = defn.companion.map(applyObjBody).getOrElse(ClsLikeBody.empty(Tree.Ident(defn.sym.nme)))
      
      def replaceSuper(parentPath: Path) = new BlockTransformer(SymbolSubst.Id):
        override def applyResult(r: Result)(k: Result => Block) = super.applyResult(r):
          case Call(Value.SimpleRef(sym: BuiltinSymbol), args) if sym.nme == "super" => k(Call(parentPath, args)(CallMetadata.defaultMlsFun))
          case r => k(r)
      val preCtor = defn.parentPath match
        case S(parent) => replaceSuper(parent).applyBlock(defn.preCtor)
        case N => defn.preCtor
      
      val (sym, ctor, ctorParams, methods) =
        val ctorParams = defn.paramsOpt match
          case S(ps) => ps :: defn.auxParams
          case N => defn.auxParams
        (defn.sym, defn.ctor, ctorParams, defn.methods)
      
      val modSym = companion.isym

      val preCtorFun = FunDefn.withFreshSymbol(S(modSym), BlockMemberSymbol("preCtor$", Nil, false), ctorParams, preCtor)(N, Nil)
      val ctorFun = FunDefn.withFreshSymbol(S(modSym), BlockMemberSymbol("class$ctor$", Nil, false), ctorParams, ctor)(N, Nil)
      val newPreCtorFun = stageCtor(preCtorFun)
      val newCtorFun = stageCtor(ctorFun)
      
      val cfg = new StagingCfg(defn.isym, modSym, Nil, Nil)
      val (entryFun, newMethods, cont) = stageMethods(cfg)(methods)
      val (companionEntryFun, companionMethods) = companion.methods.partition(_.sym.nme == "generate")
      val combinedEntryFun: FunDefn = companionEntryFun match
        case Nil => entryFun
        case companionFun :: Nil =>
          val symMap = entryFun.params.flatMap(_.params.map(_.sym))
            .zip(companionFun.params.flatMap(_.params.map(_.sym)))
            .toMap
          val paramRewrite = new BlockTransformer(VarSymSubst(symMap))
          val combinedBody = Begin(companionFun.body, paramRewrite.applyBlock(entryFun.body))
          companionFun.copy(body = combinedBody)(companionFun.configOverride, companionFun.annotations)
        case _ =>
          raise(ErrorReport(msg"There shouldn't be more than one entry function generated in a module." -> N :: Nil))
          entryFun
      
      // used for staging classes inside modules
      val newCompanion = companion.copy(
        methods = combinedEntryFun :: newPreCtorFun :: newCtorFun :: newMethods ++ companionMethods,
        ctor = Begin(companion.ctor, cont(End())),
      )
      val newModule = defn.copy(sym = sym, companion = S(newCompanion), ctor = applyBlock(ctor))(defn.configOverride, defn.annotations.filter:
        case Annot.Modifier(Keyword.`staged`) => false
        case _ => true)
      Define(newModule, applyBlock(rest))
    case b => super.applyBlock(b)

  def mkDefnMap(b: Block): Unit =
    val transformer = new BlockTraverser:
      override def applyDefn(defn: Defn) = defn match
        case c: ClsLikeDefn =>
          defnMap.addOne(c.isym, c)
          super.applyDefn(defn)
        case _ => super.applyDefn(defn)
    transformer.applyBlock(b)

  def apply(b: Block) =
    mkDefnMap(b)
    applyBlock(b)
