package hkmc2
package codegen

import utils.*
import hkmc2.Message.MessageContext

import scala.collection.mutable.HashMap
import scala.util.chaining._

import mlscript.utils.*, shorthands.*

import semantics.*
import semantics.Elaborator.State

import syntax.{Literal, Tree}

// it should be possible to cache some common constructions (End, Option) into the context
// this avoids having to rebuild the same shapes everytime they are needed

// transform Block to Block IR so that it can be instrumented in mlscript
class InstrumentationImpl(using State, Raise):
  type ArgWrappable = Path | Symbol
  type Context = HashMap[Path, Path]
  // TODO: there could be a fresh scope per function body, instead of a single one for the entire program
  val scope = Scope.empty(Scope.Cfg.default)

  def asArg(x: ArgWrappable): Arg =
    x match
    case p: Path => p.asArg
    case l: Symbol => l.asPath.asArg

  // null and undefined are missing
  def toValue(lit: Str | Int | BigDecimal | Bool): Value =
    val l = lit match
    case i: Int => Tree.IntLit(i)
    case b: Bool => Tree.BoolLit(b)
    case s: Str => Tree.StrLit(s)
    case n: BigDecimal => Tree.DecLit(n)
    Value.Lit(l)

  extension [A, B](ls: Ls[(A => B) => B])
    def collectApply(f: Ls[A] => B): B =
      // defer applying k while prepending new elements to the list
      ls.foldRight((_: Ls[A] => B)(Nil))((headCont, tailCont) =>
        k =>
          headCont: head =>
            tailCont: tail =>
              k(head :: tail)
      )(f)

  // helpers for constructing Block

  def assign(res: Result, symName: Str = "tmp")(k: Path => Block): Block =
    // TODO: skip assignment if res: Path?
    val sym = new TempSymbol(N, symName)
    Scoped(Set(sym), Assign(sym, res, k(sym.asPath)))

  def tuple(elems: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    assign(Tuple(false, elems.map(asArg)), symName)(k)

  def ctor(cls: Path, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    assign(Instantiate(false, cls, args.map(asArg)), symName)(k)

  // isMlsFun is probably always true?
  def call(fun: Path, args: Ls[ArgWrappable], isMlsFun: Bool = true, symName: Str = "tmp")(k: Path => Block): Block =
    assign(Call(fun, args.map(asArg))(isMlsFun, false, false), symName)(k)

  // helpers for instrumenting Block

  def blockMod(name: Str) = summon[State].blockSymbol.asPath.selSN(name)
  def optionMod(name: Str) = summon[State].optionSymbol.asPath.selSN(name)

  def blockCtor(name: Str, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    ctor(blockMod(name), args, symName)(k)
  def optionSome(arg: ArgWrappable, symName: Str = "tmp")(k: Path => Block): Block =
    ctor(optionMod("Some"), Ls(arg), symName)(k)
  def optionNone(symName: Str = "tmp")(k: Path => Block): Block =
    assign(optionMod("None"), symName)(k)

  def blockCall(name: Str, args: Ls[ArgWrappable], symName: Str = "tmp")(k: Path => Block): Block =
    call(blockMod(name), args, symName = symName)(k)

  // linking functions defined in MLscipt

  def fnPrintCode(p: Path)(k: Block): Block =
    // discard result, we only care about side effect
    blockCall("printCode", Ls(p))(_ => k)

  def fnConcat(p1: Path, p2: Path, symName: String = "concat")(k: Path => Block): Block =
    blockCall("concat", Ls(p1, p2), symName)(k)

  // transformation helpers

  def transformSymbol(sym: Symbol, symName: Str = "sym")(k: Path => Block): Block =
    sym match
    case clsSym: ClassSymbol =>
      clsSym.defn match
      case S(defn) =>
        val name = scope.allocateOrGetName(sym)
        transformParamsOpt(defn.paramsOpt): paramsOpt =>
          blockCtor("ClassSymbol", Ls(toValue(name), paramsOpt), symName)(k)
      case N =>
        raise(ErrorReport(msg"Unable to infer parameters from ClassSymbol in staged module, which are necessary to reconstruct class instances." -> sym.toLoc :: Nil))
        End()
    case t: TermSymbol if t.defn.exists(_.sym.asCls.isDefined) =>
      transformSymbol(t.defn.get.sym.asCls.get, symName)(k)
    case _: BuiltinSymbol =>
      // retain names to built-in functions
      blockCtor("Symbol", Ls(toValue(sym.nme)), symName)(k)
    case _ =>
      val name = scope.allocateOrGetName(sym)
      blockCtor("Symbol", Ls(toValue(name)), symName)(k)

  def transformOption[A](xOpt: Opt[A], f: A => (Path => Block) => Block)(k: Path => Block): Block =
    xOpt match
    case S(x) => f(x)(optionSome(_)(k))
    case N => optionNone()(k)

  // instrumentation rules

  def ruleEnd(symName: String = "end")(k: Path => Block): Block =
    blockCtor("End", Ls(), symName)(k)

  def ruleBranches(x: Path, p: Path, arms: Ls[Case -> Block], dflt: Opt[Block], symName: String = "branches")(using Context)(k: (Path, Context) => Block): Block =
    def applyRuleBranch(cse: Case, block: Block)(f: Path => Context => Block)(ctx: Context): Block =
      transformCase(cse): cse =>
        transformBlock(block)(using ctx.clone() += p -> x): (y, ctx) =>
          // TODO: use Arm type instead of Tup
          tuple(Ls(cse, y), "branch"): cde =>
            f(cde)(ctx.clone() -= p)

    (arms.map(applyRuleBranch).collectApply(_: Ls[Path] => Context => Block)(summon)): arms =>
      ctx =>
        tuple(arms): arms =>
          ruleEnd(): e =>
            // TODO: use transformOption here
            def dfltStaged(k: (Path, Context) => Block) =
              dflt match
              case S(dflt) =>
                transformBlock(dflt)(using ctx.clone() += p -> x): (dflt, ctx) =>
                  optionSome(dflt)(k(_, ctx.clone() -= p))
              case N => optionNone()(k(_, ctx))
            dfltStaged: (dflt, ctx) =>
              blockCtor("Match", Ls(x, arms, dflt, e), symName)(k(_, ctx))

  // transformations of Block

  def transformPath(p: Path)(using ctx: Context)(k: Path => Block): Block =
    // rulePath
    ctx.get(p).map(k).getOrElse:
      p match
      case Value.Ref(l, disamb) =>
        transformSymbol(disamb.getOrElse(l)): sym =>
          blockCtor("ValueRef", Ls(sym), "var")(k)
      case l: Value.Lit =>
        blockCtor("ValueLit", Ls(l), "lit")(k)
      case s @ Select(p, Tree.Ident(name)) =>
        transformPath(p): x =>
          val sym = s.symbol.map(transformSymbol(_))
            .getOrElse(blockCtor("Symbol", Ls(toValue(name))))
          sym: sym =>
            blockCtor("Select", Ls(x, sym), "sel")(k)
      case DynSelect(qual, fld, arrayIdx) =>
        transformPath(qual): x =>
          transformPath(fld): y =>
            blockCtor("DynSelect", Ls(x, y, toValue(arrayIdx)), "dynsel")(k)
      case _: Value.This =>
        raise(ErrorReport(msg"Value.This not supported in staged module." -> p.toLoc :: Nil))
        End()

  def transformResult(r: Result)(using Context)(k: Path => Block): Block =
    r match
    case p: Path => transformPath(p)(k)
    case Tuple(mut, elems) =>
      assert(!mut, "mutable tuple not supported")
      transformArgs(elems): xs =>
        tuple(xs.map(_._1)): codes =>
          blockCtor("Tuple", Ls(codes), "tup")(k)
    case Instantiate(mut, cls, args) =>
      assert(!mut, "mutable instantiation not supported")
      transformArgs(args): xs =>
        transformPath(cls): cls =>
          tuple(xs.map(_._1)): codes =>
            blockCtor("Instantiate", Ls(cls, codes), "inst")(k)
    case Call(fun, args) =>
      val stagedFunPath =
        fun match
        case s @ Select(qual, Tree.Ident(name)) => s.symbol.flatMap({
            case t: TermSymbol => t.owner.flatMap({ case sym: DefinitionSymbol[?] =>
                sym.defn.flatMap(_.hasStagedModifier.map(_ =>
                  Select(qual, Tree.Ident(name + "_gen"))(N)
                ))
              })
            case _ => N
          })
        case _ => N

      val newFun = stagedFunPath.getOrElse(fun)
      transformPath(newFun): fun =>
        transformArgs(args): args =>
          tuple(args.map(_._1)): tup =>
            blockCtor("Call", Ls(fun, tup), "app")(k)
    case _ =>
      raise(ErrorReport(msg"Other Results not supported in staged module: ${r.toString()}" -> r.toLoc :: Nil))
      End()

  def transformArg(a: Arg)(using Context)(k: ((Path, Bool)) => Block): Block =
    val Arg(spread, value) = a
    if spread.isDefined then
      raise(ErrorReport(msg"Spread parameters are not supported in staged module: ${a.toString()}" -> N :: Nil))
      End()
    else
      transformPath(value): value =>
        blockCtor("Arg", Ls(value)): cde =>
          k(cde, spread.isDefined)

  def transformArgs(args: Ls[Arg])(using Context)(k: Ls[(Path, Bool)] => Block): Block =
    args.map(transformArg).collectApply(k)

  def transformParamList(ps: ParamList)(k: Path => Block) =
    ps.params.map(p => transformSymbol(p.sym)).collectApply(tuple(_)(k))

  def transformParamsOpt(pOpt: Opt[ParamList])(k: Path => Block) =
    transformOption(pOpt, transformParamList)(k)

  def transformCase(cse: Case)(using Context)(k: Path => Block): Block =
    cse match
    case Case.Lit(lit) => blockCtor("Lit", Ls(Value.Lit(lit)))(k)
    case Case.Cls(cls, path) =>
      transformSymbol(cls): cls =>
        transformPath(path): path =>
          blockCtor("Cls", Ls(cls, path))(k)
    case Case.Tup(len, true) =>
      raise(ErrorReport(msg"Spread parameters are not supported in staged module: ${cse.toString()}" -> N :: Nil))
      End()
    case Case.Tup(len, false) =>
      blockCtor("Tup", Ls(toValue(len)))(k)
    case Case.Field(name, safe) =>
      raise(ErrorReport(msg"Case.Field not supported in staged module." -> name.toLoc :: Nil))
      End()

  def transformBlock(b: Block)(using Context)(k: Path => Block): Block =
    transformBlock(b)((p, _) => k(p))

  def transformBlock(b: Block)(using ctx: Context)(k: (Path, Context) => Block): Block =
    b match
    case Return(res, implct) =>
      transformResult(res): x =>
        blockCtor("Return", Ls(x, toValue(implct)), "return")(k(_, ctx))
    case Assign(x, r, b) =>
      transformResult(r): y =>
        transformSymbol(x): xSym =>
          blockCtor("ValueRef", Ls(xSym)): xStaged =>
            (Assign(x, xStaged, _)):
              given Context = ctx.clone() += x.asPath -> xStaged
              transformBlock(b): (z, ctx) =>
                blockCtor("Assign", Ls(xSym, y, z), "assign")(k(_, ctx))
    case Define(cls: ClsLikeDefn, rest) =>
      assert(cls.companion.isEmpty, "nested module not supported")
      transformBlock(rest): p =>
        transformSymbol(cls.isym): c =>
          // staging the methods within the module
          cls.methods.map(transformFunDefn).collectApply: methods =>
            tuple(methods): methods =>
              optionNone(): none => // TODO: handle companion object
                blockCtor("ClsLikeDefn", Ls(c, methods, none)): cls =>
                  blockCtor("Define", Ls(cls, p))(k(_, ctx))
    case End(_) => ruleEnd()(k(_, ctx))
    case Match(p, ks, dflt, rest) =>
      transformPath(p): x =>
        ruleBranches(x, p, ks, dflt): (stagedMatch, ctx) =>
          transformBlock(rest)(using ctx): (z, ctx) =>
            fnConcat(stagedMatch, z, "match")(k(_, ctx))
    case Begin(sub, rest) =>
      // TODO: This is untested as there is no test case that generates the Begin block yet
      transformBlock(sub): (sub, ctx) =>
        transformBlock(rest)(using ctx): (rest, ctx) =>
          fnConcat(sub, rest)(k(_, ctx))
    case Scoped(syms, body) =>
      syms.toList.map(transformSymbol(_)).collectApply: symsStaged =>
        tuple(symsStaged): tup =>
          transformBlock(body): (body, ctx) =>
            blockCtor("Scoped", Ls(tup, body))(b => Scoped(syms, k(b, ctx)))
    case Label(labelSymbol, loop, body, rest) =>
      transformSymbol(labelSymbol): labelSymbol =>
        transformBlock(body): (body, ctx) =>
          transformBlock(rest)(using ctx): (rest, ctx) =>
            blockCtor("Label", Ls(labelSymbol, toValue(loop), body, rest))(k(_, ctx))
    case Break(labelSymbol) =>
      transformSymbol(labelSymbol): labelSymbol =>
        blockCtor("Break", Ls(labelSymbol))(k(_, ctx))
    case _ =>
      raise(ErrorReport(msg"Other Blocks not supprted in staged module: ${b.toString()}" -> N :: Nil))
      End()

  def transformFunDefn(f: FunDefn)(using Context)(k: Path => Block): Block =
    transformBlock(f.body): body =>
      if f.params.length != 1 then
        raise(WarningReport(msg"Multiple parameter lists are not supported in shape propagation yet." -> f.sym.toLoc :: Nil))
      // maintain parameter names in instrumented code
      f.params.map(
        _.params.map(p => blockCtor("Symbol", Ls(toValue(p.sym.nme)))).collectApply
      ).collectApply: paramListSyms =>
        blockCtor("Symbol", Ls(toValue(f.sym.nme))): sym =>
          paramListSyms.map(tuple(_)).collectApply: tups =>
            tuple(tups): tup =>
              blockCtor("FunDefn", Ls(sym, tup, body, toValue(true)))(k)

  def applyFunDefn(f: FunDefn): (FunDefn, Block => Block) =
    val genSymName = f.sym.nme + "_instr"
    val genSym = BlockMemberSymbol(genSymName, Nil, false)
    val sym = f.owner.get.asPath.selSN(genSymName)

    // turn into fundefn
    val dSym = TermSymbol(f.dSym.k, f.dSym.owner, Tree.Ident(f.sym.nme + "_instr"))
    val argSyms = f.params.flatMap(_.params).map(_.sym)
    val newBody = Scoped(Set(argSyms*), transformFunDefn(f)(using new HashMap)(Return(_, false)))

    // TODO: remove it. only for test
    val debug = (k: Block) => call(sym, Nil)(fnPrintCode(_)(k))
    val newFun = f.copy(sym = genSym, dSym = dSym, params = Ls(PlainParamList(Nil)), body = newBody)(false)
    (newFun, debug)

// TODO: rename as InstrumentationTransformer?
class Instrumentation(using State, Raise) extends BlockTransformer(new SymbolSubst()):
  val impl = new InstrumentationImpl

  override def applyBlock(b: Block): Block =
    super.applyBlock(b) match
    // find modules with staged annotation
    case Define(c: ClsLikeDefn, rest) if c.companion.exists(_.isym.defn.exists(_.hasStagedModifier.isDefined)) =>
      val sym = c.sym.subst
      val companion = c.companion.get
      val (stagedMethods, debugPrintCode) = companion.methods
        .map(impl.applyFunDefn)
        .unzip
      val ctor = FunDefn.withFreshSymbol(S(companion.isym), BlockMemberSymbol("ctor$", Nil), Ls(PlainParamList(Nil)), companion.ctor)(false)
      val (stagedCtor, ctorPrint) = impl.applyFunDefn(ctor)

      val unit = State.runtimeSymbol.asPath.selSN("Unit")
      val debugBlock = (ctorPrint :: debugPrintCode).foldRight((Return(unit, true): Block))(_(_))
      def debugCont(rest: Block) =
        Begin(debugBlock, rest)
      // add generator functions for classes within the constructor
      val genCls = new BlockTransformer(new SymbolSubst()):
        override def applyBlock(b: Block): Block = super.applyBlock(b) match
        case Define(c: ClsLikeDefn, rest) if c.companion.isEmpty =>
          val (stagedMethods, debugPrintCode) = c.methods
            .map(impl.applyFunDefn)
            .unzip
          val newModule = c.copy(methods = c.methods ++ stagedMethods)
          Define(newModule, rest)
        case b => b
      val newCtor = genCls.applyBlock(companion.ctor)
      val newCompanion = companion.copy(methods = stagedCtor :: companion.methods ++ stagedMethods, ctor = newCtor.mapTail(debugCont))
      val newModule = c.copy(sym = sym, companion = S(newCompanion))
      Define(newModule, rest)
    case b => b
