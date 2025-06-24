package hkmc2
package semantics


import scala.collection.mutable
import scala.annotation.tailrec
import scala.language.implicitConversions

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.*
import Tree.*
import Term.{ Blk, Rcd }
import hkmc2.Message.MessageContext

import Keyword.{`let`, `set`}


object Elaborator:
  
  val binaryOps = Set(
    ",",
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "===", "!==",
    "&&", "||")
  val unaryOps = Set("-", "+", "!", "~", "typeof")
  val anyOps = Set("super")
  val builtins = binaryOps ++ unaryOps ++ anyOps
  val aliasOps = Map(
    ";" -> ",",
    "+." -> "+",
    "-." -> "-",
    "*." -> "*",
    "/." -> "/")
  private val builtinBinOps = aliasOps ++ (binaryOps.map: op =>
    op -> op).toMap

  val reservedNames = binaryOps.toSet ++ aliasOps.keySet + "NaN" + "Infinity"

  enum OuterCtx:
    case Function(returnHandlerSymbol: TempSymbol)
    case InnerScope(innerSymbol: InnerSymbol)
    case LocalScope
    case LambdaOrHandlerBlock
    case NonReturnContext

    def inner: Opt[InnerSymbol] = this match
      case InnerScope(inner) => S(inner)
      case _ => N
  
  enum ReturnHandler:
    case Required(handler: TempSymbol)
    case Direct
    case NotInFunction
    case Forbidden
  
  /** Context used to keep track of underscores representing lambda shorthands, eg in `_ + 1`. */
  // TODO later: use TempSymbol instead of VarSymbol? (currently, trying that creates lot of problems)
  class UnderCtx(val unders: Opt[mutable.ArrayBuffer[VarSymbol]])
  
  case class Ctx(outer: OuterCtx, parent: Opt[Ctx], env: Map[Str, Ctx.Elem], 
    mode: Mode):
    
    def +(local: Str -> Symbol): Ctx = copy(outer, env = env + local.mapSecond(Ctx.RefElem(_)))
    def ++(locals: IterableOnce[Str -> Symbol]): Ctx =
      copy(outer, env = env ++ locals.mapValues(Ctx.RefElem(_)))
    def elem_++(locals: IterableOnce[Str -> Ctx.Elem]): Ctx =
      copy(outer, env = env ++ locals.iterator.filter: kv =>
        // * Imports should not shadow symbols defined in the same scope;
        // * but they should be allowed to shadow previous imports.
        env.get(kv._1).forall(_.isImport))
    
    def withMembers(members: Iterable[Str -> MemberSymbol[?]], out: Opt[Symbol] = N): Ctx =
      copy(env = env ++ members.map:
        case (nme, sym) =>
          val elem = out orElse outer.inner match
            case S(outer) => Ctx.SelElem(outer, sym.nme, S(sym), isImport = false)
            case N => Ctx.RefElem(sym)
          nme -> elem
      )
    
    def nest(outerCtx: OuterCtx): Ctx = Ctx(outerCtx, Some(this), Map.empty, mode)
    def nestLocal: Ctx = nest(OuterCtx.LocalScope)
    def nestInner(inner: InnerSymbol): Ctx = nest(OuterCtx.InnerScope(inner))
    
    def get(name: Str): Opt[Ctx.Elem] =
      env.get(name).orElse(parent.flatMap(_.get(name)))
    def getOuter: Opt[InnerSymbol] = outer.inner.orElse(parent.flatMap(_.getOuter))
    def getNonLocalRetHandler: Opt[TempSymbol] = outer match
      case OuterCtx.Function(sym) => S(sym)
      case _ => parent.flatMap(_.getNonLocalRetHandler)
    def getRetHandler: ReturnHandler = outer match
      case OuterCtx.Function(sym) => ReturnHandler.Direct
      case _: (OuterCtx.LambdaOrHandlerBlock.type | OuterCtx.InnerScope) =>
        getNonLocalRetHandler.fold(ReturnHandler.NotInFunction)(ReturnHandler.Required(_))
      case OuterCtx.NonReturnContext => ReturnHandler.Forbidden
      case OuterCtx.LocalScope =>
        parent.fold(ReturnHandler.NotInFunction)(_.getRetHandler)
    
    // * Invariant: We expect that the top-level context only contain hard-coded symbols like `globalThis`
    // * and that built-in symbols like Int and Str be imported into another nested context on top of it.
    // * It should not be possible to shadow these built-in symbols, so user code should always be compiled
    // * in further nested contexts.
    lazy val preludeCtx: Ctx =
      parent match
      case N => lastWords("Cannot find prelude context.")
      case S(par) => if par.parent.isEmpty then this else par.preludeCtx
    
    // * Method `getBuiltin` is used to look up built-in symbols in the context of builtin symbols.
    def getBuiltin(nme: Str): Opt[Ctx.Elem] =
      preludeCtx.env.get(nme)
    
    lazy val builtins: Ctx#MkBuiltins = preludeCtx.MkBuiltins
    private object MkBuiltins extends MkBuiltins
    
    class MkBuiltins:
      assert(Ctx.this is preludeCtx)
      private def assumeBuiltin(nme: Str): Symbol =
        getBuiltin(nme)
          .getOrElse(throw new NoSuchElementException(s"builtin $nme not in ${parent.map(_.env.keySet)}"))
          .symbol.getOrElse(throw new NoSuchElementException(s"builtin symbol $nme"))
      private def assumeBuiltinTpe(nme: Str): TypeSymbol =
        assumeBuiltin(nme).asTpe.getOrElse(throw new NoSuchElementException(
          s"builtin type symbol $nme"))
      private def assumeBuiltinCls(nme: Str): ClassSymbol =
        assumeBuiltin(nme).asCls.getOrElse(throw new NoSuchElementException(
          s"builtin class symbol $nme"))
      private def assumeBuiltinMod(nme: Str): ModuleSymbol =
        assumeBuiltin(nme).asMod.getOrElse(throw new NoSuchElementException(
          s"builtin module symbol $nme"))
      val Unit = assumeBuiltinCls("Unit")
      val Int = assumeBuiltinCls("Int")
      val Num = assumeBuiltinCls("Num")
      val Str = assumeBuiltinCls("Str")
      val Function = assumeBuiltinCls("Function")
      val Bool = assumeBuiltinCls("Bool")
      val Object = assumeBuiltinCls("Object")
      val untyped = assumeBuiltinTpe("untyped")
      // println(s"Builtins: $Int, $Num, $Str, $untyped")
      class VirtualModule(val module: ModuleSymbol):
        val bms = getBuiltin(module.nme) match
          case S(Ctx.RefElem(bms: BlockMemberSymbol)) => bms
          case huh => wat(huh)
        protected def assumeObject(nme: Str): BlockMemberSymbol =
          module.tree.definedSymbols.get(nme).getOrElse:
            throw new NoSuchElementException(
              s"builtin module symbol source.$nme")
      object source extends VirtualModule(assumeBuiltinMod("source")):
        val line = assumeObject("line")
        val name = assumeObject("name")
        val file = assumeObject("file")
      object js extends VirtualModule(assumeBuiltinMod("js")):
        val try_catch = assumeObject("try_catch")
      object debug extends VirtualModule(assumeBuiltinMod("debug")):
        val printStack = assumeObject("printStack")
        val getLocals = assumeObject("getLocals")
      object annotations extends VirtualModule(assumeBuiltinMod("annotations")):
        val compile = assumeObject("compile")
      def getBuiltinOp(op: Str): Opt[Str] =
        if getBuiltin(op).isDefined then builtinBinOps.get(op) else N
      /** Classes that do not use `instanceof` in pattern matching. */
      val virtualClasses = Set(Int, Num, Str, Bool)
  
  object Ctx:
    abstract class Elem:
      def nme: Str
      def ref(id: Tree.Ident)(using Elaborator.State): Term
      def symbol: Opt[Symbol]
      def isImport: Bool
    final case class RefElem(sym: Symbol) extends Elem:
      val nme = sym.nme
      def ref(id: Tree.Ident)(using Elaborator.State): Term =
        // * Note: due to symbolic ops, we may have `id.name =/= nme`;
        // * e.g., we can have `id.name = "|>"` and `nme = "pipe"`.
        Term.Ref(sym)(id, 666, N) // FIXME: 666 is a temporary placeholder
      def symbol = S(sym)
      def isImport: Bool = false
    final case class SelElem(base: Elem, nme: Str, symOpt: Opt[FieldSymbol], isImport: Bool) extends Elem:
      def ref(id: Tree.Ident)(using Elaborator.State): Term =
        // * Same remark as in RefElem#ref
        Term.SynthSel(base.ref(Ident(base.nme)),
          new Tree.Ident(nme).withLocOf(id))(symOpt)
      def symbol = symOpt
    given Conversion[Symbol, Elem] = RefElem(_)
    val empty: Ctx = Ctx(OuterCtx.LocalScope, N, Map.empty, Mode.Full)
    
  enum Mode:
    case Full
    case Light
  
  type Ctxl[A] = Ctx ?=> A
  
  transparent inline def ctx(using Ctx): Ctx = summon
  
  class State:
    val suid = new Uid.Symbol.State
    given State = this
    val globalThisSymbol = TopLevelSymbol("globalThis")
    // In JavaScript, `import` can be used for getting current file path, as `import.meta`
    val importSymbol = new VarSymbol(syntax.Tree.Ident("import"))
    val runtimeSymbol = TempSymbol(N, "runtime")
    val termSymbol = TempSymbol(N, "Term")
    val effectSigSymbol = ClassSymbol(DummyTypeDef(syntax.Cls), Ident("EffectSig"))
    val nonLocalRetHandlerTrm =
      val id = new Ident("NonLocalReturn")
      val sym = ClassSymbol(DummyTypeDef(syntax.Cls), id)
      Term.Sel(runtimeSymbol.ref(), id)(S(sym))
    val nonLocalRet =
      val id = new Ident("ret")
      BlockMemberSymbol(id.name, Nil, true)
    val matchResultClsSymbol =
      val id = new Ident("MatchResult")
      // val td = DummyTypeDef(syntax.Cls)
      val td = TypeDef(syntax.Cls, App(id, Tup(Ident("captures") :: Nil)), N)
      val cs = ClassSymbol(td, id)
      val flag = FldFlags.empty.copy(value = true)
      val ps = PlainParamList(Param(flag, VarSymbol(Ident("captures")), N, Modulefulness(N)(false)) :: Nil)
      cs.defn = S(ClassDef.Parameterized(N, syntax.Cls, cs, BlockMemberSymbol(cs.name, td :: Nil),
        Nil, ps, Nil, N, ObjBody(Blk(Nil, Term.Lit(UnitLit(false)))), N, Nil))
      cs
    val matchFailureClsSymbol =
      val id = new Ident("MatchFailure")
      val td = DummyTypeDef(syntax.Cls)
      val cs = ClassSymbol(td, id)
      val flag = FldFlags.empty.copy(value = true)
      val ps = PlainParamList(Param(flag, VarSymbol(Ident("errors")), N, Modulefulness(N)(false)) :: Nil)
      cs.defn = S(ClassDef.Parameterized(N, syntax.Cls, cs, BlockMemberSymbol(cs.name, td :: Nil),
        Nil, ps, Nil, N, ObjBody(Blk(Nil, Term.Lit(UnitLit(false)))), N, Nil))
      cs
    val builtinOpsMap =
      val baseBuiltins = builtins.map: op =>
          op -> BuiltinSymbol(op,
            binary = binaryOps(op),
            unary = unaryOps(op),
            nullary = false,
            functionLike = anyOps(op))
        .toMap
      baseBuiltins ++ aliasOps.map:
        case (alias, base) => alias -> baseBuiltins(base)
    val seqSymbol = TermSymbol(ImmutVal, N, Ident(";"))
    def init(using State): Ctx = Ctx.empty.copy(env = Map(
      "globalThis" -> globalThisSymbol,
    ))
    def dbg: Bool = false
    def dbgUid(uid: Uid[Symbol]): Str =
      if dbg then s"‹$uid›" else ""
      // ^ we do not display the uid by default to avoid polluting diff-test outputs
  transparent inline def State(using state: State): State = state
  
end Elaborator


import Elaborator.*


class Elaborator(val tl: TraceLogger, val wd: os.Path, val prelude: Ctx)
(using val raise: Raise, val state: State)
extends Importer:
  import tl.*
  
  def mkLetBinding(sym: LocalSymbol, rhs: Term, annotations: Ls[Annot]): Ls[Statement] =
    LetDecl(sym, annotations) :: DefineVar(sym, rhs) :: Nil
  
  def resolveField(srcTree: Tree, base: Opt[Symbol], nme: Ident): Opt[FieldSymbol] =
    base match
    case S(psym: BlockMemberSymbol) =>
      psym.modOrObjTree match
      case S(cls) =>
        cls.definedSymbols.get(nme.name) match
        case s @ S(clsSym) => s
        case N =>
          raise(ErrorReport(msg"${cls.k.desc.capitalize} '${cls.symbol.nme
            }' does not contain member '${nme.name}'" -> srcTree.toLoc :: Nil))
          S(ErrorSymbol(nme.name, srcTree))
      case N =>
        N
    case _ => N
  
  def cls(trm: Term, inAppPrefix: Bool)
      : Ctxl[Term]
      = trace[Term](s"Elab class ${trm}", r => s"~> $r"):
    trm.symbol match
    case S(cls: ClassSymbol) =>
      trm
    case S(mem: BlockMemberSymbol) =>
      // FIXME: `defn` is not available before elaboration. See pull/277#discussion_r2051448677
      if !mem.hasLiftedClass || mem.defn.exists(_.isDeclare.isDefined) then trm
      else Term.SynthSel(trm, Ident("class"))(mem.clsTree.orElse(mem.modOrObjTree).map(_.symbol))
    case _ => trm
  
  def annot(tree: Tree): Ctxl[Opt[Annot]] = tree match
    case Keywrd(kw @ (Keyword.`abstract` | Keyword.`declare` | Keyword.`data`)) => S(Annot.Modifier(kw))
    case _ => term(tree) match
      case Term.Error => N
      case trm =>
        trm.symbol match
        case S(sym) =>
          sym.asTpe match
          case S(ctx.builtins.untyped) =>
            return S(Annot.Untyped)
          case _ => ()
        case _ => ()
        S(Annot.Trm(trm))
  
  def term(tree: Tree): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    val unders = mutable.ArrayBuffer.empty[VarSymbol]
    given UnderCtx = new UnderCtx(S(unders))
    val st = subterm(tree, inAppPrefix = false, inTyAppPrefix = false)
    val params = unders.iterator.map: sym =>
        Param(FldFlags.empty, sym, N, Modulefulness.none)
      .toList
    if params.isEmpty then st
    else Term.Lam(PlainParamList(params), st)
  
  def subterm(tree: Tree, inAppPrefix: Bool = false, inTyAppPrefix: Bool = false)(using Ctx)(using UnderCtx): Term =
  trace[Term](s"Elab subterm ${tree.showDbg}", r => s"~> $r"):
    tree.desugared match
    case Trm(term) => term
    case unt @ Unt() => unit.withLocOf(unt)
    case Bra(k, e) =>
      k match
      case BracketKind.Round =>
      case BracketKind.Curly =>
      case _ =>
        raise(ErrorReport(msg"Unsupported ${k.name} in this position" -> tree.toLoc :: Nil))
      term(e) // * not `subterm` as `e` could be a lambda shorthand
    case b: Block =>
      ctx.nestLocal.givenIn:
        block(b, hasResult = true)._1 match
        case Term.Blk(Nil, res) => res
        case res => res
    case lit: Literal =>
      Term.Lit(lit)
    case d: Def =>
      subterm(Block(d :: Unt() :: Nil))
    case LetLike(`let`, lhs, rhso, S(bod)) =>
      subterm(Block(LetLike(`let`, lhs, rhso, N) :: bod :: Nil))
    case LetLike(`let`, lhs, rhso, N) =>
      raise(ErrorReport(
        msg"Expected a body for let bindings in expression position" ->
          tree.toLoc :: Nil))
      block(LetLike(`let`, lhs, rhso, N) :: Nil, hasResult = true)._1
    case LetLike(`set`, lhs, S(rhs), N) =>
      Term.Assgn(subterm(lhs), subterm(rhs))
    case LetLike(`set`, lhs, S(rhs), S(bod)) =>
      // * Backtracking assignment
      lhs match
      case id: Ident =>
        val lt = subterm(lhs)
        val sym = TempSymbol(S(lt), "old")
        Blk(
          LetDecl(sym, Nil) :: DefineVar(sym, lt) :: Nil, Term.Try(Blk(
            Term.Assgn(lt, subterm(rhs)) :: Nil,
            subterm(bod),
        ), Term.Assgn(lt, sym.ref(id))))
      case _ => ??? // TODO error
    case (hd @ Hndl(id: Ident, c, Block(sts_), S(bod))) => ctx.nest(OuterCtx.LambdaOrHandlerBlock).givenIn:
      
      val sym = fieldOrVarSym(HandlerBind, id)
      log(s"Processing `handle` statement $id (${sym}) ${ctx.outer}")
      
      val derivedClsSym = ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident(s"Handler$$${id.name}$$"))
      derivedClsSym.defn = S(ClassDef(
        N, syntax.Cls, derivedClsSym,
        BlockMemberSymbol(derivedClsSym.name, Nil),
        Nil, Nil, N, ObjBody(Blk(Nil, Term.Lit(Tree.UnitLit(false)))), List()))
      
      val elabed = ctx.nestInner(derivedClsSym).givenIn:
        block(sts_, hasResult = false)._1
      
      elabed.res match
      case Term.Lit(UnitLit(false)) => 
      case trm => raise(WarningReport(msg"Terms in handler block do nothing" -> trm.toLoc :: Nil))
      
      val tds = elabed.stats.map {
          case td @ TermDefinition(owner, Fun, sym, params, tparams, sign, body, resSym, flags, mf, annotations) =>
            params.reverse match
              case ParamList(_, value :: Nil, _) :: newParams =>
                val newTd = TermDefinition(owner, Fun, sym, newParams.reverse, tparams, sign, body, resSym, flags, mf, annotations)
                S(HandlerTermDefinition(value.sym, newTd))
              case _ => 
                raise(ErrorReport(msg"Handler function is missing resumption parameter" -> td.toLoc :: Nil))
                None
              
          case st => 
            raise(ErrorReport(msg"Only function definitions are allowed in handler blocks" -> st.toLoc :: Nil))
            None
        }.collect { case Some(x) => x }
      
      val (cp, p) = c match
        case App(c, Tup(params)) =>
          (cls(subterm(c), inAppPrefix = true), params.map(subterm(_)))
        case c =>
          (cls(subterm(c), inAppPrefix = false), Nil)
      
      (ctx + (id.name -> sym)).givenIn:
        Term.Handle(sym, cp, p, derivedClsSym, tds, subterm(bod))
    case h: Hndl =>
      raise(ErrorReport(
        msg"Unsupported handle binding shape" ->
          h.toLoc :: Nil))
      Term.Error
    case id @ Ident("this") =>
      ctx.getOuter match
      case S(sym) => sym.ref(id)
      case N =>
        raise(ErrorReport(msg"Cannot use 'this' outside of an object scope." -> tree.toLoc :: Nil))
        Term.Error
    case id @ Ident(name) =>
      ctx.get(name) match
      case S(elem) => elem.ref(id)
      case N =>
        state.builtinOpsMap.get(name) match
        case S(bi) => bi.ref(id)
        case N =>
          raise(ErrorReport(msg"Name not found: $name" -> tree.toLoc :: Nil))
          Term.Error
    case TyApp(lhs, targs) =>
      Term.TyApp(subterm(lhs, inTyAppPrefix = true), targs.map {
        case Modified(Keyword.`in`, inLoc, arg) => Term.WildcardTy(S(subterm(arg)), N)
        case Modified(Keyword.`out`, outLoc, arg) => Term.WildcardTy(N, S(subterm(arg)))
        case Tup(Modified(Keyword.`in`, inLoc, arg1) :: Modified(Keyword.`out`, outLoc, arg2) :: Nil) =>
          Term.WildcardTy(S(subterm(arg1)), S(subterm(arg2)))
        case arg => subterm(arg)
      })(N)
    case InfixApp(TyTup(tvs), Keyword.`->`, body) =>
      val boundVars = mutable.HashMap.empty[Str, VarSymbol]
      def genSym(id: Tree.Ident) =
        val sym = VarSymbol(id)
        sym.decl = S(TyParam(FldFlags.empty, N, sym)) // TODO vce
        boundVars += id.name -> sym
        sym
      val syms = (tvs.collect:
        case id: Tree.Ident => (genSym(id), N, N)
        case InfixApp(id: Tree.Ident, Keyword.`extends`, ub) => (genSym(id), S(ub), N)
        case InfixApp(id: Tree.Ident, Keyword.`restricts`, lb) => (genSym(id), N, S(lb))
        case InfixApp(InfixApp(id: Tree.Ident, Keyword.`extends`, ub), Keyword.`restricts`, lb) => (genSym(id), S(ub), S(lb))
      )
      val outer = (tvs.collect:
        case Outer(S(name: Tree.Ident)) => genSym(name)
        case Outer(N) => genSym(Tree.Ident("outer"))
      ) match
        case ot :: Nil => S(ot)
        case _ :: rest =>
          raise(ErrorReport(msg"Only one outer variable can be bound." -> tree.toLoc :: Nil))
          N
        case Nil => N
      
      if syms.length + outer.count(_ => true) != tvs.length then
        raise(ErrorReport(msg"Illegal forall annotation." -> tree.toLoc :: Nil))
        Term.Error
      else
        given Ctx = ctx ++ boundVars
        val bds = syms.map:
          case (sym, ub, lb) =>
            QuantVar(sym, ub.map(ub => subterm(ub)), lb.map(lb => subterm(lb)))
        Term.Forall(bds, outer, subterm(body))
    case InfixApp(lhs, Keyword.`->`, Effectful(eff, rhs)) =>
      Term.FunTy(subterm(lhs), subterm(rhs), S(subterm(eff)))
    case InfixApp(lhs, Keyword.`->`, rhs) =>
      Term.FunTy(subterm(lhs), subterm(rhs), N)
    case InfixApp(lhs, Keyword.`=>`, rhs) =>
      ctx.nest(OuterCtx.LambdaOrHandlerBlock).givenIn:
        val (syms, nestCtx) = params(lhs, false)
        Term.Lam(syms, term(rhs)(using nestCtx))
    case InfixApp(lhs, Keyword.`as`, rhs) =>
      Term.Asc(subterm(lhs), subterm(rhs))
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      block(tree :: Nil, hasResult = false)._1
    case tree @ InfixApp(lhs, Keyword.`is` | Keyword.`and`, rhs) =>
      val des = new ucs.Desugarer(this)(tree)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(des)}")
      Term.IfLike(Keyword.`if`, des)
    case InfixApp(lhs, kw @ (Keyword.`then` | Keyword.`with`), rhs) =>
      raise:
        ErrorReport(msg"Unexpected infix use of keyword '${kw.name}' here" -> tree.toLoc :: Nil)
      Term.Error
    case OpApp(lhs, Ident("|"), rhs :: Nil) =>
      Term.CompType(subterm(lhs), subterm(rhs), true)
    case OpApp(lhs, Ident("&"), rhs :: Nil) =>
      Term.CompType(subterm(lhs), subterm(rhs), false)
    case OpApp(lhs, Ident(":="),rhs :: Nil) =>
      Term.SetRef(subterm(lhs), subterm(rhs))
    case OpApp(Sel(pre, idn: Ident), Ident("#"), (idp: Ident) :: Nil) =>
      val c = cls(subterm(idn), inAppPrefix = false)
      val f = c.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) =>
          cls.tree.allSymbols.get(idp.name) match
          case S(fld: FieldSymbol) => S(fld)
          case _ =>
            raise(ErrorReport(msg"Class '${cls.nme}' does not contain member '${idp.name}'." -> idp.toLoc :: Nil))
            N
        case _ =>
          raise(ErrorReport(msg"Identifier `${idn.name}` does not name a known class symbol." -> idn.toLoc :: Nil))
          N
      Term.SelProj(subterm(pre), c, idp)(f)
    case App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: App(Ident(proj), args) :: Nil)) =>
      subterm(App(App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: Ident(proj) :: Nil)), args))
    case App(Ident("!"), Tree.Tup(rhs :: Nil)) =>
      Term.Deref(subterm(rhs))
    case App(Ident("~"), Tree.Tup(rhs :: Nil)) =>
      Term.Neg(subterm(rhs))
    case tree @ OpSplit(lhs, rhss) =>
      val tree = rhss.foldLeft(lhs):
        case (acc, rhs) =>
          rhs.splitOn(acc)
      subterm(tree)
    case tree @ App(lhs, rhs) =>
      val sym = FlowSymbol("‹app-res›")
      val lt = subterm(lhs, inAppPrefix = true)
      val rt = subterm(rhs)
      Term.App(lt, rt)(tree, N, sym)
    case tree @ OpApp(lhs, op, rhss) =>
      val sym = FlowSymbol("‹app-res›")
      val lt = subterm(lhs, inAppPrefix = true)
      val ot = subterm(op, inAppPrefix = true)
      val rts = rhss.map(r => PlainFld(subterm(r)))
      Term.App(ot, Term.Tup(PlainFld(lt) :: rts)(Tree.DummyTup))(
        Tree.DummyApp, N, sym)
    case SynthSel(pre, nme) =>
      val preTrm = subterm(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      Term.SynthSel(preTrm, nme)(sym)
    case Sel(pre, nme) =>
      val preTrm = subterm(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      sym match
      // * Enforcing [invariant:1]
      case S(ms: BlockMemberSymbol)
        if !inAppPrefix && ms.isParameterizedMethod && !preTrm.symbol.exists(_.isModule) =>
        raise:
          ErrorReport(
            msg"[debinding error] Method '${nme.name}' cannot be accessed without being called." -> nme.toLoc :: Nil)
      case S(_) | N => ()
      if sym.contains(ctx.builtins.source.line) then
        val loc = tree.toLoc.getOrElse(???)
        val (line, _, _) = loc.origin.fph.getLineColAt(loc.spanStart)
        Term.Lit(Tree.IntLit(loc.origin.startLineNum + line))
      else if sym.contains(ctx.builtins.source.name) then
        Term.Lit(Tree.StrLit(ctx.getOuter.map(_.nme).getOrElse("")))
      else if sym.contains(ctx.builtins.source.file) then
        val loc = tree.toLoc.getOrElse(???)
        Term.Lit(Tree.StrLit(loc.origin.fileName.toString))
      else
        Term.Sel(preTrm, nme)(sym)
    case MemberProj(ct, nme) =>
      val c = cls(subterm(ct), inAppPrefix = false)
      val f = c.symbol.flatMap(_.asCls) match
        case S(cls: ClassSymbol) =>
          cls.tree.allSymbols.get(nme.name) match
          case S(fld: FieldSymbol) => S(fld)
          case _ =>
            raise(ErrorReport(msg"Class '${cls.nme}' does not contain member '${nme.name}'." -> nme.toLoc :: Nil))
            N
        case _ =>
          raise:
            ErrorReport:
              msg"${ct.describe.capitalize} is not a known class." -> ct.toLoc ::
              msg"Note: any expression of the form `‹expression›::‹identifier›` is a member projection;" -> N ::
              msg"  add a space before ‹identifier› to make it an operator application." -> N ::
              Nil
          N
      val self = VarSymbol(Ident("self"))
      val args = VarSymbol(Ident("args"))
      val ps = ParamList(ParamListFlags.empty,
        Param(FldFlags.empty, self, N, Modulefulness.none) :: Nil,
        S:
          Param(FldFlags.empty, args, N, Modulefulness.none)
      )
      val rs = FlowSymbol("‹app-res›")
      Term.Lam(ps,
        Term.App(Term.SelProj(self.ref(), c, nme)(f), args.ref())(
          Tree.App(nme, Tree.Tup(Nil)) // FIXME
          , N, rs)
      )
    case tree @ Tup(TermDef(Ins, f, N) :: fs) =>
      Term.CtxTup((f :: fs).map(fld(_)))(tree)
    case tree @ Tup(fields) =>
      Term.Tup(fields.map(fld(_)))(tree)
    // case New(c, rfto) =>
    //   assert(rfto.isEmpty)
    //   Term.New(cls(subterm(c), inAppPrefix = inAppPrefix), params.map(subterm(_)), bodo).withLocOf(tree)
    case ProperNew(body, rfto) => // TODO handle Under
      lazy val bodo = rfto.map: rft =>
        val clsSym = new ClassSymbol(Tree.DummyTypeDef(syntax.Cls), Tree.Ident("$anon"))
        ctx.nestInner(clsSym).givenIn:
          clsSym ->
            // TODO integrate context inherited from cls
            // TODO make context with var symbols for class parameters
            ObjBody(block(rft, hasResult = false)._1)
      body match
      case S(Apps(c, argss)) =>
        Term.New(
          cls(subterm(c), inAppPrefix = true), 
          argss.map: 
            case Tup(args) =>
              args.map(subterm(_)),
          bodo
        ).withLocOf(tree)
      case S(c) => // * We'll catch bad `new` targets during type checking
        Term.New(cls(subterm(c), inAppPrefix = false), Nil, bodo).withLocOf(tree)
      case N =>
        Term.New(State.globalThisSymbol.ref().sel(Ident("Object"), S(ctx.builtins.Object)),
          Nil, bodo).withLocOf(tree)
      // case _ =>
      //   raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
    case tree @ Tree.IfLike(kw, _, split) =>
      val desugared = new ucs.Desugarer(this)(tree)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(desugared)}")
      Term.IfLike(kw, desugared)
    case Tree.Quoted(body) => Term.Quoted(subterm(body))
    case Tree.Unquoted(body) => Term.Unquoted(subterm(body))
    case tree @ Tree.Case(_, branches) =>
      val scrut = VarSymbol(Ident("caseScrut"))
      val des = new ucs.Desugarer(this)(tree, scrut)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(des)}")
      Term.Lam(PlainParamList(
          Param(FldFlags.empty, scrut, N, Modulefulness.none) :: Nil
        ), Term.IfLike(Keyword.`if`, des))
    case Modified(Keyword.`return`, kwLoc, body) =>
      ctx.getRetHandler match
      case ReturnHandler.Required(sym) =>
        tl.log(s"Non-local return: $sym")
        val rs = FlowSymbol("‹app-res›")
        val retMtdTree = new Tree.Ident("ret")
        val argTree = new Tree.Tup(body :: Nil)
        val dummyIdent = new Tree.Ident("return").withLoc(kwLoc)
        Term.App(
          Term.Sel(sym.ref(dummyIdent), retMtdTree)(S(state.nonLocalRet)),
          Term.Tup(PlainFld(subterm(body)) :: Nil)(argTree)
        )(Tree.App(Tree.Sel(dummyIdent, retMtdTree), argTree), N, rs)
      case ReturnHandler.NotInFunction =>
        raise:
          ErrorReport(msg"Return statements are not allowed outside of a function." -> tree.toLoc :: Nil)
        Term.Error
      case ReturnHandler.Direct =>
        Term.Ret(subterm(body))
      case ReturnHandler.Forbidden =>
        raise:
          ErrorReport(msg"Return statements are not allowed in this context." -> tree.toLoc :: Nil)
        Term.Error
    case Modified(Keyword.`throw`, kwLoc, body) =>
      Term.Throw(subterm(body))
    case Modified(Keyword.`do`, kwLoc, body) =>
      Blk(subterm(body) :: Nil, unit)
    case TypeDef(Mod, head, N) =>
      subterm(head)
    case Tree.Region(id: Tree.Ident, body) =>
      val sym = VarSymbol(id)
      given Ctx = ctx + (id.name -> sym)
      Term.Region(sym, subterm(body))
    case Tree.RegRef(reg, value) => Term.RegRef(subterm(reg), subterm(value))
    case Outer(S(_)) =>
      raise(ErrorReport(msg"Illegal outer binding." -> tree.toLoc :: Nil))
      Term.Error
    case Outer(N) => ctx.get("outer") match
      case S(sym) => sym.ref(Tree.Ident("outer"))
      case N =>
        raise(ErrorReport(msg"Illegal outer reference." -> tree.toLoc :: Nil))
        Term.Error
    case Empty() =>
      raise(ErrorReport(msg"A term was expected in this position, but no term was found." -> tree.toLoc :: Nil))
      Term.Error
    case Error() =>
      Term.Error
    case TermDef(k, nme, rhs) =>
      raise(ErrorReport(msg"Illegal definition in term position." -> tree.toLoc :: Nil))
      Term.Error
    case TypeDef(k, head, rhs) =>
      raise(ErrorReport(msg"Illegal type declaration in term position." -> tree.toLoc :: Nil))
      Term.Error
    case Modified(kw, kwLoc, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' modifier." -> kwLoc :: Nil))
      subterm(body)
    case Jux(lhs, rhs) =>
      def go(acc: Term, trees: Ls[Tree]): Term =
        trees match
        case Nil => acc
        
        // * FIXME this `f.name.head.isLetter` test is a big hack...
        // * TODO would be better to keep the fixity of applications part of the Tree repr.
        case (ap @ App(f: Ident, tup @ Tup(lhs :: args))) :: trees if !f.name.head.isLetter =>
          val res = go(acc, lhs :: Nil)
          val sym = FlowSymbol("‹app-res›")
          val fl = Fld(FldFlags.empty, res, N)
          val app = Term.App(subterm(f, inAppPrefix = true), Term.Tup(
            fl :: args.map(fld))(tup))(ap, N, sym)
          go(app, trees)
        case (ap @ App(f, tup @ Tup(args))) :: trees =>
          val sym = FlowSymbol("‹app-res›")
          go(Term.App(subterm(f, inAppPrefix = true),
              Term.Tup(Fld(FldFlags.empty, acc, N) :: args.map(fld))(tup)
            )(ap, N, sym), trees)
        case Block(sts) :: trees =>
          go(acc, sts ::: trees)
        case tree :: trees =>
          raise(ErrorReport(msg"Illegal juxtaposition right-hand side (${tree.describe})." -> tree.toLoc :: Nil))
          go(acc, trees)
      
      go(subterm(lhs), rhs :: Nil)
    case Open(op) =>
      raise(ErrorReport(msg"Illegal position for 'open' statement." -> tree.toLoc :: Nil))
      Term.Error
    case OpenIn(op, body) =>
      subterm(Block(Open(op) :: body :: Nil), inAppPrefix)
    case DynAccess(obj, fld, ai) =>
      Term.DynSel(subterm(obj), subterm(fld), ai)
    case Spread(kw, kwLoc, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' spread operator." -> kwLoc :: Nil))
      Term.Error
    case und: Under =>
      summon[UnderCtx].unders match
      case N =>
        raise(ErrorReport(msg"Illegal position for '_' placeholder." -> tree.toLoc :: Nil))
        Term.Error
      case S(unds) =>
        val sym = VarSymbol(Ident("_" + unds.size))
        unds += sym
        sym.ref()
    case Annotated(lhs, rhs) =>
      annot(lhs).fold(subterm(rhs))(ann =>
        Term.Annotated(ann, subterm(rhs)))
    case Keywrd(kw) =>
      raise(ErrorReport(msg"Unexpected keyword '${kw.name}' in this position." -> tree.toLoc :: Nil))
      Term.Error
    case Constructor(delc) =>
      raise(ErrorReport(msg"Unsupported constructor in this position." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def arg(tree: Tree)(using UnderCtx): Ctxl[Term] = tree match
    case u: Under => subterm(tree) // Note: currently `f(a, _, c)` is treated the same as `f of a, _, c`
    case _ => term(tree)
  def fld(tree: Tree)(using UnderCtx): Ctxl[Elem] = tree match
    case InfixApp(id: Ident, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, Term.Lit(StrLit(id.name).withLocOf(id)), S(arg(rhs)))
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, term(lhs), S(arg(rhs)))
    case Spread(Keyword.`..`, _, S(trm)) =>
      Spd(false, arg(trm))
    case Spread(Keyword.`...`, _, S(trm)) =>
      Spd(true, arg(trm))
    case _ =>
      val t = arg(tree)
      var flags = FldFlags.empty
      Fld(flags, t, N)
  
  def unit: Term.UnitVal = Term.UnitVal()
  
  
  
  def block(sts: Ls[Tree], hasResult: Bool)(using c: Ctx)(using UnderCtx): (Blk, Ctx) =
    block(new Tree.Block(sts), hasResult)
  
  def block(blk: Tree.Block, hasResult: Bool)(using c: Ctx)(using UnderCtx): (Blk, Ctx) =
    blockOrRcd(blk, hasResult) match
      case (blk: Blk, ctx) => (blk, ctx)
      case (rcd: Rcd, ctx) => (Blk(Nil, rcd), ctx)
  
  // * Some blocks do not have a meaningful result,
  // * e.g., constructor blocks or top-level blocks (in MLscript files and diff-tests);
  // * for these, elaborate with `hasResult = false`, which uses `undefined` as the result
  // * when there is no other result available. This is fine since the value is never used.
  // * These useless trailing `undefined`s are then removed by `Lowering`.
  def blockOrRcd(blk: Tree.Block, hasResult: Bool)(using c: Ctx)(using UnderCtx)
    : (Blk | Rcd, Ctx)
    = trace[(Blk | Rcd, Ctx)](
        pre = s"Elab block ${blk.desugStmts.toString.truncate(100, "[...]")} ${ctx.outer}", r => s"~> ${r._1}"
      ):
    
    val members = blk.definedSymbols.toMap
    val newSignatureTrees = mutable.Map.empty[Str, Tree] // * Store trees of signatures
    
    // TODO Support module overloading and roll this check up
    blk.definedSymbols.foreach:
      case (name, sym) =>
        val defns = sym.trees.collect:
          case td: TermDef if td.rhs.isDefined => td
          case td: TypeDef => td
        if defns.length > 1 then
          raise(ErrorReport(msg"Multiple definitions of symbol '$name'" -> N ::
            defns.map(msg"defined here" -> _.toLoc)))
        val decls = sym.trees.collect:
          case td: TermDef if td.rhs.isEmpty => td
        if decls.length > 1 then
          raise(ErrorReport(msg"Multiple declarations of symbol '$name'" -> N ::
            decls.map(msg"declared here" -> _.toLoc)))
        val sig = decls.collectFirst:
          case td
            if td.annotatedResultType.isDefined
            && td.paramLists.isEmpty
            => td.annotatedResultType.get
        sig.foreach: sig =>
          newSignatureTrees += name -> sig
    
    // TODO extract this into a separate method
    // * @param funs:
    // *  While elaborating a block, we move all function definitions to the top (similar to JS function semantics)
    @tailrec
    def go(sts: Ls[Tree], annotations: Ls[Annot], acc: Ls[Statement]): Ctxl[(Blk | Rcd, Ctx)] =
      /** Call this function when the following term cannot be annotated. */
      def reportUnusedAnnotations: Unit = if annotations.nonEmpty then raise:
        WarningReport:
          msg"This annotation has no effect" -> (annotations.foldLeft[Opt[Loc]](N):
            case (acc, ann) => acc match
              case N => ann.toLoc
              case S(loc) => S(loc ++ ann.toLoc)
          ) :: (sts.headOption match
            case N => msg"A target term is expected at the end of block" -> blk.toLoc.map(_.right)
            case S(head) => msg"Annotations are not supported on ${head.describe} terms." -> head.toLoc
          ) :: Nil
      sts match
      case Nil =>
        reportUnusedAnnotations
        (mkBlk(acc, N, hasResult), ctx)
      case Constructor(Block(ctors)) :: sts =>
        // TODO properly handle (it currently desugars to sibling classes)
        go(sts, annotations, acc)
      case Open(bod) :: sts =>
        reportUnusedAnnotations
        bod match
          case Jux(bse, Block(sts)) =>
            some(bse -> some(sts))
          // * There could be other shapes of open statements...
          case bse: Ident =>
            some(bse -> N)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement shape." -> bod.toLoc :: Nil))
            N
        match
        case N => go(sts, annotations, acc)
        case S((base, importedTrees)) =>
          base match
          case baseId: Ident =>
            ctx.get(baseId.name) match
            case S(baseElem) =>
              val importedNames = importedTrees match
                case N => // "wilcard" open
                  baseElem.symbol match
                  case S(sym: BlockMemberSymbol) if sym.modOrObjTree.isDefined =>
                    sym.modOrObjTree.get.definedSymbols.map:
                      case (nme, sym) => nme -> Ctx.SelElem(baseElem, sym.nme, S(sym), isImport = true)
                  case _ =>
                    raise(ErrorReport(msg"Wildcard 'open' not supported for this kind of symbol." -> baseId.toLoc :: Nil))
                    Nil
                case S(sts) => sts.flatMap:
                  case id: Ident =>
                    if ctx.env.contains(id.name) then
                      raise(WarningReport(msg"Imported name '${id.name}' is shadowed by a name already defined in the same scope" -> id.toLoc :: Nil))
                    val sym = resolveField(id, baseElem.symbol, id)
                    val e = Ctx.SelElem(baseElem, id.name, sym, isImport = true)
                    id.name -> e :: Nil
                  case t =>
                    raise(ErrorReport(msg"Illegal 'open' statement element." -> t.toLoc :: Nil))
                    Nil
              (ctx elem_++ importedNames).givenIn:
                go(sts, Nil, acc)
            case N =>
              raise(ErrorReport(msg"Name not found: ${baseId.name}" -> baseId.toLoc :: Nil))
              go(sts, Nil, acc)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement base." -> base.toLoc :: Nil))
            go(sts, Nil, acc)
      case (m @ Modified(Keyword.`import`, absLoc, arg)) :: sts =>
        reportUnusedAnnotations
        val (newCtx, newAcc) = arg match
          case Tree.StrLit(path) =>
            val stmt = importPath(path)
            (ctx + (stmt.sym.nme -> stmt.sym),
            stmt.withLocOf(m) :: acc)
          case _ =>
            raise(ErrorReport(
              msg"Expected string literal after 'import' keyword" ->
              arg.toLoc :: Nil))
            (ctx, acc)
        newCtx.givenIn:
          go(sts, Nil, newAcc)
      
      case Spread(Keyword.`...`, kwLoc, S(body)) :: sts =>
        reportUnusedAnnotations
        go(sts, Nil, RcdSpread(term(body)) :: acc)
      case InfixApp(lhs, Keyword.`:`, rhs) :: sts =>
        var newCtx = ctx
        val rhs_t = rhs match
          case _: Under => subterm(rhs)
          case _ => term(rhs)
        val newAcc = lhs match
          case id: Ident =>
            val sym = new VarSymbol(id)
            newCtx += id.name -> sym
            RcdField(Term.Lit(StrLit(id.name)).withLocOf(id), sym.ref(id)) ::
            DefineVar(sym, rhs_t) ::
            LetDecl(sym, annotations) ::
            acc
          case lit: Literal =>
            reportUnusedAnnotations
            RcdField(Term.Lit(lit).withLocOf(lit), rhs_t) :: acc
          case Bra(BracketKind.Round, inner) =>
            reportUnusedAnnotations
            RcdField(term(inner), rhs_t) :: acc
          case _ =>
            raise(ErrorReport(msg"Unexpected record key shape." -> lhs.toLoc :: Nil))
            RcdField(Term.Error, rhs_t) :: acc
        newCtx.givenIn:
          go(sts, Nil, newAcc)
      case (hd @ LetLike(`let`, Apps(id: Ident, tups), rhso, N)) :: sts
      if tups.isEmpty || id.name.headOption.exists(_.isLower) =>
        reportUnusedAnnotations
        val sym =
          fieldOrVarSym(LetBind, id)
        log(s"Processing `let` statement $id (${sym}) ${ctx.outer}")
        members.get(id.name).foreach: s =>
          raise(ErrorReport(msg"Name '${id.name}' is already used"
            -> hd.toLoc :: msg"by a member declared in the same block" -> s.toLoc :: Nil))
        val newAcc = rhso match
          case S(rhs) =>
            val rrhs = tups.foldRight(rhs):
              Tree.InfixApp(_, Keyword.`=>`, _)
            mkLetBinding(sym, term(rrhs), annotations) reverse_::: acc
          case N =>
            if tups.nonEmpty then
              raise(ErrorReport(msg"Expected a right-hand side for let bindings with parameters" -> hd.toLoc :: Nil))
            LetDecl(sym, annotations) :: acc
        (ctx + (id.name -> sym)) givenIn:
          go(sts, Nil, newAcc)
      case (tree @ LetLike(`let`, lhs, _, N)) :: sts =>
        raise(ErrorReport(msg"Unsupported let binding shape" -> tree.toLoc :: Nil))
        go(sts, Nil, Term.Error :: acc)
      case Def(lhs, rhs) :: sts =>
        reportUnusedAnnotations
        lhs match
        case id: Ident =>
          val r = term(rhs)
          ctx.get(id.name) match
          case S(elem) =>
            elem.symbol match
            case S(sym: LocalSymbol) => go(sts, Nil, DefineVar(sym, r) :: acc)
          case N =>
            // TODO lookup in members? inherited/refined stuff?
            raise(ErrorReport(msg"Name not found: ${id.name}" -> id.toLoc :: Nil))
            go(sts, Nil, Term.Error :: acc)
        case App(base, args) =>
          go(Def(base, InfixApp(args, Keyword.`=>`, rhs)) :: sts, Nil, acc)
        case _ =>
          raise(ErrorReport(msg"Unrecognized definitional assignment left-hand side: ${lhs.describe}"
            -> lhs.toLoc :: Nil)) // TODO BE
          go(sts, Nil, Term.Error :: acc)
      case (td @ TermDef(k, nme, rhs)) :: sts =>
        log(s"Processing term definition $nme")
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        td.name match
          case R(id) =>
            val sym = members.getOrElse(id.name, die)
            val owner = ctx.outer.inner
            val isMethod = owner.exists(_.isInstanceOf[ClassSymbol])
            val nonLocalRetHandler = TempSymbol(N, s"nonLocalRetHandler$$${id.name}")
            val tdf = ctx.nest(OuterCtx.Function(nonLocalRetHandler)).givenIn:
              // * Add type parameters to context
              val (tps, newCtx1) = td.typeParams match
                case S(t) => 
                  val (tps, ctx) = typeParams(t)
                  (S(tps), ctx)
                case N => (N, ctx)
              // * Add parameters to context
              var newCtx = newCtx1
              val pss = td.paramLists.map: ps =>
                val (res, newCtx2) = params(ps, false)(using newCtx)
                newCtx = newCtx2
                res
              // * Elaborate signature
              val st = td.annotatedResultType.orElse(newSignatureTrees.get(id.name))
              val s = st.map(term(_)(using newCtx))
              val b = if ctx.mode != Mode.Light
                then rhs.map(term(_)(using newCtx))
                else S(Term.Missing)
              val nb: Opt[Term] = if nonLocalRetHandler.directRefs.isEmpty then b else b.map: inner =>
                val clsSym = ClassSymbol(Tree.DummyTypeDef(Cls), Tree.Ident("‹non-local return effect›"))
                val valueSym = VarSymbol(Ident("value"))
                val resumeSym = VarSymbol(Ident("resume"))
                val mtdSym = BlockMemberSymbol("ret", Nil, true)
                val td = TermDefinition(
                  N, Fun, mtdSym, PlainParamList(Param(FldFlags.empty, valueSym, N, Modulefulness.none) :: Nil) :: Nil,
                  N, N, S(valueSym.ref(Ident("value"))), FlowSymbol(s"‹result of non-local return›"), TermDefFlags.empty, Modulefulness.none, Nil)
                val htd = HandlerTermDefinition(resumeSym, td)
                Term.Handle(nonLocalRetHandler, state.nonLocalRetHandlerTrm, Nil, clsSym, htd :: Nil, inner)
              val r = FlowSymbol(s"‹result of ${sym}›")
              
              val mfn = st match
                // TypeDef(Mod, _, N, N) indicates if the function marks
                // its result as "module". e.g, `fun f: module M`
                //                                      ^^^^^^
                case S(TypeDef(Mod, _, N)) => 
                  Modulefulness.ofSign(s)(true)
                case _ =>
                  Modulefulness.none
              
              val tdf = TermDefinition(owner, k, sym, pss, tps, s, nb, r, 
                TermDefFlags.empty.copy(isMethod = isMethod), mfn, annotations)
              sym.defn = S(tdf)
              
              tdf
            go(sts, Nil, tdf :: acc)
          case L(d) =>
            reportUnusedAnnotations
            raise(d)
            go(sts, Nil, acc)
      case (td @ TypeDef(k, head, rhs)) :: sts =>
        
        assert((k is Als) || (k is Cls) || (k is Mod) || (k is Obj) || (k is Pat), k)
        val body = td.withPart
        
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        val nme = td.name match
          case R(id) => id
          case L(d) =>
            raise(d)
            return go(sts, Nil, acc)
        val sym = members.getOrElse(nme.name, lastWords(s"Symbol not found: ${nme.name}"))
        
        var newCtx = S(td.symbol).collectFirst:
            case s: InnerSymbol => s
          .fold(ctx.nest(OuterCtx.NonReturnContext))(ctx.nestInner(_))
        
        val tps = td.typeParams match
          case S(ts) =>
            ts.tys.flatMap: targ =>
              val (id, vce) = targ match
                case id: Ident =>
                  (id, N)
                case Modified(Keyword.`in`, inLoc, id: Ident) =>
                  (id, S(false))
                case Modified(Keyword.`out`, outLoc, id: Ident) =>
                  (id, S(true))
              val vs = VarSymbol(id)
              val res = TyParam(FldFlags.empty, vce, vs)
              vs.decl = S(res)
              res :: Nil
          case N => Nil
        
        newCtx ++= tps.map(tp => tp.sym.name -> tp.sym) // TODO: correct ++?
        
        val isDataClass = annotations.exists:
          case Annot.Modifier(Keyword.`data`) => true
          case _ => false
        
        val pss = td.paramLists.map: ps =>
          val (res, newCtx2) =
            given Ctx = newCtx
            params(ps, isDataClass)
          newCtx = newCtx2
          res
        
        def withFields(using Ctx)(fn: (Ctx) ?=> (Term.Blk, Ctx)): (Term.Blk, Ctx) =
          val fields: Ls[Statement] = pss.flatMap: ps =>
            ps.params.flatMap: p =>
              // For class-like types, "desugar" the parameters into additional class fields.
              val owner = td.symbol match
                // Any MemberSymbol should be an InnerSymbol, except for TypeAliasSymbol, 
                // but type aliases should not call this function.
                case s: InnerSymbol => S(s)
                case _: TypeAliasSymbol => die

              if p.flags.value || isDataClass then
                val fsym = BlockMemberSymbol(p.sym.nme, Nil)
                val fdef = TermDefinition(
                  owner,
                  ImmutVal,
                  fsym,
                  Nil, N, N,
                  S(p.sym.ref()),
                  FlowSymbol("‹class-param-res›"),
                  TermDefFlags.empty.copy(isMethod = (k is Cls)),
                  p.modulefulness,
                  Nil
                )
                assert(p.fldSym.isEmpty)
                p.fldSym = S(fsym)
                fsym.defn = S(fdef)
                sym.defn = S(fdef)
                fdef :: Nil
              else
                val psym = TermSymbol(LetBind, owner, p.sym.id)
                val decl = LetDecl(psym, Nil)
                val defn = DefineVar(psym, p.sym.ref())
                p.fldSym = S(psym)
                decl :: defn :: Nil
          
          val ctxWithFields =
            val valParams = fields.collect:
              case f: TermDefinition =>
                f.sym.nme -> f.sym
            val params = fields.collect:
              case (f: LetDecl) =>
                f.sym.nme -> f.sym
            ctx.withMembers(valParams, ctx.outer.inner) ++ params
          
          val (blk, c) = fn(using ctxWithFields)
          val blkWithFields: Blk = blk.copy(stats = fields ::: blk.stats)
          (blkWithFields, c)
        
        def mkBody(using Ctx) = withFields:
          body match
          case N | S(Error()) => (new Blk(Nil, Term.Lit(UnitLit(false))), ctx)
          case S(b: Tree.Block) => block(b, hasResult = false)
          case S(t) =>
            raise(ErrorReport(
              msg"Illegal body of ${k.desc} definition (should be a block; found ${t.describe})." -> t.toLoc :: Nil))
            (new Blk(Nil, Term.Lit(UnitLit(false))), ctx)
        
        val defn = k match
        case Als =>
          val alsSym = td.symbol.asInstanceOf[TypeAliasSymbol] // TODO improve `asInstanceOf`
          // newCtx.nest(S(alsSym)).givenIn:
          newCtx.nestLocal.givenIn:
            assert(pss.isEmpty)
            assert(body.isEmpty)
            val d =
              given Ctx = newCtx
              semantics.TypeDef(alsSym, tps, rhs.map(term(_)), N, annotations)
            alsSym.defn = S(d)
            d
        case Pat =>
          val patSym = td.symbol.asInstanceOf[PatternSymbol] // TODO improve `asInstanceOf`
          val owner = ctx.outer.inner
          newCtx.nestInner(patSym).givenIn:
            if pss.length > 1 then raise:
                ErrorReport:
                  msg"Multiple parameter lists are not supported for this definition." ->
                    td.toLoc :: Nil
            assert(body.isEmpty)
            val ps = pss.headOption
            td.rhs match
              case N => raise(ErrorReport(msg"Pattern definitions must have a body." -> td.toLoc :: Nil))
              case S(tree) =>
                val (patternParams, extractionParams) = ps match // Filter out pattern parameters.
                  case S(ParamList(_, params, _)) => params.partition:
                    case param @ Param(flags = FldFlags(false, false, false, true, false)) => true
                    case param @ Param(flags = FldFlags(pat = false)) => false
                  case N => (Nil, Nil)
                // TODO: Implement extraction parameters.
                if extractionParams.nonEmpty then
                  raise(ErrorReport(msg"Pattern extraction parameters are not yet supported." ->
                    Loc(extractionParams.iterator.map(_.sym)) :: Nil))
                log(s"pattern parameters: ${patternParams.mkString("{ ", ", ", " }")}")
                patSym.patternParams = patternParams
                val split = ucs.DeBrujinSplit.elaborate(patternParams, tree, this)
                scoped("ucs:rp:elaborated"):
                  log(s"elaborated ${patSym.nme}:\n${split.display}")
                patSym.split = split
            log(s"pattern body is ${td.rhs}")
            val translate = new ucs.Translator(this)
            val bod = translate(
              patSym.patternParams,
              Nil, // ps.map(_.params).getOrElse(Nil), // TODO[Luyu]: remove pattern parameters
              td.rhs.getOrElse(die))
            val pd = PatternDef(owner, patSym, sym, tps, ps, Nil,
              ObjBody(Blk(bod, Term.Lit(UnitLit(false)))), annotations)
            patSym.defn = S(pd)
            pd
        case k: (Mod.type | Obj.type) =>
          val clsSym = td.symbol.asInstanceOf[ModuleSymbol] // TODO: improve `asInstanceOf`
          val owner = ctx.outer.inner
          newCtx.nestInner(clsSym).givenIn:
            log(s"Processing type definition $nme")
            val cd =
              val (bod, c) = mkBody
              ModuleDef(owner, clsSym, sym, tps, pss.headOption, pss.tailOr(Nil), newOf(td), k, ObjBody(bod), annotations)
            clsSym.defn = S(cd)
            cd
        case Cls =>
          val clsSym = td.symbol.asInstanceOf[ClassSymbol] // TODO: improve `asInstanceOf`
          val owner = ctx.outer.inner
          newCtx.nestInner(clsSym).givenIn:
            log(s"Processing type definition $nme")
            val cd =
              val (bod, c) = mkBody
              ClassDef(owner, Cls, clsSym, sym, tps, pss, newOf(td), ObjBody(bod), annotations)
            clsSym.defn = S(cd)
            cd
        sym.defn = S(defn)
        go(sts, Nil, defn :: acc)
      case Annotated(annotation, target) :: sts =>
        go(target :: sts, annotations ++ annot(annotation), acc)
      case (st: Tree) :: sts =>
        // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        val res = annotations.foldLeft(term(st)):
          case (acc, ann) => Term.Annotated(ann, acc)
        sts match
        case Nil => (mkBlk(acc, S(res), hasResult), ctx)
        case _ => go(sts, Nil, res :: acc)
    end go
    
    c.withMembers(members, c.outer.inner).givenIn:
      go(blk.desugStmts, Nil, Nil)
  
  
  def mkBlk(acc: Ls[Statement], res: Opt[Term], hasResult: Bool): Blk | Rcd =
    // TODO forbid certain kinds of terms in records
    val isRcd = acc.exists:
      case _: (RcdField | RcdSpread) => true
      case _ => false
    if isRcd then Term.Rcd((res.toList ::: acc).reverse)
    else Blk(acc.reverse, res.getOrElse:
      if hasResult
        then unit
        else Term.Lit(UnitLit(false))
    )
  
  def newOf(td: TypeDef)(using Ctx): Opt[Term.New] =
    td.extension
    match
    case S(ext) => S(term(ProperNew(S(ext), N)))
    case N => N
    match
    case S(n: Term.New) => S(n)
    case S(trm) =>
      raise:
        ErrorReport:
          msg"Unexpected shape of extension clause: ${trm.describe}" -> trm.toLoc :: Nil
      N
    case N => N
  
  def fieldOrVarSym(k: TermDefKind, id: Ident)(using Ctx): TermSymbol | VarSymbol =
    if ctx.outer.inner.isDefined then TermSymbol(k, ctx.outer.inner, id)
    else VarSymbol(id)
  
  def param(t: Tree, inUsing: Bool, inDataClass: Bool): Ctxl[Opt[Opt[Bool] -> Param]] =
    // mm: `module`-modified
    def go(t: Tree, inUsing: Bool, flags: FldFlags, mm: Bool): Ctxl[Opt[Opt[Bool] -> Param]] = t match
    case TypeDef(Mod, inner, N) =>
      go(inner, inUsing, flags, true)
    case TypeDef(Pat, inner, N) =>
      go(inner, inUsing, flags.copy(pat = true), mm)
    case TermDef(ImmutVal, inner, _) =>
      go(inner, inUsing, flags.copy(value = true), mm)
    case TermDef(Ins, inner, N) =>
      go(inner, inUsing, flags, mm)
    case _ =>
      t.asParam(inUsing).map: (isSpd, p, t) =>
        val sym = VarSymbol(p)
        val sign = t.map(term(_))
        val param = Param(flags, sym, sign, Modulefulness.ofSign(sign)(mm))
        sym.decl = S(param)
        isSpd -> param
    go(t, inUsing, if inDataClass then FldFlags.empty.copy(value = true) else FldFlags.empty, false)
      
  
  def params(t: Tree, inDataClass: Bool): Ctxl[(ParamList, Ctx)] = t match
    case Tup(ps) =>
      def go(ps: Ls[Tree], acc: Ls[Param], ctx: Ctx, flags: ParamListFlags): (ParamList, Ctx) =
        ps match
        case Nil => (ParamList(flags, acc.reverse, N), ctx)
        case hd :: tl =>
          val isCtxParam = hd match
            case TermDef(k = Ins, rhs = N) => true
            case _ => false
          param(hd, flags.ctx || isCtxParam, inDataClass)(using ctx) match
          case S((isSpd, p)) =>
            val newCtx = ctx + (p.sym.name -> p.sym)
            val newFlags = if isCtxParam then flags.copy(ctx = true) else flags
            if isCtxParam && acc.nonEmpty then
              raise(ErrorReport(msg"Keyword `using` must occur before all parameters." -> hd.toLoc :: Nil))
            isSpd match
            case S(spdKnd) =>
              if tl.nonEmpty then
                raise(ErrorReport(msg"Spread parameters must be the last in the parameter list." -> hd.toLoc :: Nil))
              (ParamList(flags, acc.reverse, S(p)), newCtx)
            case N => go(tl, p :: acc, newCtx, newFlags)
          case N =>
            ???
      go(ps, Nil, ctx, ParamListFlags.empty)
  
  def typeParams(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case TyTup(ps) =>
      val vs = ps.map:
        case id: Ident =>
          val sym = VarSymbol(id)
          sym.decl = S(TyParam(FldFlags.empty, N, sym))
          Param(FldFlags.empty, sym, N, Modulefulness.none)
      (vs, ctx ++ vs.map(p => p.sym.name -> p.sym))
  
  def importFrom(sts: Tree.Block)(using c: Ctx): (Blk, Ctx) =
    given UnderCtx = new UnderCtx(N)
    val (res, newCtx) = block(sts, hasResult = false)
    // TODO handle name clashes
    (res, newCtx)
  
  def topLevel(sts: Tree.Block)(using c: Ctx): (Blk, Ctx) =
    given UnderCtx = new UnderCtx(N)
    val (res, ctx) = block(sts, hasResult = false)
    computeVariances(res)
    (res, ctx)
  
  def computeVariances(s: Statement): Unit =
    val trav = VarianceTraverser()
    def go(s: Statement): Unit = s match
      case TermDefinition(_, k, sym, pss, _, sign, body, r, _, _, _) =>
        pss.foreach(ps => ps.params.foreach(trav.traverseType(S(false))))
        sign.foreach(trav.traverseType(S(true)))
        body match
          case S(b) =>
            go(b)
          case N =>
      case ClassDef(sym, tps, pso, body) =>
        pso.foreach: ps =>
          ps.foreach: p =>
            p.sign.foreach(trav.traverseType(S(true)))
        body.blk.stats.foreach(go)
        // s.subStatements.foreach(go)
      case _ =>
        s.subStatements.foreach(go)
    while trav.changed do
      trav.changed = false
      go(s)
  
  class VarianceTraverser(var changed: Bool = true) extends Traverser:
    override def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.TyApp(lhs, targs) =>
        lhs.symbol.flatMap(sym => sym.asTpe orElse sym.asMod orElse sym.asObj) match
          case S(sym: ClassSymbol) =>
            sym.defn match
            case S(td: ClassDef) =>
              if td.tparams.sizeCompare(targs) =/= 0 then
                raise(ErrorReport(msg"Wrong number of type arguments" -> trm.toLoc :: Nil)) // TODO BE
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              // TODO(sym->sym.uid)
          case S(sym: ModuleSymbol) =>
            sym.defn match
            case S(td: ModuleDef) =>
              if td.tparams.sizeCompare(targs) =/= 0 then
                raise(ErrorReport(msg"Wrong number of type arguments" -> trm.toLoc :: Nil)) // TODO BE
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              // TODO(sym->sym.uid)
          case S(sym: TypeAliasSymbol) =>
            // TODO dedup with above...
            sym.defn match
            case S(td: semantics.TypeDef) =>
              if td.tparams.sizeCompare(targs) =/= 0 then
                raise(ErrorReport(msg"Wrong number of type arguments" -> trm.toLoc :: Nil)) // TODO BE
              td.tparams.zip(targs).foreach:
                case (tp, targ) =>
                  if !tp.isContravariant then traverseType(pol)(targ)
                  if !tp.isCovariant then traverseType(pol.!)(targ)
            case N =>
              TODO(sym->sym.uid)
          // case S(sym) => ???
          case N =>
            log(s"No symbol found $lhs ${lhs.symbol}")
            ???
      case Term.Ref(sym: VarSymbol) =>
        sym.decl match
          case S(ty: TyParam) =>
            if pol =/= S(true) && ty.isCovariant then
              changed = true
              ty.isCovariant = false
            if pol =/= S(false) && ty.isContravariant then
              changed = true
              ty.isContravariant = false
          // case _ => ???
          case N =>
            lastWords(s"VarSymbol ${sym.name} has no declaration")
      case _ => super.traverseType(pol)(trm)
  abstract class Traverser:
    def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.Lit(_) | Term.UnitVal() | Term.Error =>
      case Term.TyApp(lhs, targs) =>
        // lhs.resolveSymbol
        // targs.foreach(traverseType(pol))
        ???
      case r: Term.Ref =>
      case Term.FunTy(l, r, e) =>
        traverseType(pol.!)(l)
        traverseType(pol)(r)
        e.foreach(e => traverseType(pol)(e))
      case Term.Forall(_, _, body) =>
        traverseType(pol)(body)
      case Term.WildcardTy(in, out) =>
        in.foreach(t => traverseType(pol.!)(t))
        out.foreach(t => traverseType(pol)(t))
      case Term.CompType(lhs, rhs, _) => () // TODO:
      case Term.SynthSel(bse, nme) =>
        traverseType(pol)(bse) // FIXME: probably wrong for what we want to do
      case Term.Tup(fields) =>
        // fields.foreach(f => traverseType(pol)(f.value))
        fields.foreach(traverseType(pol))
      // case _ => ???
      case Term.Neg(ty) => 
        traverseType(pol.!)(ty)
      case _ =>
        // TODO
    def traverseType(pol: Pol)(f: Elem): Unit = f match
      case f: Fld =>
        traverseType(pol)(f.term)
        f.asc.foreach(traverseType(pol))
    def traverseType(pol: Pol)(f: Param): Unit =
      f.sign.foreach(traverseType(pol))
end Elaborator

type Pol = Opt[Bool]
extension (p: Pol) def ! : Pol = p.map(!_)

