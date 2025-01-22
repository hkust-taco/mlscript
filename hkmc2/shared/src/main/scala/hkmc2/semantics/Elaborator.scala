package hkmc2
package semantics


import scala.collection.mutable
import scala.annotation.tailrec
import scala.language.implicitConversions

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.*
import Tree.*
import hkmc2.Message.MessageContext

import Keyword.{`let`, `set`}


object Elaborator:
  
  val binaryOps = Set(
    ",",
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "===", "!==",
    "&&", "||")
  val unaryOps = Set("-", "+", "!", "~")
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
  
  case class Ctx(outer: Opt[InnerSymbol], parent: Opt[Ctx], env: Map[Str, Ctx.Elem]):
    
    def +(local: Str -> Symbol): Ctx = copy(outer, env = env + local.mapSecond(Ctx.RefElem(_)))
    def ++(locals: IterableOnce[Str -> Symbol]): Ctx =
      copy(outer, env = env ++ locals.mapValues(Ctx.RefElem(_)))
    def elem_++(locals: IterableOnce[Str -> Ctx.Elem]): Ctx =
      copy(outer, env = env ++ locals)
    
    def withMembers(members: Iterable[Str -> MemberSymbol[?]], out: Opt[Symbol] = N): Ctx =
      copy(env = env ++ members.map:
        case (nme, sym) =>
          val elem = out orElse outer match
            case S(outer) => Ctx.SelElem(outer, sym.nme, S(sym))
            case N => Ctx.RefElem(sym)
          nme -> elem
      )
    
    def nest(outer: Opt[InnerSymbol]): Ctx = Ctx(outer, Some(this), Map.empty)
    
    def get(name: Str): Opt[Ctx.Elem] =
      env.get(name).orElse(parent.flatMap(_.get(name)))
    def getOuter: Opt[InnerSymbol] = outer.orElse(parent.flatMap(_.getOuter))
    
    // * Invariant: We expect that the top-level context only contain hard-coded symbols like `globalThis`
    // * and that built-in symbols like Int and Str be imported into another nested context on top of it.
    // * It should not be possible to shadow these built-in symbols, so user code should always be compiled
    // * in further nested contexts.
    // * Method `getBuiltin` is used to look up built-in symbols in the context of builtin symbols.
    def getBuiltin(nme: Str): Opt[Ctx.Elem] =
      parent.filter(_.parent.nonEmpty).fold(env.get(nme))(_.getBuiltin(nme))
    
    // TODO only store this in the top-level context!
    object Builtins:
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
      val Int = assumeBuiltinCls("Int")
      val Num = assumeBuiltinCls("Num")
      val Str = assumeBuiltinCls("Str")
      val untyped = assumeBuiltinTpe("untyped")
      // println(s"Builtins: $Int, $Num, $Str, $untyped")
      val Predef = assumeBuiltinMod("Predef")
      def getBuiltinOp(op: Str): Opt[Str] =
        if getBuiltin(op).isDefined then builtinBinOps.get(op) else N
  
  object Ctx:
    abstract class Elem:
      def nme: Str
      def ref(id: Tree.Ident)(using Elaborator.State): Term
      def symbol: Opt[Symbol]
    final case class RefElem(val sym: Symbol) extends Elem:
      val nme = sym.nme
      def ref(id: Tree.Ident)(using Elaborator.State): Term =
        // * Note: due to symbolic ops, we may have `id.name =/= nme`;
        // * e.g., we can have `id.name = "|>"` and `nme = "pipe"`.
        Term.Ref(sym)(id, 666) // FIXME: 666 is a temporary placeholder
      def symbol = S(sym)
    final case class SelElem(val base: Elem, val nme: Str, val symOpt: Opt[FieldSymbol]) extends Elem:
      def ref(id: Tree.Ident)(using Elaborator.State): Term =
        // * Same remark as in RefElem#ref
        Term.SynthSel(base.ref(Ident(base.nme)),
          new Tree.Ident(nme).withLocOf(id))(symOpt)
      def symbol = symOpt
    given Conversion[Symbol, Elem] = RefElem(_)
    val empty: Ctx = Ctx(N, N, Map.empty)
  
  type Ctxl[A] = Ctx ?=> A
  
  transparent inline def ctx(using Ctx): Ctx = summon
  
  class State:
    given State = this
    val suid = new Uid.Symbol.State
    val globalThisSymbol = TopLevelSymbol("globalThis")
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


class Elaborator(val tl: TraceLogger, val wd: os.Path)
(using val raise: Raise, val state: State)
extends Importer:
  import tl.*
  
  def mkLetBinding(sym: LocalSymbol, rhs: Term, annotations: Ls[Annot]): Ls[Statement] =
    LetDecl(sym, annotations) :: DefineVar(sym, rhs) :: Nil
  
  def resolveField(srcTree: Tree, base: Opt[Symbol], nme: Ident): Opt[FieldSymbol] =
    base match
    case S(psym: BlockMemberSymbol) =>
      psym.modTree match
      case S(cls) =>
        cls.definedSymbols.get(nme.name) match
        case s @ S(clsSym) => s
        case N =>
          raise(ErrorReport(msg"${cls.k.desc.capitalize} '${cls.symbol.nme
            }' does not contain member '${nme.name}'" -> srcTree.toLoc :: Nil))
          N
      case N =>
        N
    case _ => N
  
  /** To perform a reverse lookup for a term that references a symbol in the current context. */
  def reference(target: ClassSymbol | ModuleSymbol): Ctxl[Opt[Term]] =
    def go(ctx: Ctx): Opt[Term] =
      ctx.env.values.collectFirst:
        case elem if elem.symbol.flatMap(_.asClsLike).contains(target) => elem.ref(target.id)
      .orElse(ctx.parent.flatMap(go))
    go(ctx).map(Term.SynthSel(_, Ident("class"))(S(target)))
  
  def cls(tree: Tree, inAppPrefix: Bool): Ctxl[Term] = trace[Term](s"Elab class ${tree.showDbg}", r => s"~> $r"):
    val trm = term(tree, inAppPrefix)
    trm.symbol match
    case S(cls: ClassSymbol) =>
      trm
    case S(mem: BlockMemberSymbol) =>
      if !mem.hasLiftedClass then trm
      else Term.SynthSel(trm, Ident("class"))(mem.clsTree.orElse(mem.modTree).map(_.symbol))
    case _ => trm
  
  def annot(tree: Tree): Ctxl[Opt[Annot]] = tree match
    case Keywrd(kw @ (Keyword.`abstract` | Keyword.`declare`)) => S(Annot.Modifier(kw))
    case _ => term(tree) match
      case Term.Error => N
      case trm =>
        trm.symbol match
        case S(sym) =>
          sym.asTpe match
          case S(ctx.Builtins.untyped) =>
            return S(Annot.Untyped)
          case _ => ()
        case _ => ()
        S(Annot.Trm(trm))
  
  def term(tree: Tree, inAppPrefix: Bool = false): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    tree.desugared match
    case Bra(k, e) =>
      k match
      case BracketKind.Round =>
      case _ =>
        raise(ErrorReport(msg"Unsupported ${k.name} in this position" -> tree.toLoc :: Nil))
      term(e)
    case Block(s :: Nil) =>
      term(s)
    case Block(sts) =>
      block(sts)._1
    case lit: Literal =>
      Term.Lit(lit)
    case d: Def =>
      term(Block(d :: UnitLit(true) :: Nil))
    case LetLike(`let`, lhs, rhso, S(bod)) =>
      term(Block(LetLike(`let`, lhs, rhso, N) :: bod :: Nil))
    case LetLike(`let`, lhs, S(rhs), N) =>
      raise(ErrorReport(
        msg"Expected a body for let bindings in expression position" ->
          tree.toLoc :: Nil))
      block(LetLike(`let`, lhs, S(rhs), N) :: Nil)._1
    case LetLike(`set`, lhs, S(rhs), N) =>
      Term.Assgn(term(lhs), term(rhs))
    case LetLike(`set`, lhs, S(rhs), S(bod)) =>
      // * Backtracking assignment
      lhs match
      case id: Ident =>
        val lt = term(lhs)
        val sym = TempSymbol(S(lt), "old")
        Term.Blk(
        LetDecl(sym, Nil) :: DefineVar(sym, lt) :: Nil, Term.Try(Term.Blk(
          Term.Assgn(lt, term(rhs)) :: Nil,
          term(bod),
        ), Term.Assgn(lt, sym.ref(id))))
      case _ => ??? // TODO error
    case Hndl(id, cls, blk, S(bod)) =>
      term(Block(Hndl(id, cls, blk, N) :: bod :: Nil))
    case Hndl(id: Ident, cls: Ident, Block(sts), N) =>
      raise(ErrorReport(
        msg"Expected a body for handle bindings in expression position" ->
          tree.toLoc :: Nil))
          
      block(Hndl(id, cls, Block(sts), N) :: Nil)._1
      
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
      Term.TyApp(term(lhs), targs.map {
        case Modified(Keyword.`in`, inLoc, arg) => Term.WildcardTy(S(term(arg)), N)
        case Modified(Keyword.`out`, outLoc, arg) => Term.WildcardTy(N, S(term(arg)))
        case Tup(Modified(Keyword.`in`, inLoc, arg1) :: Modified(Keyword.`out`, outLoc, arg2) :: Nil) =>
          Term.WildcardTy(S(term(arg1)), S(term(arg2)))
        case arg => term(arg)
      })
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
        val nestCtx = ctx ++ boundVars
        val bds = syms.map:
          case (sym, ub, lb) => QuantVar(sym, ub.map(ub => term(ub)(using nestCtx)), lb.map(lb => term(lb)(using nestCtx)))
        Term.Forall(bds, outer, term(body)(using nestCtx))
    case InfixApp(lhs, Keyword.`->`, Effectful(eff, rhs)) =>
      Term.FunTy(term(lhs), term(rhs), S(term(eff)))
    case InfixApp(lhs, Keyword.`->`, rhs) =>
      Term.FunTy(term(lhs), term(rhs), N)
    case InfixApp(lhs, Keyword.`=>`, rhs) =>
      ctx.nest(N).givenIn:
        val (syms, nestCtx) = params(lhs)
        Term.Lam(syms, term(rhs)(using nestCtx))
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Term.Asc(term(lhs), term(rhs))
    case tree @ InfixApp(lhs, Keyword.`is` | Keyword.`and`, rhs) =>
      val des = new ucs.Desugarer(this)(tree)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(des)}")
      val nor = new ucs.Normalization(this)(des)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(nor)}")
      Term.IfLike(Keyword.`if`, des)(nor)
    case app @ PartialApp(lhs, args) =>
      var params: Ls[Param] = Nil
      def mkParam =
        val p = Param(FldFlags.empty, VarSymbol(Ident("_")), N)
        params ::= p
        p
      def go(args: Ls[Tree \/ Under], acc: Ls[Term]): Term =
        args match
        case Nil => Term.Tup(acc.reverseIterator.map(Fld(FldFlags.empty, _, N)).toList)(
            Tup(Nil) // FIXME
          )
        case L(arg) :: rest => go(rest, term(arg) :: acc)
        case R(und) :: rest => go(rest, mkParam.sym.ref() :: acc)
      val base = lhs match
        case L(t) => term(t)
        case R(und) => mkParam.sym.ref()
      val res = FlowSymbol("‹partial-app-res›")
      val body = Term.App(base, go(args, Nil))(app, res)
      Term.Lam(PlainParamList(params.reverse), body)
    case App(Ident("|"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), true)
    case App(Ident("&"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), false)
    case App(Ident(":="), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.SetRef(term(lhs), term(rhs))
    case App(Ident("#"), Tree.Tup(Sel(pre, idn: Ident) :: (idp: Ident) :: Nil)) =>
      val c = cls(idn, inAppPrefix = false)
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
      Term.SelProj(term(pre), c, idp)(f)
    case App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: App(Ident(proj), args) :: Nil)) =>
      term(App(App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: Ident(proj) :: Nil)), args))
    case App(Ident("!"), Tree.Tup(rhs :: Nil)) =>
      Term.Deref(term(rhs))
    case App(Ident("~"), Tree.Tup(rhs :: Nil)) =>
      Term.Neg(term(rhs))
    case tree @ App(lhs, OpBlock(ops)) =>
      ops.foldLeft(term(lhs)):
        case (acc, (op, arg)) =>
          val sym = FlowSymbol("‹app-res›")
          val tup = new Tup(Nil) // TODO
          Term.App(term(op), Term.Tup(PlainFld(acc) :: PlainFld(term(arg)) :: Nil)(tup))(tree, sym)
    case tree @ App(lhs, rhs) =>
      val sym = FlowSymbol("‹app-res›")
      val lt = term(lhs, inAppPrefix = true)
      val rt = term(rhs)
      
      // Check if module arguments match module parameters
      val args = rt match
        case Term.Tup(fields) => S(fields)
        case _ => N
      if args.exists:
        _.exists:
          case spd: Spd => false
          case fld: Fld => fld.flags.mod
      then
        val params = lt.symbol
          .collect:
            case sym: BlockMemberSymbol => sym.trmTree
          .flatten
          .collect:
            case td: TermDef => td.paramLists.headOption
          .flatten
        for
          (args, params) <- (args zip params)
          (arg, param) <- (args zip params.fields)
        do
          arg match
          case spd: Spd =>
            TODO(spd)
          case arg: Fld =>
            val argMod = arg.flags.mod
            val paramMod = param.isModuleModifier
            if argMod && !paramMod then raise:
              ErrorReport:
                msg"Only module parameters may receive module arguments (values)." -> 
                arg.toLoc :: Nil
      
      Term.App(lt, rt)(tree, sym)
    case SynthSel(pre, nme) =>
      val preTrm = term(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      Term.SynthSel(preTrm, nme)(sym)
    case Sel(pre, nme) =>
      val preTrm = term(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      Term.Sel(preTrm, nme)(sym)
    case MemberProj(ct, nme) =>
      val c = cls(ct, inAppPrefix = false)
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
        Param(FldFlags.empty, self, N) :: Nil,
        S:
          Param(FldFlags.empty, args, N)
      )
      val rs = FlowSymbol("‹app-res›")
      Term.Lam(ps,
        Term.App(Term.SelProj(self.ref(), c, nme)(f), args.ref())(
          Tree.App(nme, Tree.Tup(Nil)) // FIXME
          , rs)
      )
    case tree @ Tup(fields) =>
      Term.Tup(fields.map(fld(_)))(tree)
    case New(body) => // TODO handle Under
      body match
      case App(c, Tup(params)) =>
        Term.New(cls(c, inAppPrefix = true), params.map(term(_))).withLocOf(tree)
      case c => // * We'll catch bad `new` targets during type checking
        Term.New(cls(c, inAppPrefix = false), Nil).withLocOf(tree)
      // case _ =>
      //   raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
    case tree @ Tree.IfLike(kw, _, split) =>
      val desugared = new ucs.Desugarer(this)(tree)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(desugared)}")
      val normalized = new ucs.Normalization(this)(desugared)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(normalized)}")
      Term.IfLike(kw, desugared)(normalized)
    case Tree.Quoted(body) => Term.Quoted(term(body))
    case Tree.Unquoted(body) => Term.Unquoted(term(body))
    case tree @ Tree.Case(_, branches) =>
      val scrut = VarSymbol(Ident("caseScrut"))
      val des = new ucs.Desugarer(this)(tree, scrut)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(des)}")
      val nor = new ucs.Normalization(this)(des)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(nor)}")
      Term.Lam(PlainParamList(
          Param(FldFlags.empty, scrut, N) :: Nil
        ), Term.IfLike(Keyword.`if`, des)(nor))
    case Modified(Keyword.`return`, kwLoc, body) =>
      Term.Ret(term(body))
    case Modified(Keyword.`throw`, kwLoc, body) =>
      Term.Throw(term(body))
    case Modified(Keyword.`do`, kwLoc, body) =>
      Term.Blk(term(body) :: Nil, unit)
    case TypeDef(Mod, head, N, N) =>
      term(head)
    case Tree.Region(id: Tree.Ident, body) =>
      val sym = VarSymbol(id)
      val nestCtx = ctx + (id.name -> sym)
      Term.Region(sym, term(body)(using nestCtx))
    case Tree.RegRef(reg, value) => Term.RegRef(term(reg), term(value))
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
    case TypeDef(k, head, extension, body) =>
      raise(ErrorReport(msg"Illegal type declaration in term position." -> tree.toLoc :: Nil))
      Term.Error
    case Modified(kw, kwLoc, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' modifier." -> kwLoc :: Nil))
      term(body)
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
          val app = Term.App(term(f, inAppPrefix = true), Term.Tup(
            fl :: args.map(fld))(tup))(ap, sym)
          go(app, trees)
        case (ap @ App(f, tup @ Tup(args))) :: trees =>
          val sym = FlowSymbol("‹app-res›")
          go(Term.App(term(f, inAppPrefix = true),
              Term.Tup(Fld(FldFlags.empty, acc, N) :: args.map(fld))(tup)
            )(ap, sym), trees)
        case Block(sts) :: trees =>
          go(acc, sts ::: trees)
        case tree :: trees =>
          raise(ErrorReport(msg"Illegal juxtaposition right-hand side." -> tree.toLoc :: Nil))
          go(acc, trees)
      
      go(term(lhs), rhs :: Nil)
    case Open(op) =>
      raise(ErrorReport(msg"Illegal position for 'open' statement." -> tree.toLoc :: Nil))
      Term.Error
    case OpenIn(op, body) =>
      term(Block(Open(op) :: body :: Nil), inAppPrefix)
    case Spread(kw, kwLoc, body) =>
      raise(ErrorReport(msg"Illegal position for '${kw.name}' spread operator." -> tree.toLoc :: Nil))
      Term.Error
    case Under() =>
      raise(ErrorReport(msg"Illegal position for '_' placeholder." -> tree.toLoc :: Nil))
      Term.Error
    case Annotated(lhs, rhs) =>
      annot(lhs).fold(term(rhs))(ann =>
        Term.Annotated(ann, term(rhs)))
    case Keywrd(kw) =>
      raise(ErrorReport(msg"Unexpected keyword '${kw.name}' in this position." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def fld(tree: Tree): Ctxl[Elem] = tree match
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, term(lhs), S(term(rhs)))
    case Spread(Keyword.`..`, _, S(trm)) =>
      Spd(false, term(trm))
    case Spread(Keyword.`...`, _, S(trm)) =>
      Spd(true, term(trm))
    case _ => 
      val t = term(tree)
      var flags = FldFlags.empty
      if ModuleChecker.evalsToModule(t)
        then flags = flags.copy(mod = true)
      Fld(flags, t, N)
  
  def unit: Term.Lit = Term.Lit(UnitLit(true))
  
  
  
  def block(sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) =
    block(new Tree.Block(sts))
  
  def block(blk: Tree.Block)(using c: Ctx): (Term.Blk, Ctx) = trace[(Term.Blk, Ctx)](
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
    def go(sts: Ls[Tree], funs: Ls[TermDefinition], annotations: Ls[Annot], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] =
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
        val res = unit
        (Term.Blk(funs reverse_::: acc.reverse, res), ctx)
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
        case N => go(sts, funs, annotations, acc)
        case S((base, importedTrees)) =>
          base match
          case baseId: Ident =>
            ctx.get(baseId.name) match
            case S(baseElem) =>
              val importedNames = importedTrees match
                case N => // "wilcard" open
                  baseElem.symbol match
                  case S(sym: BlockMemberSymbol) if sym.modTree.isDefined =>
                    sym.modTree.get.definedSymbols.map:
                      case (nme, sym) => nme -> Ctx.SelElem(baseElem, sym.nme, S(sym))
                  case _ =>
                    raise(ErrorReport(msg"Wildcard 'open' not supported for this kind of symbol." -> baseId.toLoc :: Nil))
                    Nil
                case S(sts) => sts.flatMap:
                  case id: Ident =>
                    val sym = resolveField(id, baseElem.symbol, id)
                    val e = Ctx.SelElem(baseElem, id.name, sym)
                    id.name -> e :: Nil
                  case t =>
                    raise(ErrorReport(msg"Illegal 'open' statement element." -> t.toLoc :: Nil))
                    Nil
              (ctx elem_++ importedNames).givenIn:
                go(sts, funs, Nil, acc)
            case N =>
              raise(ErrorReport(msg"Name not found: ${baseId.name}" -> baseId.toLoc :: Nil))
              go(sts, funs, Nil, acc)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement base." -> base.toLoc :: Nil))
            go(sts, funs, Nil, acc)
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
          go(sts, funs, Nil, newAcc)
      
      case (hd @ LetLike(`let`, Apps(id: Ident, tups), rhso, N)) :: sts if id.name.headOption.exists(_.isLower) =>
        val sym =
          fieldOrVarSym(LetBind, id)
        log(s"Processing `let` statement $id (${sym}) ${ctx.outer}")
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
          go(sts, funs, Nil, newAcc)
      case (tree @ LetLike(`let`, lhs, S(rhs), N)) :: sts =>
        raise(ErrorReport(msg"Unsupported let binding shape" -> tree.toLoc :: Nil))
        go(sts, funs, Nil, Term.Error :: acc)
      case (hd @ Hndl(id: Ident, cls: Ident, Block(sts_), N)) :: sts =>
        reportUnusedAnnotations
        val res: Term.Blk = ctx.nest(N).givenIn:
          val sym = fieldOrVarSym(HandlerBind, id)
          log(s"Processing `handle` statement $id (${sym}) ${ctx.outer}")
          
          // TODO: shouldn't need uid here
          val derivedClsSym = ClassSymbol(Tree.TypeDef(syntax.Cls, Tree.Error(), N, N), Tree.Ident(s"${cls.name}$$${id.name}$$${State.suid.nextUid}"))
          derivedClsSym.defn = S(ClassDef(
            N, syntax.Cls, derivedClsSym,
            BlockMemberSymbol(derivedClsSym.name, Nil),
            Nil, N, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true)))), List()))
          
          val elabed = ctx.nest(S(derivedClsSym)).givenIn:
            block(sts_)._1
          
          elabed.res match
            case Term.Lit(UnitLit(true)) => 
            case trm => raise(WarningReport(msg"Terms in handler block do nothing" -> trm.toLoc :: Nil))
          
          val tds = elabed.stats.map {
            case td @ TermDefinition(owner, Fun, sym, params, sign, body, resSym, flags, annotations) =>
              params.reverse match
                case ParamList(_, value :: Nil, _) :: newParams =>
                  val newTd = TermDefinition(owner, Fun, sym, newParams.reverse, sign, body, resSym, flags, annotations)
                  S(HandlerTermDefinition(value.sym, newTd))
                case _ => 
                  raise(ErrorReport(msg"Handler function is missing resumption parameter" -> td.toLoc :: Nil))
                  None
                
            case st => 
              raise(ErrorReport(msg"Only function definitions are allowed in handler blocks" -> st.toLoc :: Nil))
              None
          }.collect { case Some(x) => x }
          
          val newAcc = funs ::: Handle(sym, term(cls), derivedClsSym, tds) :: acc
          val newCtx = ctx + (id.name -> sym)
          val body = block(sts)(using newCtx)._1
          Term.Blk(newAcc.reverse, body) // <<<<<<<<<<<<<<<<<<<<<<<<<<< FIXME scope problem (not calling `go`)
        (res, ctx)
      case (tree @ Hndl(_, _, _, N)) :: sts =>
        raise(ErrorReport(msg"Unsupported handle binding shape" -> tree.toLoc :: Nil))
        go(sts, funs, Nil, Term.Error :: acc)
      
      case Def(lhs, rhs) :: sts =>
        reportUnusedAnnotations
        lhs match
        case id: Ident =>
          val r = term(rhs)
          ctx.get(id.name) match
          case S(elem) =>
            elem.symbol match
            case S(sym: LocalSymbol) => go(sts, funs, Nil, DefineVar(sym, r) :: acc)
          case N =>
            // TODO lookup in members? inherited/refined stuff?
            raise(ErrorReport(msg"Name not found: ${id.name}" -> id.toLoc :: Nil))
            go(sts, funs, Nil, Term.Error :: acc)
        case App(base, args) =>
          go(Def(base, InfixApp(args, Keyword.`=>`, rhs)) :: sts, funs, Nil, acc)
        case _ =>
          raise(ErrorReport(msg"Unrecognized definitional assignment left-hand side: ${lhs.describe}"
            -> lhs.toLoc :: Nil)) // TODO BE
          go(sts, funs, Nil, Term.Error :: acc)
      case (td @ TermDef(k, nme, rhs)) :: sts =>
        log(s"Processing term definition $nme")
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        td.name match
          case R(id) =>
            val sym = members.getOrElse(id.name, die)
            val owner = ctx.outer
            val isModMember = owner.exists(_.isInstanceOf[ModuleSymbol])
            val tdf = ctx.nest(N).givenIn:
              // * Add type parameters to context
              val (tps, newCtx1) = td.typeParams match
                case S(t) => typeParams(t)
                case N => (N, ctx)
              // * Add parameters to context
              var newCtx = newCtx1
              val pss = td.paramLists.map: ps =>
                val (res, newCtx2) = params(ps)(using newCtx)
                newCtx = newCtx2
                res
              // * Elaborate signature
              val st = td.annotatedResultType.orElse(newSignatureTrees.get(id.name))
              val s = st.map(term(_)(using newCtx))
              val b = rhs.map(term(_)(using newCtx))
              val r = FlowSymbol(s"‹result of ${sym}›")
              val tdf = TermDefinition(owner, k, sym, pss, s, b, r, 
                TermDefFlags.empty.copy(isModMember = isModMember), annotations)
              sym.defn = S(tdf)
              
              // indicates if the function really returns a module
              val em = b.exists(ModuleChecker.evalsToModule)
              // indicates if the function marks its result as "module"
              val mm = st match
                case Some(TypeDef(Mod, _, N, N)) => true
                case _ => false
              
              // checks rules regarding module methods
              s match
                case N if em => raise:
                  ErrorReport:
                    msg"Functions returning module values must have explicit return types." ->
                    td.head.toLoc :: Nil
                case S(t) if em && ModuleChecker.isTypeParam(t) => raise:
                  ErrorReport:
                    msg"Functions returning module values must have concrete return types." ->
                    td.head.toLoc :: Nil
                case S(_) if em && !mm => raise:
                  ErrorReport:
                    msg"The return type of functions returning module values must be prefixed with module keyword." ->
                    td.head.toLoc :: Nil
                case S(_) if mm && !isModMember => raise:
                  ErrorReport:
                    msg"Only module methods may return module values." ->
                    td.head.toLoc :: Nil
                case _ => ()
              
              tdf
            tdf.k match
            case Fun => go(sts, tdf :: funs, Nil, acc)
            case _ => go(sts, funs, Nil, tdf :: acc)
          case L(d) =>
            reportUnusedAnnotations
            raise(d)
            go(sts, funs, Nil, acc)
      case (td @ TypeDef(k, head, extension, body)) :: sts =>
        assert((k is Als) || (k is Cls) || (k is Mod) || (k is Obj) || (k is Pat), k)
        td.symbName match
        case S(L(d)) => raise(d)
        case _ => ()
        val nme = td.name match
          case R(id) => id
          case L(d) =>
            raise(d)
            return go(sts, funs, Nil, acc)
        val sym = members.getOrElse(nme.name, lastWords(s"Symbol not found: ${nme.name}"))
        var newCtx = ctx.nest(S(td.symbol).collectFirst{
          case s: InnerSymbol => s })
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
        val ps =
          td.paramLists.match
            case Nil => N
            case ps :: Nil => S(ps)
            case ps :: _ =>
              raise:
                ErrorReport:
                  msg"Multiple parameter lists are not supported for this definition." ->
                    td.toLoc :: Nil
              S(ps)
          .map: ps =>
            val (res, newCtx2) =
              given Ctx = newCtx
              params(ps)
            newCtx = newCtx2
            res
        val defn = k match
        case Als =>
          val alsSym = td.symbol.asInstanceOf[TypeAliasSymbol] // TODO improve `asInstanceOf`
          // newCtx.nest(S(alsSym)).givenIn:
          newCtx.nest(N).givenIn:
            assert(ps.isEmpty)
            assert(body.isEmpty)
            val d =
              given Ctx = newCtx
              semantics.TypeDef(alsSym, tps, extension.map(term(_)), N, annotations)
            alsSym.defn = S(d)
            d
        case Pat =>
          val patSym = td.symbol.asInstanceOf[PatternSymbol] // TODO improve `asInstanceOf`
          val owner = ctx.outer
          newCtx.nest(S(patSym)).givenIn:
            assert(body.isEmpty)
            td.extension match
              case N => raise(ErrorReport(msg"Pattern definitions must have a body." -> td.toLoc :: Nil))
              case S(tree) =>
                val (patternParams, extractionParams) = ps match // Filter out pattern parameters.
                  case S(ParamList(_, params, _)) => params.partition:
                    case param @ Param(FldFlags(false, false, false, false, true), _, _) => true
                    case param @ Param(FldFlags(_, _, _, _, false), _, _) => false
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
            log(s"pattern body is ${td.extension}")
            val translate = new ucs.Translator(this)
            val bod = translate(
              patSym.patternParams,
              Nil, // ps.map(_.params).getOrElse(Nil), // TODO[Luyu]: remove pattern parameters
              td.extension.getOrElse(die))
            val pd = PatternDef(owner, patSym, sym, tps, ps, ObjBody(Term.Blk(bod, Term.Lit(UnitLit(true)))), annotations)
            patSym.defn = S(pd)
            pd
        case k: (Mod.type | Obj.type) =>
          val clsSym = td.symbol.asInstanceOf[ModuleSymbol] // TODO: improve `asInstanceOf`
          val owner = ctx.outer
          newCtx.nest(S(clsSym)).givenIn:
            log(s"Processing type definition $nme")
            val cd =
              val (bod, c) = body match
                case S(b: Tree.Block) => block(b)
                // case S(t) => block(t :: Nil)
                case S(t) => ???
                case N => (new Term.Blk(Nil, Term.Lit(UnitLit(true))), ctx)
              ModuleDef(owner, clsSym, sym, tps, ps, k, ObjBody(bod), annotations)
            clsSym.defn = S(cd)
            cd
        case Cls =>
          val clsSym = td.symbol.asInstanceOf[ClassSymbol] // TODO: improve `asInstanceOf`
          val owner = ctx.outer
          newCtx.nest(S(clsSym)).givenIn:
            log(s"Processing type definition $nme")
            val cd =
              val (bod, c) = body match
                case S(b: Tree.Block) => block(b)
                // case S(t) => block(t :: Nil)
                case S(t) => ???
                case N => (new Term.Blk(Nil, Term.Lit(UnitLit(true))), ctx)
              ClassDef(owner, Cls, clsSym, sym, tps, ps, ObjBody(bod), annotations)
            clsSym.defn = S(cd)
            cd
        sym.defn = S(defn)
        go(sts, funs, Nil, defn :: acc)
      case Annotated(annotation, target) :: sts =>
        go(target :: sts, funs, annotations ++ annot(annotation), acc)
      case (st: Tree) :: sts =>
        // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        val res = annotations.foldLeft(term(st)):
          case (acc, ann) => Term.Annotated(ann, acc)
        sts match
        case Nil => (Term.Blk(funs reverse_::: acc.reverse, res), ctx)
        case _ => go(sts, funs, Nil, res :: acc)
    end go
    
    c.withMembers(members, c.outer).givenIn:
      go(blk.desugStmts, Nil, Nil, Nil)
  
  
  def fieldOrVarSym(k: TermDefKind, id: Ident)(using Ctx): LocalSymbol & NamedSymbol =
    if ctx.outer.isDefined then TermSymbol(k, ctx.outer, id)
    else VarSymbol(id)
  
  def param(t: Tree): Ctxl[Opt[Opt[Bool] -> Param]] = t match
    case TypeDef(Mod, inner, N, N) =>
      val ps = param(inner).map(_.mapSecond(p => p.copy(flags = p.flags.copy(mod = true))))
      for p <- ps if p._2.flags.mod do p._2.sign match
        case N =>
          raise(ErrorReport(msg"Module parameters must have explicit types." -> t.toLoc :: Nil))
        case S(ret) if ModuleChecker.isTypeParam(ret) => 
          raise(ErrorReport(msg"Module parameters must have concrete types." -> t.toLoc :: Nil))
        case _ => ()
      ps
    case TypeDef(Pat, inner, N, N) =>
      param(inner).map(_.mapSecond(p => p.copy(flags = p.flags.copy(pat = true))))
    case _ =>
      t.asParam.map: (isSpd, p, t) =>
        isSpd -> Param(FldFlags.empty, fieldOrVarSym(ParamBind, p), t.map(term(_)))
  
  def params(t: Tree): Ctxl[(ParamList, Ctx)] = t match
    case Tup(ps) =>
      val plf = ParamListFlags.empty
      def go(ps: Ls[Tree], acc: Ls[Param], ctx: Ctx): (ParamList, Ctx) =
        ps match
        case Nil => (ParamList(plf, acc.reverse, N), ctx)
        case hd :: tl =>
          param(hd)(using ctx) match
          case S((isSpd, p)) =>
            val newCtx = ctx + (p.sym.name -> p.sym)
            isSpd match
            case S(spdKnd) =>
              if tl.nonEmpty then
                raise(ErrorReport(msg"Spread parameters must be the last in the parameter list." -> hd.toLoc :: Nil))
              (ParamList(plf, acc.reverse, S(p)), newCtx)
            case N => go(tl, p :: acc, newCtx)
          case N =>
            ???
      go(ps, Nil, ctx)
  
  def typeParams(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case TyTup(ps) =>
      val vs = ps.map:
        case id: Ident =>
          val sym = VarSymbol(id)
          sym.decl = S(TyParam(FldFlags.empty, N, sym))
          Param(FldFlags.empty, sym, N)
      (vs, ctx ++ vs.map(p => p.sym.name -> p.sym))
  
  
  def pattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol])] =
    val boundVars = mutable.HashMap.empty[Str, VarSymbol]
    def go(t: Tree): Pattern = t match
      case id @ Ident(name) =>
        val sym = boundVars.getOrElseUpdate(name, VarSymbol(id))
        Pattern.Var(sym)
      // case Tup(fields) =>
      //   val pats = fields.map(
      //     f => pattern(f) match
      //       case (pat, vars) =>
      //         boundVars ++= vars
      //         pat
      //   )
      //   Pattern.Tuple(pats)
      case _ =>
        ???
    (go(t), boundVars.toList)
  
  def importFrom(sts: Tree.Block)(using c: Ctx): (Term.Blk, Ctx) =
    val (res, newCtx) = block(sts)
    // TODO handle name clashes
    (res, newCtx)
  
  
  def topLevel(sts: Tree.Block)(using c: Ctx): (Term.Blk, Ctx) =
    val (res, ctx) = block(sts)
    computeVariances(res)
    (res, ctx)
  
  def computeVariances(s: Statement): Unit =
    val trav = VarianceTraverser()
    def go(s: Statement): Unit = s match
      case TermDefinition(_, k, sym, pss, sign, body, r, _, _) =>
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
  
  object ModuleChecker:
    
    /** Checks if a term is a reference to a type parameter. */
    def isTypeParam(t: Term): Bool = t.symbol
      .filter(_.isInstanceOf[VarSymbol])
      .flatMap(_.asInstanceOf[VarSymbol].decl)
      .exists(_.isInstanceOf[TyParam])
    
    /** Checks if a term evaluates to a module value. */
    def evalsToModule(t: Term): Bool = 
      def isModule(t: Tree): Bool = t match
        case TypeDef(Mod, _, _, _) => true
        case _ => false
      def returnsModule(t: TermDef): Bool = t.annotatedResultType match
        case S(TypeDef(Mod, _, N, N)) => true
        case _ => false
      t match
        case Term.Blk(_, res) => evalsToModule(res)
        case Term.App(lhs, rhs) => lhs.symbol match
          case S(sym: BlockMemberSymbol) => sym.trmTree.exists(returnsModule)
          case _ => false
        case t => t.symbol match
          case S(sym: BlockMemberSymbol) => sym.modTree.exists(isModule)
          case _ => false
  
  class VarianceTraverser(var changed: Bool = true) extends Traverser:
    override def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.TyApp(lhs, targs) =>
        lhs.symbol.flatMap(sym => sym.asTpe orElse sym.asMod) match
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
      case Term.Lit(_) | Term.Error =>
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
    def traverseType(pol: Pol)(f: Elem): Unit = f match
      case f: Fld =>
        traverseType(pol)(f.term)
        f.asc.foreach(traverseType(pol))
    def traverseType(pol: Pol)(f: Param): Unit =
      f.sign.foreach(traverseType(pol))
end Elaborator

type Pol = Opt[Bool]
extension (p: Pol) def ! : Pol = p.map(!_)

