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
  
  private val binaryOps = Ls(
    ",",
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "===",
    "&&", "||")
  private val unaryOps = Set("-", "+", "!", "~")
  private val aliasOps = Map(
    ";" -> ",",
    "+." -> "+",
    "-." -> "-",
    "*." -> "*")

  val reservedNames = binaryOps.toSet ++ aliasOps.keySet + "NaN" + "Infinity"
  
  case class Ctx(outer: Opt[InnerSymbol], parent: Opt[Ctx], env: Map[Str, Ctx.Elem]):
    def +(local: Str -> Symbol): Ctx = copy(outer, env = env + local.mapSecond(Ctx.RefElem(_)))
    def ++(locals: IterableOnce[Str -> Symbol]): Ctx =
      copy(outer, env = env ++ locals.mapValues(Ctx.RefElem(_)))
    def elem_++(locals: IterableOnce[Str -> Ctx.Elem]): Ctx =
      copy(outer, env = env ++ locals)
    def withMembers(members: Iterable[Str -> MemberSymbol[?]], out: Opt[Symbol] = N): Ctx =
      copy(env = env ++ members.map:
        case (nme, sym) => nme -> (
          out orElse outer match
          case S(outer) => Ctx.SelElem(outer, sym.nme, S(sym))
          case N => sym: Ctx.Elem
        )
      )
    def nest(outer: Opt[InnerSymbol]): Ctx = Ctx(outer, Some(this), Map.empty)
    def get(name: Str): Opt[Ctx.Elem] =
      env.get(name).orElse(parent.flatMap(_.get(name)))
    def getOuter: Opt[InnerSymbol] = outer.orElse(parent.flatMap(_.getOuter))
    lazy val allMembers: Map[Str, Symbol] =
      parent.fold(Map.empty)(_.allMembers) ++ env.flatMap:
        case (n, re: Ctx.RefElem) => (n, re.sym) :: Nil
        case _ => Nil // FIXME?
  
  object Ctx:
    abstract class Elem:
      def nme: Str
      def ref(id: Tree.Ident): Term
      def symbol: Opt[Symbol]
    final case class RefElem(val sym: Symbol) extends Elem:
      val nme = sym.nme
      def ref(id: Tree.Ident): Term =
        require(id.name == nme)
        Term.Ref(sym)(id, 666) // TODO 666
      def symbol = S(sym)
    final case class SelElem(val base: Elem, val nme: Str, val symOpt: Opt[Symbol]) extends Elem:
      def ref(id: Tree.Ident): Term =
        // * Note: due to symbolic ops, we may have `id.name =/= nme`;
        // * e.g., we can have `id.name = "|>"` and `nme = "pipe"`.
        Term.Sel(base.ref(Ident(base.nme)),
          new Tree.Ident(nme).withLocOf(id))(symOpt)
      def symbol = symOpt
    given Conversion[Symbol, Elem] = RefElem(_)
    val empty: Ctx = Ctx(N, N, Map.empty)
    // val globalThisSymbol = TermSymbol(ImmutVal, N, Ident("globalThis"))
    val globalThisSymbol = TopLevelSymbol("globalThis")
    val seqSymbol = TermSymbol(ImmutVal, N, Ident(";"))
    def init(using State): Ctx = empty.copy(env = Map(
      "globalThis" -> globalThisSymbol,
    ))
  type Ctxl[A] = Ctx ?=> A
  def ctx: Ctxl[Ctx] = summon
  class State:
    private var curUi = 0
    def nextUid: Int = { curUi += 1; curUi }
import Elaborator.*

class Elaborator(val tl: TraceLogger, val wd: os.Path)
(using val raise: Raise, val state: State)
extends Importer:
  import state.nextUid
  import tl.*
  
  // * Ref allocation skolem UID, preserved
  private val allocSkolemUID = nextUid
  private val allocSkolemSym = VarSymbol(Ident("Alloc"), allocSkolemUID)
  private val allocSkolemDef = TyParam(FldFlags.empty, N, allocSkolemSym)
  allocSkolemSym.decl = S(allocSkolemDef)

  private val builtinOpsMap =
    val baseBuiltins = binaryOps.map: op =>
        op -> BuiltinSymbol(op, binary = true, unary = unaryOps(op), nullary = false)
      .toMap
    baseBuiltins ++ aliasOps.map:
      case (alias, base) => alias -> baseBuiltins(base)
  
  def mkLetBinding(sym: LocalSymbol, rhs: Term): Ls[Statement] =
    LetDecl(sym) :: DefineVar(sym, rhs) :: Nil
  
  def resolveField(srcTree: Tree, base: Opt[Symbol], nme: Ident): Opt[Symbol] =
    base match
    case S(psym: BlockMemberSymbol) =>
      psym.modTree match
      case S(cls) =>
        cls.definedSymbols.get(nme.name) match
        case s @ S(clsSym) => s
        case N =>
          raise(ErrorReport(msg"Module '${cls.symbol.nme}' does not contain member '${nme.name}'" -> srcTree.toLoc :: Nil))
          N
      case N =>
        N
    case _ => N
  
  def cls(tree: Tree): Ctxl[Term] = trace[Term](s"Elab class ${tree.showDbg}", r => s"~> $r"):
    val trm = term(tree)
    trm.symbol match
    case S(cls: ClassSymbol) =>
      trm
    case S(mem: BlockMemberSymbol) =>
      if !mem.hasLiftedClass then trm
      else Term.Sel(trm, Ident("class"))(mem.clsTree.orElse(mem.modTree).map(_.symbol))
    case _ => trm
  
  def term(tree: Tree): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    tree.desugared match
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
        val sym = TempSymbol(nextUid, S(lt), "old")
        Term.Blk(
        LetDecl(sym) :: DefineVar(sym, lt) :: Nil, Term.Try(Term.Blk(
          Term.Assgn(lt, term(rhs)) :: Nil,
          term(bod),
        ), Term.Assgn(lt, sym.ref(id))))
      case _ => ??? // TODO error
    case Handle(id, cls, blk, S(bod)) =>
      term(Block(Handle(id, cls, blk, N) :: bod :: Nil))
    case Handle(id: Ident, cls: Ident, Block(sts), N) =>
      raise(ErrorReport(
        msg"Expected a body for handle bindings in expression position" ->
          tree.toLoc :: Nil))
          
      val sym =
        fieldOrVarSym(Handler, id)
      val newCtx = ctx + (id.name -> sym)
      Term.Handle(sym, term(cls)(using newCtx), ObjBody(block(sts)._1))
      
    case h: Handle =>
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
    case id @ Ident("Alloc") => Term.Ref(allocSkolemSym)(id, 1)
    case id @ Ident(name) =>
      ctx.get(name) match
      case S(sym) => sym.ref(id)
      case N =>
        builtinOpsMap.get(name) match
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
        val sym = VarSymbol(id, nextUid)
        sym.decl = S(TyParam(FldFlags.empty, N, sym)) // TODO vce
        boundVars += id.name -> sym
        sym
      val syms = (tvs.collect:
        case id: Tree.Ident => (genSym(id), N, N)
        case InfixApp(id: Tree.Ident, Keyword.`extends`, ub) => (genSym(id), S(ub), N)
        case InfixApp(id: Tree.Ident, Keyword.`restricts`, lb) => (genSym(id), N, S(lb))
        case InfixApp(InfixApp(id: Tree.Ident, Keyword.`extends`, ub), Keyword.`restricts`, lb) => (genSym(id), S(ub), S(lb))
      )
      if syms.length != tvs.length then
        raise(ErrorReport(msg"Illegal forall annotation." -> tree.toLoc :: Nil))
        Term.Error
      else
        val nestCtx = ctx ++ boundVars
        val bds = syms.map:
          case (sym, ub, lb) => QuantVar(sym, ub.map(ub => term(ub)(using nestCtx)), lb.map(lb => term(lb)(using nestCtx)))
        Term.Forall(bds, term(body)(using nestCtx))
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
    case InfixApp(lhs, Keyword.`is` | Keyword.`and`, rhs) =>
      val des = new Desugarer(tl, this).shorthands(tree)(ctx)
      val nor = new ucs.Normalization(tl)(des)
      Term.IfLike(Keyword.`if`, des)(nor)
    case App(Ident("|"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), true)
    case App(Ident("&"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), false)
    case App(Ident(":="), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.Assgn(term(lhs), term(rhs))
    case App(Ident("#"), Tree.Tup(Sel(pre, idn: Ident) :: (idp: Ident) :: Nil)) =>
      Term.SelProj(term(pre), term(idn), idp)
    case App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: App(Ident(proj), args) :: Nil)) =>
      term(App(App(Ident("#"), Tree.Tup(Sel(pre, Ident(name)) :: Ident(proj) :: Nil)), args))
    case App(Ident("!"), Tree.Tup(rhs :: Nil)) =>
      Term.Deref(term(rhs))
    case App(Ident("~"), Tree.Tup(rhs :: Nil)) =>
      term(rhs)
    case tree @ App(lhs, rhs) =>
      val sym = FlowSymbol("‹app-res›", nextUid)
      Term.App(term(lhs), term(rhs))(tree, sym)
    case Sel(pre, nme) =>
      val preTrm = term(pre)
      val sym = resolveField(nme, preTrm.symbol, nme)
      Term.Sel(preTrm, nme)(sym)
    case tree @ Tup(fields) =>
      Term.Tup(fields.map(fld(_)))(tree)
    case New(body) =>
      body match
      case App(c, Tup(params)) =>
        Term.New(cls(c), params.map(term)).withLocOf(tree)
      case c => // * We'll catch bad `new` targets during type checking
        Term.New(cls(c), Nil).withLocOf(tree)
      // case _ =>
      //   raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
    case Tree.IfLike(kw, split) =>
      val desugared = new Desugarer(tl, this).termSplit(split, identity)(Split.End)(ctx)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(desugared)}")
      val normalized = new ucs.Normalization(tl)(desugared)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(normalized)}")
      Term.IfLike(kw, desugared)(normalized)
    case Tree.Quoted(body) => Term.Quoted(term(body))
    case Tree.Unquoted(body) => Term.Unquoted(term(body))
    case Tree.Case(branches) =>
      val scrut = VarSymbol(Ident("caseScrut"), nextUid)
      val desugarer = new Desugarer(tl, this)
      val des = desugarer.patternSplit(branches, scrut)(Split.End)(ctx)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(des)}")
      val nor = new ucs.Normalization(tl)(des)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(nor)}")
      Term.Lam(Param(FldFlags.empty, scrut, N) :: Nil, Term.IfLike(Keyword.`if`, des)(nor))
    case Modified(Keyword.`return`, kwLoc, body) =>
      Term.Ret(term(body))
    case Modified(Keyword.`do`, kwLoc, body) =>
      Term.Blk(term(body) :: Nil, unit)
    case Tree.Region(id: Tree.Ident, body) =>
      val sym = VarSymbol(id, nextUid)
      val nestCtx = ctx + (id.name -> sym)
      Term.Region(sym, term(body)(using nestCtx))
    case Tree.RegRef(reg, value) => Term.RegRef(term(reg), term(value))
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
          val sym = FlowSymbol("‹app-res›", nextUid)
          val fl = Fld(FldFlags.empty, res, N)
          val app = Term.App(term(f), Term.Tup(
            fl :: args.map(fld))(tup))(ap, sym)
          go(app, trees)
        case (ap @ App(f, tup @ Tup(args))) :: trees =>
          val sym = FlowSymbol("‹app-res›", nextUid)
          go(Term.App(term(f),
              Term.Tup(Fld(FldFlags.empty, acc, N) :: args.map(fld))(tup)
            )(ap, sym), trees)
        case Block(sts) :: trees =>
          go(acc, sts ::: trees)
        case tree :: trees =>
          raise(ErrorReport(msg"Illegal juxtaposition right-hand side." -> tree.toLoc :: Nil))
          go(acc, trees)
      
      go(term(lhs), rhs :: Nil)
    case Open(body) =>
      raise(ErrorReport(msg"Illegal position for 'open' statement." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def fld(tree: Tree): Ctxl[Fld] = tree match
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, term(lhs), S(term(rhs)))
    case _ => Fld(FldFlags.empty, term(tree), N)
  
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
          case td if td.signature.isDefined => td.signature.get
        sig.foreach: sig =>
          newSignatureTrees += name -> sig
    
    // TODO extract this into a separate method
    @tailrec
    def go(sts: Ls[Tree], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] = sts match
      case Nil =>
        val res = unit
        (Term.Blk(acc.reverse, res), ctx)
      case Open(bod) :: sts =>
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
        case N => go(sts, acc)
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
                go(sts, acc)
            case N =>
              raise(ErrorReport(msg"Name not found: ${baseId.name}" -> baseId.toLoc :: Nil))
              go(sts, acc)
          case _ =>
            raise(ErrorReport(msg"Illegal 'open' statement base." -> base.toLoc :: Nil))
            go(sts, acc)
      case (m @ Modified(Keyword.`import`, absLoc, arg)) :: sts =>
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
          go(sts, newAcc)
      case (hd @ LetLike(`let`, Apps(id: Ident, tups), rhso, N)) :: sts if id.name.headOption.exists(_.isLower) =>
        val sym =
          fieldOrVarSym(LetBind, id)
        log(s"Processing `let` statement $id (${sym}) ${ctx.outer}")
        val newAcc = rhso match
          case S(rhs) =>
            val rrhs = tups.foldRight(rhs):
              Tree.InfixApp(_, Keyword.`=>`, _)
            mkLetBinding(sym, term(rrhs)) reverse_::: acc
          case N =>
            if tups.nonEmpty then
              raise(ErrorReport(msg"Expected a right-hand side for let bindings with parameters" -> hd.toLoc :: Nil))
            LetDecl(sym) :: acc
        (ctx + (id.name -> sym)) givenIn:
          go(sts, newAcc)
      case (tree @ LetLike(`let`, lhs, S(rhs), N)) :: sts =>
        raise(ErrorReport(msg"Unsupported let binding shape" -> tree.toLoc :: Nil))
        go(sts, Term.Error :: acc)
      case (hd @ Handle(id: Ident, cls: Ident, Block(sts_), N)) :: sts =>
        val sym =
          fieldOrVarSym(LetBind, id)
        log(s"Processing `handle` statement $id (${sym}) ${ctx.outer}")
        val newAcc = Term.Handle(sym, term(cls), ObjBody(block(sts_)._1)) :: acc
        ctx + (id.name -> sym) givenIn:
          go(sts, newAcc)
      case (tree @ Handle(_, _, _, N)) :: sts =>
        raise(ErrorReport(msg"Unsupported handle binding shape" -> tree.toLoc :: Nil))
        go(sts, Term.Error :: acc)

      case Def(lhs, rhs) :: sts =>
        lhs match
        case id: Ident =>
          val r = term(rhs)
          ctx.get(id.name) match
          case S(elem) =>
            elem.symbol match
            case S(sym: LocalSymbol) => go(sts, DefineVar(sym, r) :: acc)
          case N =>
            // TODO lookup in members? inherited/refined stuff?
            raise(ErrorReport(msg"Name not found: ${id.name}" -> id.toLoc :: Nil))
            go(sts, Term.Error :: acc)
        case App(base, args) =>
          go(Def(base, InfixApp(args, Keyword.`=>`, rhs)) :: sts, acc)
        case _ =>
          raise(ErrorReport(msg"Unrecognized definitional assignment left-hand side: ${lhs.describe}"
            -> lhs.toLoc :: Nil)) // TODO BE
          go(sts, Term.Error :: acc)
      case (td @ TermDef(k, nme, rhs)) :: sts =>
        log(s"Processing term definition $nme")
        td.name match
          case R(id) =>
            val sym = members.getOrElse(id.name, die)
            val owner = ctx.outer
            val tdf = ctx.nest(N).givenIn:
              // * Add type parameters to context
              val (tps, newCtx1) = td.typeParams match
                case S(t) => typeParams(t)
                case N => (N, ctx)
              // * Add parameters to context
              val (pss, newCtx) = 
                td.paramLists.foldLeft(Ls[ParamList](), newCtx1):
                  case ((pss, ctx), ps) => 
                    val (qs, newCtx) = params(ps)(using ctx)
                    (pss :+ ParamList(ParamListFlags.empty, qs), newCtx)
              val b = rhs.map(term(_)(using newCtx))
              val r = FlowSymbol(s"‹result of ${sym}›", nextUid)
              val tdf = TermDefinition(owner, k, sym, pss,
                td.signature.orElse(newSignatureTrees.get(id.name)).map(term), b, r)
              sym.defn = S(tdf)
              tdf
            go(sts, tdf :: acc)
          case L(d) =>
            raise(d)
            go(sts, acc)
      case (td @ TypeDef(k, head, extension, body)) :: sts =>
        assert((k is Als) || (k is Cls) || (k is Mod), k)
        val nme = td.name match
          case R(id) => id
          case L(d) =>
            raise(d)
            new Ident("<error>") // TODO improve
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
              val vs = VarSymbol(id, nextUid)
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
              semantics.TypeDef(alsSym, tps, extension.map(term), N)
            alsSym.defn = S(d)
            d
        case Mod =>
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
              ModuleDef(owner, clsSym, tps, ps, ObjBody(bod))
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
              ClassDef(owner, Cls, clsSym, tps, ps, ObjBody(bod))
            clsSym.defn = S(cd)
            cd
        go(sts, defn :: acc)
        
      case Modified(Keyword.`abstract`, absLoc, body) :: sts =>
        ???
        // TODO: pass abstract to `go`
        go(body :: sts, acc)
      case Modified(Keyword.`declare`, absLoc, body) :: sts =>
        ???
        // TODO: pass declare to `go`
        go(body :: sts, acc)
      case (result: Tree) :: Nil =>
        val res = term(result)
        (Term.Blk(acc.reverse, res), ctx)
      case (st: Tree) :: sts =>
        val res = term(st) // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        go(sts, res :: acc)
    end go
    
    c.withMembers(members, c.outer).givenIn:
      go(blk.desugStmts, Nil)
  
  
  def fieldOrVarSym(k: TermDefKind, id: Ident)(using Ctx): LocalSymbol & NamedSymbol =
    if ctx.outer.isDefined then TermSymbol(k, ctx.outer, id)
    else VarSymbol(id, nextUid)
  
  def param(t: Tree): Ctxl[Ls[Param]] = t.param.map: (p, t) =>
    Param(FldFlags.empty, fieldOrVarSym(ParamBind, p), t.map(term))
  
  def params(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case Tup(ps) =>
      val res = ps.flatMap(param)
      (res, ctx ++ res.map(p => p.sym.name -> p.sym))
  
  def typeParams(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case TyTup(ps) =>
      val vs = ps.map:
        case id: Ident =>
          val sym = VarSymbol(id, nextUid)
          sym.decl = S(TyParam(FldFlags.empty, N, sym))
          Param(FldFlags.empty, sym, N)
      (vs, ctx ++ vs.map(p => p.sym.name -> p.sym))
  
  
  def pattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol])] =
    val boundVars = mutable.HashMap.empty[Str, VarSymbol]
    def go(t: Tree): Pattern = t match
      case id @ Ident(name) =>
        val sym = boundVars.getOrElseUpdate(name, VarSymbol(id, nextUid))
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
      case TermDefinition(_, k, sym, pss, sign, body, r) =>
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
        lhs.symbol.flatMap(_.asTpe) match
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
      case Term.Forall(_, body) =>
        traverseType(pol)(body)
      case Term.WildcardTy(in, out) =>
        in.foreach(t => traverseType(pol.!)(t))
        out.foreach(t => traverseType(pol)(t))
      case Term.CompType(lhs, rhs, _) => () // TODO:
      case Term.Sel(bse, nme) =>
        traverseType(pol)(bse) // FIXME: probably wrong for what we want to do
      case Term.Tup(fields) =>
        // fields.foreach(f => traverseType(pol)(f.value))
        fields.foreach(traverseType(pol))
      // case _ => ???
    def traverseType(pol: Pol)(f: Fld): Unit =
      traverseType(pol)(f.value)
      f.asc.foreach(traverseType(pol))
    def traverseType(pol: Pol)(f: Param): Unit =
      f.sign.foreach(traverseType(pol))
end Elaborator

type Pol = Opt[Bool]
extension (p: Pol) def ! : Pol = p.map(!_)

