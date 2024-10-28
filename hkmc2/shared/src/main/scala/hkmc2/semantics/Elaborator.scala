package hkmc2
package semantics


import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.*
import Tree.*
import hkmc2.Message.MessageContext

import Keyword.{`let`, `set`}


object Elaborator:
  case class Ctx(outer: Opt[MemberSymbol[?]], parent: Opt[Ctx], members: Map[Str, Symbol], locals: Map[Str, LocalSymbol]):
    def +(local: (Str, BlockLocalSymbol)): Ctx = copy(outer, locals = locals + local)
    def nest(outer: Opt[MemberSymbol[?]]): Ctx = Ctx(outer, Some(this), Map.empty, Map.empty)
    def get(name: Str): Opt[Symbol] =
      locals.get(name).orElse(members.get(name)).orElse(parent.flatMap(_.get(name)))
    lazy val allMembers: Map[Str, Symbol] = parent.fold(Map.empty)(_.allMembers) ++ members
  object Ctx:
    val empty: Ctx = Ctx(N, N, Map.empty, Map.empty)
    val globalThisSymbol = TermSymbol(ImmutVal, N, Ident("globalThis"))
    val errorSymbol = ClassSymbol(S(globalThisSymbol), Ident("Error"))
    val seqSymbol = TermSymbol(ImmutVal, N, Ident(";"))
    def init(using State): Ctx = empty.copy(members = Map(
      "globalThis" -> globalThisSymbol,
      "console" -> TermSymbol(ImmutVal, N, Ident("console")),
      "process" -> TermSymbol(ImmutVal, N, Ident("process")),
      "fs" -> TermSymbol(ImmutVal, N, Ident("fs")),
      "String" -> TermSymbol(ImmutVal, N, Ident("String")),
      "Error" -> errorSymbol,
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
  
  def mkLetBinding(sym: LocalSymbol, rhs: Term): Ls[Statement] =
    LetDecl(sym) :: DefineVar(sym, rhs) :: Nil
  
  def term(tree: Tree): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    tree.desugared match
    case Block(s :: Nil) =>
      term(s)
    case Block(sts) =>
      block(sts)._1
    case lit: Literal =>
      Term.Lit(lit)
    case LetLike(`let`, lhs, rhso, S(bod)) =>
      term(Block(LetLike(`let`, lhs, rhso, N) :: bod :: Nil))
    case LetLike(`let`, lhs, S(rhs), N) =>
      raise(ErrorReport(
        msg"Expected a right-hand side for let bindings in expression position" ->
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
    case Ident("true") => Term.Lit(Tree.BoolLit(true))
    case Ident("false") => Term.Lit(Tree.BoolLit(false))
    case id @ Ident("Alloc") => Term.Ref(allocSkolemSym)(id, 1)
    case id @ Ident(name) =>
      ctx.get(name) match
      case S(sym) => sym.ref(id)
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
        val nestCtx = ctx.copy(locals = ctx.locals ++ boundVars)
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
      Term.If(des)(nor)
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
      Term.Sel(term(pre), nme)
    case tree @ Tup(fields) =>
      Term.Tup(fields.map(fld(_)))(tree)
    case New(body) =>
      body match
      case App(cls, Tup(params)) =>
        Term.New(term(cls), params.map(term)).withLocOf(tree)
      case cls => // we'll catch bad `new` targets during type checking
        Term.New(term(cls), Nil).withLocOf(tree)
      // case _ =>
      //   raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
    case Tree.If(split) =>
      val desugared = new Desugarer(tl, this).termSplit(split, identity)(Split.Nil)(ctx)
      scoped("ucs:desugared"):
        log(s"Desugared:\n${Split.display(desugared)}")
      val normalized = new ucs.Normalization(tl)(desugared)
      scoped("ucs:normalized"):
        log(s"Normalized:\n${Split.display(normalized)}")
      Term.If(desugared)(normalized)
    case IfElse(InfixApp(InfixApp(scrutinee, Keyword.`is`, ctor @ Ident(cls)), Keyword.`then`, cons), alts) =>
      ctx.get(cls) match
        case S(sym: ClassSymbol) =>
          val scrutTerm = term(scrutinee)
          val scrutVar = TempSymbol(nextUid, S(scrutTerm), "scrut")
          val body = Split.Let(scrutVar, scrutTerm, Branch(
            scrutVar.ref(),
            Pattern.Class(sym, N, true)(ctor),
            Split.default(term(cons))
          ) :: Split.default(term(alts)))
          Term.If(body)(body)
        case _ =>
          raise(ErrorReport(msg"Illegal pattern $cls." -> tree.toLoc :: Nil))
          Term.Error
    case IfElse(InfixApp(cond, Keyword.`then`, cons), alts) =>
      val scrutTerm = term(cond)
      val scrutVar = TempSymbol(nextUid, S(scrutTerm), "scrut")
      val body = Split.Let(scrutVar, scrutTerm, Branch(
        scrutVar.ref(),
        Split.default(term(cons))
      ) :: Split.default(term(alts)))
      Term.If(body)(body)
    case Tree.Quoted(body) => Term.Quoted(term(body))
    case Tree.Unquoted(body) => Term.Unquoted(term(body))
    case Tree.Case(Block(branches)) => branches.lastOption match
      case S(InfixApp(id: Ident, Keyword.`then`, dflt)) =>
        val sym = VarSymbol(id, nextUid)
        val nestCtx = ctx.copy(locals = ctx.locals ++ Ls(id.name -> sym))
        val body = branches.dropRight(1).foldRight(Split.default(term(dflt)(using nestCtx))):
          case (InfixApp(target, Keyword.`then`, cons), res) =>
            val scrutIdent = Ident("scrut"): Ident
            val cond = term(App(Ident("=="), Tree.Tup(id :: target :: Nil)))(using nestCtx)
            val scrut = TempSymbol(nextUid, S(cond), "scrut")
            Split.Let(scrut, cond, Branch(
              scrut.ref(),
              Pattern.LitPat(Tree.BoolLit(true)),
              Split.default(term(cons)(using nestCtx))
            ) :: res)
          case _ =>
            raise(ErrorReport(msg"Unsupported case branch." -> tree.toLoc :: Nil))
            Split.default(Term.Error)
        Term.Lam(Param(FldFlags.empty, sym, N) :: Nil, Term.If(body)(body))
      case _ =>
        raise(ErrorReport(msg"Unsupported default case branch." -> tree.toLoc :: Nil))
        Term.Error
    case Modified(Keyword.`return`, kwLoc, body) =>
      Term.Ret(term(body))
    case Tree.Region(id: Tree.Ident, body) =>
      val sym = VarSymbol(id, nextUid)
      val nestCtx = ctx.copy(locals = ctx.locals ++ Ls(id.name -> sym))
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
  
  
  
  
  def block(_sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) = trace[(Term.Blk, Ctx)](
    pre = s"Elab block ${_sts.toString.truncate(30, "[...]")} ${ctx.outer}", r => s"~> ${r._1}"
  ):
    
    val sts = _sts.map(_.desugared)
    val newMembers = mutable.Map.empty[Str, MemberSymbol[?]] // * Definitions with implementations
    val newSignatures = mutable.Map.empty[Str, MemberSymbol[?]] // * Definitions containing only signatures
    val newSignatureTrees = mutable.Map.empty[Str, Tree] // * Store trees of signatures, passing them to definition objects
    
    @tailrec def preprocessStatement(statement: Tree): Unit = statement match
      case Open(body) =>
        body match
        case _ =>
          raise(ErrorReport(msg"Illegal 'open' statement shape." -> body.toLoc :: Nil))
      case td: TermDef =>
        log(s"Found TermDef ${td.name}")
        td.name match
          case R(id) =>
            lazy val sym = TermSymbol(td.k, ctx.outer, id)
            val members = if td.signature.isEmpty then newMembers else newSignatures
            members.get(id.name) match
              case S(sym) =>
                raise(ErrorReport(msg"Duplicate definition of ${id.name}" -> td.toLoc
                  :: msg"aready defined here" -> id.toLoc :: Nil))
              case N =>
                members += id.name -> sym
                td.signature.foreach(newSignatureTrees += id.name -> _)
            td.symbolicName match
              case S(id @ Ident(nme)) =>
                members.get(nme) match
                  case S(sym) =>
                    raise(ErrorReport(msg"Duplicate definition of $nme" -> td.toLoc
                      :: msg"aready defined here" -> id.toLoc :: Nil))
                  case N =>
                    members += nme -> sym
                    td.signature.foreach(newSignatureTrees += id.name -> _)
              case N =>
          case L(d) => raise(d)
      case td: TypeDef =>
        log(s"Found TypeDef ${td.name}")
        td.name match
          case R(id) =>
            lazy val s =
              td.k match
                case Als => TypeAliasSymbol(id)
                // case Cls => // TODO
                case _ =>
                  ClassSymbol(ctx.outer, id)
            newMembers.get(id.name) match
              // TODO pair up companions
              case S(sym) =>
                raise(ErrorReport(msg"Duplicate definition of ${id.name}" -> td.toLoc
                  :: msg"aready defined here" -> id.toLoc :: Nil))
              case N =>
                newMembers += id.name -> s
            td.symName match
              case S(id @ Ident(nme)) =>
                newMembers.get(nme) match
                  case S(sym) =>
                    raise(ErrorReport(msg"Duplicate definition of $nme" -> td.toLoc
                      :: msg"aready defined here" -> id.toLoc :: Nil))
                  case N =>
                    newMembers += nme -> s
              case S(_) | N =>
          case L(d) => raise(d)
      case Modified(Keyword.`abstract`, absLoc, body) =>
        // TODO: Handle abstract
        preprocessStatement(body)
      case Modified(Keyword.`declare`, absLoc, body) =>
        // TODO: Handle abstract
        preprocessStatement(body)
      case tree =>
        log(s"Found something else $tree")
    end preprocessStatement
    sts.foreach(preprocessStatement)
    
    newSignatures.foreach:
      case (name, sym) =>
        if !newMembers.contains(name) then
          newMembers += name -> sym
    
    @tailrec
    def go(sts: Ls[Tree], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] = sts match
      case Nil =>
        val res = unit
        (Term.Blk(acc.reverse, res), ctx)
      case Open(_) :: sts => go(sts, acc)
      case (m @ Modified(Keyword.`import`, absLoc, arg)) :: sts =>
        val (newCtx, newAcc) = arg match
          case Tree.StrLit(path) =>
            val stmt = importPath(path)
            (ctx.copy(locals = ctx.locals + (stmt.sym.name -> stmt.sym)),
            stmt.withLocOf(m) :: acc)
          case _ =>
            raise(ErrorReport(
              msg"Expected string literal after 'import' keyword" ->
              arg.toLoc :: Nil))
            (ctx, acc)
        newCtx.givenIn:
          go(sts, newAcc)
      case (hd @ LetLike(`let`, Apps(id, tups), rhso, N)) :: sts if id.name.headOption.exists(_.isLower) =>
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
        ctx.copy(locals = ctx.locals + (id.name -> sym)) givenIn:
          go(sts, newAcc)
      case (tree @ LetLike(`let`, lhs, S(rhs), N)) :: sts =>
        raise(ErrorReport(msg"Unsupported let binding shape" -> tree.toLoc :: Nil))
        go(sts, Term.Error :: acc)
      case Def(lhs, rhs) :: sts =>
        lhs match
        case id: Ident =>
          val r = term(rhs)
          ctx.get(id.name) match
          case S(sym) =>
            sym match
            case sym: LocalSymbol => go(sts, DefineVar(sym, r) :: acc)
          case N =>
            // TODO lookup in members? inherited/refined stuff?
            raise(ErrorReport(msg"Name not found: ${id.name}" -> id.toLoc :: Nil))
            go(sts, Term.Error :: acc)
        case _ =>
          raise(ErrorReport(msg"Wrong number of type arguments" -> lhs.toLoc :: Nil)) // TODO BE
          go(sts, Term.Error :: acc)
      case (td @ TermDef(k, nme, rhs)) :: sts =>
        log(s"Processing term definition $nme")
        td.name match
          case R(id) =>
            val sym = newMembers(id.name).asInstanceOf[TermSymbol] // TODO improve
            val tdf = ctx.nest(N).givenIn:
              // Add type parameters to context
              val (tps, newCtx1) = td.typeParams match
                case S(t) => typeParams(t)
                case N => (N, ctx)
              // Add parameters to context
              val (ps, newCtx) = td.params match
                case S(ts) => // Go through all parameter lists
                  ts.foldLeft((Ls[Param](), newCtx1)):
                    case ((ps, ctx), t) => params(t)(using ctx).mapFirst(ps ++ _)
                  .mapFirst(some)
                case N => (N, newCtx1)
              val b = rhs.map(term(_)(using newCtx))
              val r = FlowSymbol(s"‹result of ${sym}›", nextUid)
              val tdf = TermDefinition(k, sym, ps,
                td.signature.orElse(newSignatureTrees.get(id.name)).map(term), b, r)
              sym.defn = S(tdf)
              tdf
            go(sts, tdf :: acc)
          case L(d) => go(sts, acc) // error already raised in newMembers initialization
      case TypeDef(k, head, extension, body) :: sts =>
        assert((k is Als) || (k is Cls) || (k is Mod), k)
        def processHead(head: Tree): Ctxl[(Ident, Ls[TyParam], Opt[Ls[Param]], Ctx)] =
          head match
          case TyApp(base, tparams) =>
            
            val (name, tas, as, newCtx) = processHead(base)
            // TODO reject duplicated tas, out of order as
            
            val tps =
              given Ctx = newCtx
              tparams.flatMap: targ =>
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
            (name, tps, as, newCtx.copy(locals = ctx.locals ++ tps.map(tp => tp.sym.name -> tp.sym)))
          case App(base, args) =>
            
            val (name, tas, as, newCtx) = processHead(base)
            // TODO reject duplicated as
            
            val (ps, newCtx2) =
              given Ctx = newCtx
              params(args)
            (name, tas, S(ps), newCtx2)
          case id: Ident =>
            (id, Nil, N, ctx)
          case InfixApp(lhs, Keyword.`:`, rhs) =>
            // Elaborate the signature
            processHead(lhs)
          case InfixApp(derived, Keyword.`extends`, base) =>
            processHead(derived)
          case Jux(lhs, rhs) =>
            processHead(rhs)
          // case _ => ???

          // case _ => ???
        val (nme, _, _, _) = processHead(head) // ! FIXME dumb!!!! recomputation
        val defn = k match
        case Als =>
          val sym = newMembers(nme.name).asInstanceOf[TypeAliasSymbol] // TODO improve
          ctx.nest(S(sym)).givenIn:
            val (nme, tps, ps, newCtx) = processHead(head)
            assert(ps.isEmpty)
            assert(body.isEmpty)
            val d =
              given Ctx = newCtx
              semantics.TypeDef(sym, tps, extension.map(term), N)
            sym.defn = S(d)
            d
        case k: ClsLikeKind =>
          val sym = newMembers.getOrElse(nme.name, ???).asInstanceOf[ClassSymbol] // TODO improve
          ctx.nest(S(sym)).givenIn:
            val (nme, tps, ps, newCtx) = processHead(head)
            log(s"Processing type definition $nme")
            val cd =
              given Ctx = newCtx
              val (bod, c) = body match
                case S(Tree.Block(sts)) => block(sts)
                case S(t) => block(t :: Nil)
                case N => (new Term.Blk(Nil, Term.Lit(UnitLit(true))), ctx)
              ClassDef(k, sym, tps, ps, ObjBody(bod))
            sym.defn = S(cd)
            cd
        go(sts, defn :: acc)
      case Modified(Keyword.`abstract`, absLoc, body) :: sts =>
        // TODO: pass abstract to `go`
        go(body :: sts, acc)
      case Modified(Keyword.`declare`, absLoc, body) :: sts =>
        // TODO: pass declare to `go`
        go(body :: sts, acc)
      case (result: Tree) :: Nil =>
        val res = term(result)
        (Term.Blk(acc.reverse, res), ctx)
      case (st: Tree) :: sts =>
        val res = term(st) // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        go(sts, res :: acc)
    end go
    
    c.copy(members = c.members ++ newMembers).givenIn:
      sts match
        case (_: TermDef | _: TypeDef) :: _ => go(sts, Nil)
        // case s :: Nil => (term(s), ctx)
        case _ => go(sts, Nil)
  
  
  def fieldOrVarSym(k: TermDefKind, id: Ident)(using Ctx): LocalSymbol & NamedSymbol =
    if ctx.outer.isDefined then TermSymbol(k, ctx.outer, id)
    else VarSymbol(id, nextUid)
  
  def param(t: Tree): Ctxl[Ls[Param]] = t match
    case id: Ident =>
      Param(FldFlags.empty, fieldOrVarSym(ParamBind, id), N) :: Nil
    case InfixApp(lhs: Ident, Keyword.`:`, rhs) =>
      Param(FldFlags.empty, fieldOrVarSym(ParamBind, lhs), S(term(rhs))) :: Nil
    case App(Ident(","), list) => params(list)._1
    case TermDef(ImmutVal, inner, _) => param(inner)
  
  def params(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case Tup(ps) =>
      val res = ps.flatMap(param)
      (res, ctx.copy(locals = ctx.locals ++ res.map(p => p.sym.name -> p.sym)))
  
  def typeParams(t: Tree): Ctxl[(Ls[Param], Ctx)] = t match
    case TyTup(ps) =>
      val vs = ps.map:
        case id: Ident =>
          val sym = VarSymbol(id, nextUid)
          sym.decl = S(TyParam(FldFlags.empty, N, sym))
          Param(FldFlags.empty, sym, N)
      (vs, ctx.copy(locals = ctx.locals ++ vs.map(p => p.sym.name -> p.sym)))
  
  
  def pattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol])] =
    val boundVars = mutable.HashMap.empty[Str, VarSymbol]
    def go(t: Tree): Pattern = t match
      case id @ Ident(name) =>
        val sym = boundVars.getOrElseUpdate(name, VarSymbol(id, nextUid))
        Pattern.Var(sym)
      case Tup(fields) =>
        val pats = fields.map(
          f => pattern(f) match
            case (pat, vars) =>
              boundVars ++= vars
              pat
        )
        Pattern.Tuple(pats)
      case _ =>
        ???
    (go(t), boundVars.toList)
  
  def importFrom(sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) =
    val (res, newCtx) = block(sts)
    // TODO handle name clashes
    (res, newCtx)
  
  
  def topLevel(sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) =
    val (res, ctx) = block(sts)
    computeVariances(res)
    (res, ctx)
  
  def computeVariances(s: Statement): Unit =
    val trav = VarianceTraverser()
    def go(s: Statement): Unit = s match
      case TermDefinition(k, sym, ps, sign, body, r) =>
        ps.foreach(_.foreach(trav.traverseType(S(false))))
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
        lhs.resolveSymbol match
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
              TODO(sym->sym.uid)
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
          case S(sym) => ???
          case N => ???
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

