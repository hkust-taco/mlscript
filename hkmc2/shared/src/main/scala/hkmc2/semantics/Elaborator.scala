package hkmc2
package semantics


import scala.collection.mutable
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.*
import Tree.*
import hkmc2.Message.MessageContext


object Elaborator:
  case class Ctx(parent: Opt[Ctx], members: Map[Str, Symbol], locals: Map[Str, VarSymbol]):
    def +(local: (Str, VarSymbol)): Ctx = copy(locals = locals + local)
  object Ctx:
    val empty: Ctx = Ctx(N, Map.empty, Map.empty)
  type Ctxl[A] = Ctx ?=> A
  def ctx: Ctxl[Ctx] = summon
  class State:
    private var curUi = 0
    def nextUid: Int = { curUi += 1; curUi }
import Elaborator.*

class Elaborator(tl: TraceLogger)(using raise: Raise, state: State):
  import state.nextUid
  import tl.*
  
  // * Ref allocation skolem UID, preserved
  private val allocSkolemUID = nextUid
  private val allocSkolemSym = VarSymbol(Ident("Alloc"), allocSkolemUID)
  private val allocSkolemDef = TyParam(FldFlags.empty, N, allocSkolemSym)
  allocSkolemSym.decl = S(allocSkolemDef)
  
  def term(tree: Tree): Ctxl[Term] =
  trace[Term](s"Elab term ${tree.showDbg}", r => s"~> $r"):
    tree match
    case Block(s :: Nil) =>
      term(s)
    case Block(sts) =>
      block(sts)._1
    case lit: Literal =>
      Term.Lit(lit)
    case Let(lhs, rhs, bodo) =>
      val (pat, syms, optTup) = letPattern(lhs)
      val r = term(rhs)(using optTup match // TODO: dedup with the other usage
        case S(tup) =>
          val ctx1 = ctx.copy(locals = ctx.locals ++ syms)
          val (_, ctx2) = params(tup)(using ctx1)
          ctx2
        case N => ctx)
      val b = bodo.map(term(_)(using ctx.copy(locals = ctx.locals ++ syms))).getOrElse(unit)
      Term.Blk(List(LetBinding(pat, r)), b)
    case Ident("true") => Term.Lit(Tree.BoolLit(true))
    case Ident("false") => Term.Lit(Tree.BoolLit(false))
    case id @ Ident("Alloc") => Term.Ref(allocSkolemSym)(id, 1)
    case id @ Ident(name) =>
      ctx.locals.get(name) match
        case S(sym) => sym.ref(id)
        case N =>
          ctx.members.get(name) match
            case S(sym) => sym.ref(id)
            case N =>
              raise(ErrorReport(msg"Name not found: $name" -> tree.toLoc :: Nil))
              Term.Error
    case TyApp(lhs, targs) =>
      Term.TyApp(term(lhs), targs.map {
        case Modified(Keyword.`in`, arg) => Term.WildcardTy(S(term(arg)), N)
        case Modified(Keyword.`out`, arg) => Term.WildcardTy(N, S(term(arg)))
        case Tup(Modified(Keyword.`in`, arg1) :: Modified(Keyword.`out`, arg2) :: Nil) =>
          Term.WildcardTy(S(term(arg1)), S(term(arg2)))
        case arg => term(arg)
      })
    case InfixApp(TyTup(tvs), Keyword.`->`, body) =>
      val boundVars = mutable.HashMap.empty[Str, VarSymbol]
      val bds = tvs.collect:
        case id: Tree.Ident =>
          val sym = VarSymbol(id, nextUid)
          sym.decl = S(TyParam(FldFlags.empty, N, sym)) // TODO vce
          boundVars += id.name -> sym
          sym          
      if bds.length != tvs.length then
        raise(ErrorReport(msg"Illegal forall annotation." -> tree.toLoc :: Nil))
        Term.Error
      else
        Term.Forall(bds, term(body)(using ctx.copy(locals = ctx.locals ++ boundVars)))
    case InfixApp(lhs, Keyword.`->`, Effectful(eff, rhs)) =>
      Term.FunTy(term(lhs), term(rhs), S(term(eff)))
    case InfixApp(lhs, Keyword.`->`, rhs) =>
      Term.FunTy(term(lhs), term(rhs), N)
    case InfixApp(lhs, Keyword.`=>`, rhs) =>
      val (syms, nestCtx) = params(lhs)
      Term.Lam(syms, term(rhs)(using nestCtx))
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Term.Asc(term(lhs), term(rhs))
    case InfixApp(lhs, Keyword.`is` | Keyword.`and`, rhs) =>
      Term.If(new Desugarer(tl, this).shorthands(tree)(ctx))
    case App(Ident("|"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), true)
    case App(Ident("&"), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.CompType(term(lhs), term(rhs), false)
    case App(Ident(":="), Tree.Tup(lhs :: rhs :: Nil)) =>
      Term.Set(term(lhs), term(rhs))
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
    case New(body) => body match
      case App(Ident(cls), Tup(params)) =>
        ctx.members.get(cls) match
          case S(sym: ClassSymbol) => Term.New(sym, params.map(term))
          case _ =>
            raise(ErrorReport(msg"Class $cls not found." -> tree.toLoc :: Nil))
            Term.Error
      case _ =>
        raise(ErrorReport(msg"Illegal new expression." -> tree.toLoc :: Nil))
        Term.Error
    case Tree.If(split) =>
      log(s"UCS translation started")
      val desugarer = new Desugarer(tl, this)
      val topmost = desugarer.termSplit(split, identity)(Split.Nil)(ctx)
      log(s"Desugared if: \n${Split.display(topmost)}")
      Term.If(topmost)
    case IfElse(InfixApp(InfixApp(scrutinee, Keyword.`is`, Ident(cls)), Keyword.`then`, cons), alts) =>
      ctx.members.get(cls) match
        case S(sym: ClassSymbol) =>
          val scrutIdent = Ident("scrut"): Ident
          val scrutVar = VarSymbol(scrutIdent, nextUid)
          val scrutTerm = term(scrutinee)
          Term.If:
            Split.Let(scrutVar, scrutTerm, Branch(
              scrutVar.ref(scrutIdent),
              Pattern.Class(sym, N, true),
              Split.default(term(cons))
            ) :: Split.default(term(alts)))
        case _ =>
          raise(ErrorReport(msg"Illegal pattern $cls." -> tree.toLoc :: Nil))
          Term.Error
    case IfElse(InfixApp(cond, Keyword.`then`, cons), alts) =>
      val scrutIdent = Ident("scrut"): Ident
      val scrutVar = VarSymbol(scrutIdent, nextUid)
      val scrutTerm = term(cond)
      Term.If:
        Split.Let(scrutVar, scrutTerm, Branch(
          scrutVar.ref(scrutIdent),
          Split.default(term(cons))
        ) :: Split.default(term(alts)))
    case Tree.Quoted(body) => Term.Quoted(term(body))
    case Tree.Unquoted(body) => Term.Unquoted(term(body))
    case Tree.Case(Block(branches)) => branches.lastOption match
      case S(InfixApp(id: Ident, Keyword.`then`, dflt)) =>
        val sym = VarSymbol(id, nextUid)
        val nestCtx = ctx.copy(locals = ctx.locals ++ Ls(id.name -> sym))
        Term.Lam(
          Param(FldFlags.empty, sym, N) :: Nil,
          Term.If(branches.dropRight(1).foldRight(Split.default(term(dflt)(using nestCtx)))((e, res) => e match
            case InfixApp(target, Keyword.`then`, cons) =>
              val scrutIdent = Ident("scrut"): Ident
              val scrut = VarSymbol(scrutIdent, nextUid)
              val cond = term(App(Ident("=="), Tree.Tup(id :: target :: Nil)))(using nestCtx)
              Split.Let(scrut, cond, Branch(
                scrut.ref(scrutIdent),
                Pattern.LitPat(Tree.BoolLit(true)),
                Split.default(term(cons)(using nestCtx))
              ) :: res)
            case _ =>
              raise(ErrorReport(msg"Unsupported case branch." -> tree.toLoc :: Nil))
              Split.default(Term.Error)
          ))
        )
      case _ =>
        raise(ErrorReport(msg"Unsupported default case branch." -> tree.toLoc :: Nil))
        Term.Error
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
    case TermDef(k, sym, nme, rhs) =>
      raise(ErrorReport(msg"Illegal definition in term position." -> tree.toLoc :: Nil))
      Term.Error
    case TypeDef(k, symName, head, extension, body) =>
      raise(ErrorReport(msg"Illegal type declaration in term position." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def fld(tree: Tree): Ctxl[Fld] = tree match
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, term(lhs), S(term(rhs)))
    case _ => Fld(FldFlags.empty, term(tree), N)
  
  def unit: Term.Lit = Term.Lit(UnitLit(true))
  
  def block(sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) = trace[(Term.Blk, Ctx)](
    pre = s"Elab block ${sts.toString.take(20)}[...]", r => s"~> ${r._1}"
  ):
    val newMembers = mutable.Map.empty[Str, MemberSymbol[?]] // * Definitions with implementations
    val newSignatures = mutable.Map.empty[Str, MemberSymbol[?]] // * Definitions containing only signatures
    val newSignatureTrees = mutable.Map.empty[Str, Tree] // * Store trees of signatures, passing them to definition objects
    @tailrec def preprocessStatement(statement: Tree): Unit = statement match
      case td: TermDef =>
        log(s"Found TermDef ${td.name}")
        td.name match
          case R(id) =>
            lazy val s = TermSymbol(id)
            val members = if td.signature.isEmpty then newMembers else newSignatures
            members.get(id.name) match
              case S(sym) =>
                raise(ErrorReport(msg"Duplicate definition of ${id.name}" -> td.toLoc
                  :: msg"aready defined here" -> id.toLoc :: Nil))
              case N =>
                members += id.name -> s
                td.signature.foreach(newSignatureTrees += id.name -> _)
            td.symbolicName match
              case S(id @ Ident(nme)) =>
                members.get(nme) match
                  case S(sym) =>
                    raise(ErrorReport(msg"Duplicate definition of $nme" -> td.toLoc
                      :: msg"aready defined here" -> id.toLoc :: Nil))
                  case N =>
                    members += nme -> s
                    td.signature.foreach(newSignatureTrees += id.name -> _)
              case N =>
          case L(d) => raise(d)
      case td: TypeDef =>
        log(s"Found TypeDef ${td.name}")
        td.name match
          case R(id) =>
            lazy val s = ClassSymbol(id)
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
      case Modified(Keyword.`abstract`, body) =>
        // TODO: Handle abstract
        preprocessStatement(body)
      case tree =>
        log(s"Found something else $tree")
    sts.foreach(preprocessStatement)      
    newSignatures.foreach:
      case (name, sym) =>
        if !newMembers.contains(name) then
          newMembers += name -> sym
    given Ctx = c.copy(members = c.members ++ newMembers)
    @tailrec
    def go(sts: Ls[Tree], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] = sts match
      case Nil =>
        val res = unit
        (Term.Blk(acc.reverse, res), ctx)
      case Let(lhs, rhs, N) :: sts =>
        val (pat, syms, optTup) = letPattern(lhs)
        val rhsTerm = term(rhs)(using optTup match
          case S(tup) =>
            val ctx1 = ctx.copy(locals = ctx.locals ++ syms)
            val (_, ctx2) = params(tup)(using ctx1)
            ctx2
          case N => ctx)
        go(sts, LetBinding(pat, rhsTerm) :: acc)(using ctx.copy(locals = ctx.locals ++ syms))
      case (td @ TermDef(k, sym, nme, rhs)) :: sts =>
        td.name match
          case R(id) =>
            val s = newMembers(id.name).asInstanceOf[TermSymbol] // TODO improve
            // Add type parameters to context
            val (tps, newCtx1) = td.typeParams match
              case S(t) => typeParams(t)
              case N => (N, ctx)
            // Add parameters to context
            val (ps, newCtx) = td.params match
              case S(t) => params(t)(using newCtx1).mapFirst(some)
              case N => (N, newCtx1)
            val b = rhs.map(term(_)(using newCtx))
            val r = FlowSymbol(s"‹result of ${s}›", nextUid)
            val tdf = TermDefinition(k, s, ps, (td.signature orElse newSignatureTrees.get(id.name)).map(term), b, r)
            s.defn = S(tdf)
            go(sts, tdf :: acc)
          case L(d) => go(sts, acc) // error already raised in newMembers initialization
      case TypeDef(k, symName, head, extension, body) :: sts =>
        assert((k is Als) || (k is Cls) || (k is Mod), k)
        def processHead(head: Tree): Ctxl[(Ident, Ls[TyParam], Opt[Ls[Param]], Ctx)] = head match
          case TyApp(base, tparams) =>
            
            val (name, tas, as, newCtx) = processHead(base)
            // TODO reject duplicated tas, out of order as
            
            val tps =
              given Ctx = newCtx
              tparams.flatMap: targ =>
                val (id, vce) = targ match
                  case id: Ident =>
                    (id, N)
                  case Modified(Keyword.`in`, id: Ident) =>
                    (id, S(false))
                  case Modified(Keyword.`out`, id: Ident) =>
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
          // case _ => ???
        val (nme, tps, ps, newCtx) = processHead(head)
        log(s"Processing type definition $nme")
        log(s"newMembers: ${newMembers.keys}")
        val sym = newMembers(nme.name).asInstanceOf[ClassSymbol] // TODO improve
        val cd =
          given Ctx = newCtx
          val (bod, c) = body match
            case S(Tree.Block(sts)) => block(sts)
            case S(t) => block(t :: Nil)
            case N => (new Term.Blk(Nil, Term.Lit(UnitLit(true))), ctx)
          ClassDef(sym, tps, ps, ObjBody(bod))
        sym.defn = S(cd)
        go(sts, cd :: acc)
      case Modified(Keyword.`abstract`, body) :: sts =>
        // TODO: pass abstract to `go`
        go(body :: sts, acc)
      case (result: Tree) :: Nil =>
        val res = term(result)
        (Term.Blk(acc.reverse, res), ctx)
      case (st: Tree) :: sts =>
        val res = term(st) // TODO reject plain term statements? Currently, `(1, 2)` is allowed to elaborate (tho it should be rejected in type checking later)
        go(sts, res :: acc)
    sts match
      case (_: TermDef | _: TypeDef) :: _ => go(sts, Nil)
      // case s :: Nil => (term(s), ctx)
      case _ => go(sts, Nil)

  def param(t: Tree): Ctxl[Ls[Param]] = t match
    case id: Ident =>
      Param(FldFlags.empty, VarSymbol(id, nextUid), N) :: Nil
    case InfixApp(lhs: Ident, Keyword.`:`, rhs) =>
      Param(FldFlags.empty, VarSymbol(lhs, nextUid), S(term(rhs))) :: Nil
    case App(Ident(","), list) => params(list)._1
    case TermDef(Val, _, S(inner), _) => param(inner)
  
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

      
  
  /** Elaborate the left-hand side of `let` expressions. */
  def letPattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol], Opt[Tup])] =
    t match
    // If the top-level pattern is function declaration, the only bound variable
    // is the function name and the parameters are bound in the body.
    case App(id @ Ident(name), tup @ Tup(params)) =>
      val idSym = VarSymbol(id, nextUid)
      (Pattern.Var(idSym), (name -> idSym) :: Nil, S(tup))
    // Otherwise, we recursively elaborate the pattern. `App` is interpreted as
    // constructor patterns.
    case _ =>
      val boundVars = mutable.HashMap.empty[Str, VarSymbol]
      def go(t: Tree): Pattern = t match
        case id @ Ident(name) => Pattern.Var:
          if boundVars contains name then
            raise(ErrorReport(msg"Duplicate bindings: $name" -> id.toLoc :: Nil))
          boundVars.getOrElseUpdate(name, VarSymbol(id, nextUid))
        case Tup(fields) => Pattern.Tuple(fields.map(go))
        case _ => ???
      (go(t), boundVars.toList, N)
  
  def importFrom(sts: Ls[Tree])(using c: Ctx): Ctx =
    val (_, newCtx) = block(sts)
    // TODO handle name clashes
    newCtx
  
  
  def topLevel(sts: Ls[Tree])(using c: Ctx): (Term, Ctx) =
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

