package hkmc2
package semantics

import scala.collection.immutable.Queue

import mlscript.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import hkmc2.semantics.Elaborator.*
import hkmc2.semantics.Split.{Let, Else}
import hkmc2.semantics.Term.*
import hkmc2.syntax.Tree.{Ident, IntLit, StrLit, UnitLit}
import hkmc2.utils.TraceLogger

object Specialiser:
  transparent inline def ctx(using Ctx): Ctx = summon
  transparent inline def state(using Elaborator.State): Elaborator.State = summon
  private transparent inline def wq(using Queue[TermDefinition]): Queue[TermDefinition] = summon

  import hkmc2.semantics.Elaborator.Ctx.Elem

  extension (ctx: Ctx)
    def elem_+(local: Str -> Ctx.Elem): Ctx = ctx.copy(ctx.outer, env = ctx.env + local)
    def map(f: Str -> Ctx.Elem => Str -> Ctx.Elem): Ctx =
      ctx.copy(parent = ctx.parent.map(_.map(f)), env = ctx.env.map(f))
    def showDbg: Str = ctx.env.map((k, v) => s"$k -> ${v}").mkString(", ")

  final case class Binding(val sym: Symbol, val typ: Opt[Ref]) extends Elem:
    def nme: Str = sym.nme
    def symbol: Opt[Symbol] = S(sym)
    def ref(id: Ident)(using Elaborator.State): Term = ??? // TODO: Make own context; this is dumb

  final case class TD(val td: TermDefinition) extends Elem:
    def nme: Str = td.sym.nme
    def symbol: Opt[Symbol] = S(td.sym)
    def ref(id: Ident = Ident(""))(using Elaborator.State): Term = td.sym.ref()

  object Spec:
    val empty: Spec = Spec(Nil)
  final case class Spec(val tys: Ls[Symbol -> (Ref | SynthSel)])

  type Ctxl[T] = Ctx ?=> T
  type Apps = Map[Str, Ls[Spec]]

class Specialiser(val tl: TraceLogger)(using Raise, Elaborator.State):
  import tl.*
  import Specialiser.*

  private val tInt: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Int"), 0)
  private val tStr: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Str"), 0)
  private val tUnit: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Unit"), 0)

  def block(blk: Blk, apps: Apps): Ctxl[(Blk, Apps)] = trace(s"Specialising block ${blk.showDbg}"):
    @annotation.tailrec
    def go(sts: Ls[Statement], acc: Ls[Statement], apps: Apps): Ctxl[(Blk, Apps)] =
      log(s"Specialising ${sts.headOption.map(_.showDbg).getOrElse("block end. \n")}")
      sts match
        case (b: Blk) :: sts =>
          val (newBlk, lowerApps) = block(b, apps)(using ctx.nest(N))
          go(sts, newBlk :: acc, lowerApps)
        case (t: Term) :: sts =>
          val (newTerm, lowerApps) = term(t, apps)(using ctx.nest(N))
          go(sts, newTerm :: acc, lowerApps)

        case (l: LetDecl) :: sts =>
          ctx.get(l.sym.nme) match
            case S(_) => go(sts, l :: acc, apps)
            case N => go(sts, l :: acc, apps)(using ctx elem_+ l.sym.nme -> Binding(l.sym, N))
        case (d: DefineVar) :: sts =>
          val ntyp: Opt[Ref] = d.rhs match
            case Lit(lit) => lit.asTree match
              case _: IntLit => S(tInt)
              case _: StrLit => S(tStr)
              case _: UnitLit => S(tUnit)
              case _ => N
            case _ => N // TODO: Infer type from other bindings; tuple type inference
          ctx.map((k, v) => if k == d.sym.nme then k -> Binding(d.sym, ntyp) else k -> v).givenIn:
            go(sts, d :: acc, apps)
        case (td : TermDefinition) :: sts => go(sts, acc, apps)(using ctx elem_+ td.sym.nme -> TD(td))

        case (i: Import) :: sts => go(sts, i :: acc, apps)
        case (md @ ModuleDef(_, sym, _, _, _, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, md.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pd @ PatternDef(_, sym, _, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, pd.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (p @ ClassDef.Parameterized(_, _, sym, _, _, _, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, p.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pl @ ClassDef.Plain(_, _, sym, _, _, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, pl.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (t: TypeLikeDef) :: sts => go(sts, t :: acc, apps)

        case Nil =>
          log(s"Res: ${blk.res.showDbg}")
          val (newRes, lowerApps) = term(blk.res, apps)

          val tds = ctx.env.collect{case (_, v: TD) => v.td}.toList
          log(s"Ctx: ${ctx.showDbg}")
          log(s"Term definitions: ${tds}")
          log(s"Applications: ${lowerApps}")

          val wq = tds.map(td => td -> lowerApps.getOrElse(td.sym.nme, Nil)).foldLeft(Queue.empty[TermDefinition -> Ls[Spec]]):
            (acc, v) => acc.enqueue(v)
          log(s"Queue: ${wq}")

          val newStats = processQueue(wq)(using ctx, tds)

          (Blk(tds ::: newStats ::: acc.reverse, newRes), lowerApps)

    def processQueue(q: Queue[TermDefinition -> Ls[Spec]])(using ctx: Ctx, tds: Ls[TermDefinition]): Ls[Statement] = q match
      case q if q.isEmpty => Nil
      case q => 
        log(s"Processing queue: ${q}")
        val ((td, typs), nq) = q.dequeue
        log(s"Processing ${td.sym} with ${typs}")
        val (speccedDefs, nnq) = typs.foldLeft((Ls.empty[Statement], nq))((acc, app) =>
          val name = app.tys.map {
            case (_, s: SynthSel) => s.nme
            case (_, r: Ref) => r.tree.name
          }.mkString(td.sym.nme + "_", "_", "")
          val (nt, apps) = td.body match
            // FIXME
            case S(body) => term(body, Map.empty)(using ctx elem_++ app.tys.foldLeft(Ls.empty[Str -> Binding])((acc, v) => v._2 match
              case r: Ref => v._1.nme -> Binding(v._1, S(r)) :: acc
            )).mapFirst(S(_))
            case N => (N, Nil)
          log(s"Chain specialising ${td.sym} containing ${apps}")
          val newSpeccs = apps.foldLeft(Ls.empty[TermDefinition -> Ls[Spec]])((acc, v) => tds.find(_.sym.nme == v._1).map(_ -> v._2 :: acc).getOrElse(acc))
          (td.copy(sym = BlockMemberSymbol(name, td.sym.trees), body = nt) :: acc._1, nq.enqueueAll(newSpeccs)))
        speccedDefs ++ processQueue(nnq)


    go(blk.stats, Nil, apps)

  def term(t: Term, apps: Apps): Ctxl[(Term, Apps)] = trace(s"Specialising term ${t.showDbg}"):
    t match
      case app @ App(lhs, rhs) =>
        lhs match
          case s @ SynthSel(_, n) => 
            val name = n.name
            log(s"Ctx: ${ctx.showDbg}")
            val params = ctx.get(name).map { case td: TD => td.td.params }.getOrElse(Nil)
            val typ: Spec = rhs match
              case Tup(fields) => fields.zip(params.head.params).foldLeft(Spec(Nil)):
                (acc, fieldPair) => fieldPair._1 match
                case Fld(_, Lit(lit), _) => lit.asTree match
                  case _: IntLit => acc.copy(tys = (fieldPair._2.sym -> tInt) :: acc.tys)
                  case _: StrLit => acc.copy(tys = (fieldPair._2.sym -> tStr) :: acc.tys)
                  case _: UnitLit => acc.copy(tys = (fieldPair._2.sym -> tUnit) :: acc.tys)
                  case _ => acc
                case Fld(_, Ref(r), _) => acc.copy(tys = fieldPair._2.sym -> ctx.get(r.nme).flatMap(_.asInstanceOf[Binding].typ).get :: acc.tys) // FIXME
                case _ => acc
              case _ => Spec(Nil)

            // log(s"Found application of ${name} with types ${typ.showDbg}")
            val newApps = apps + (name -> (typ :: apps.getOrElse(name, Nil).filterNot(_ == typ)))

            val newName: Ident = Ident(name + typ.tys.map{ case (_, r: Ref) => r.tree.name }.mkString("_", "_", ""))
            val specApp: App = app.copy(lhs = s.copy(nme = newName)(s.sym))(app.tree, app.resSym)
            (specApp, newApps)
          // TODO: Fix these two
          case r: Ref => 
            val name = r.sym.nme
            val typ: Opt[Ref] = rhs match
              case Tup(fields) => fields.head match // FIXME: This can obviously be more than primitives
                case Fld(_, Lit(lit), _) => lit.asTree match
                  case _: IntLit => S(tInt)
                  case _: StrLit => S(tStr)
                  case _: UnitLit => S(tUnit)
                  case _ => N
                case Fld(_, Ref(r), _) => ctx.get(r.nme).flatMap(_.asInstanceOf[Binding].typ)
                case _ => N
              case _ => N

            log(s"Found application of ${name} with type ${typ.map(_.tree.name).getOrElse("error")}")
            val newApps = typ match
              case Some(t) => apps + (name -> (t :: apps.getOrElse(name, Nil).filterNot(_ == t)))
              case N => apps

            // val newName: Ident = Ident(name + "_" + typ.map(_.tree.name).getOrElse("oops"))
            // (specApp, newApps)
            (t, apps)
          case _: Sel => (t, apps)
          case _ =>
            raise(ErrorReport(msg"I messed up :(" -> t.toLoc :: Nil)) // FIXME
            (t, apps)
      case il @ IfLike(_, desug) => desug match
        case Let(s, b, t) =>
          val (nb, lowerApps) = term(b, apps)
          (il.copy(desugared = Let(s, nb, t))(il.normalized), lowerApps)
        case Else(d) =>
          val (nd, lowerApps) = term(d, apps)
          (il.copy(desugared = Else(nd))(il.normalized), lowerApps)
        case _ => (il, apps)
      case Lam(params, body) => // TODO: specialise the lambda
        val (newBody, newApps) = term(body, apps)
        (Lam(params, newBody), newApps)
      case Forall(tvs, outer, body) => // FIXME
        val (newTerm, newApps) = term(body, apps)
        (Forall(tvs, outer, newTerm), newApps)
      case Quoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Quoted(newTerm), newApps)
      case Unquoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Unquoted(newTerm), newApps)
      case Region(name, body) =>
        val (newTerm, newApps) = term(body, apps)
        (Region(name, newTerm), newApps)
      case Deref(ref) =>
        val (newTerm, newApps) = term(ref, apps)
        (Deref(newTerm), newApps)
      case Ret(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Ret(newTerm), newApps)
      case Throw(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Throw(newTerm), newApps)
      case Try(body, finallyDo) =>
        val (b1, apps1) = term(body, apps)
        val (b2, apps2) = term(finallyDo, apps1)
        (Try(b1, b2), apps2)
      case b: Blk => block(b, apps)
      case _ => (t, apps) // TODO: Handle the few other term types

  def topLevel(b: Blk): Blk = b
    // block(b, Map.empty)(using Ctx.empty)._1
    //

enum SimpleType:
  case Primitive(name: Str)
  case Binding(sym: Symbol, st: VariableState)
  case Function(lhs: SimpleType, rhs: SimpleType)
  case Object(fields: Ls[Str -> SimpleType])

class VariableState(var lb: SimpleType, var ub: SimpleType)

class SimpleSub(val tl: TraceLogger)(using Raise):
  def id = 0


