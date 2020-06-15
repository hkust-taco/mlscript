package funtypes

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import funtypes.utils._, shorthands._
import funtypes.Message._

final case class Origin(fileName: Str, startLineNum: Int, fph: FastParseHelpers) {
  override def toString = s"$fileName:+$startLineNum"
}
final case class Loc(spanStart: Int, spanEnd: Int, origin: Origin) {
  assert(spanStart >= 0)
  assert(spanEnd >= spanStart)
  def isWithin(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanEnd <= this.spanEnd
  )
  def touches(that: Loc): Bool = that.origin === this.origin && (
    that.spanStart >= this.spanStart && that.spanStart <= this.spanEnd
    || that.spanEnd <= this.spanEnd && that.spanEnd >= this.spanStart
  )
}
sealed abstract class Diagnostic(theMsg: String) extends Exception(theMsg) {
  val allMsgs: Ls[Message -> Opt[Loc]]
}
final case class TypeError(mainMsg: Str, allMsgs: Ls[Message -> Opt[Loc]]) extends Diagnostic(mainMsg)
object TypeError {
  def apply(msgs: Ls[Message -> Opt[Loc]]): TypeError =
    TypeError(msgs.head._1.show.plainText, msgs)
}
final case class Warning(msg: Message, loco: Opt[Loc]) extends Diagnostic(msg.show.plainText) {
  val allMsgs: Ls[Message -> Opt[Loc]] = (msg, loco) :: Nil
}

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a funtypes.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var explainErrors: Boolean) extends TyperDebugging with TypeSimplifier {
  
  type Ctx = Map[String, TypeScheme]
  type Raise = Diagnostic => Unit
  
  val primProv: TypeProvenance = TypeProvenance(N, "expression")
  
  val UnitType: PrimType = PrimType(Var("unit"), primProv)
  val BoolType: PrimType = PrimType(Var("bool"), primProv)
  val IntType: PrimType = PrimType(Var("int"), primProv)
  val DecType: PrimType = PrimType(Var("number"), primProv)
  val StrType: PrimType = PrimType(Var("string"), primProv)
  
  val builtins: Ctx = {
    val tv = freshVar(primProv)(1) // Q: level?
    import FunctionType.{ apply => fun }
    Map(
      "true" -> BoolType,
      "false" -> BoolType,
      "not" -> fun(BoolType, BoolType, primProv),
      "succ" -> fun(IntType, IntType, primProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType, primProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType, primProv)),
      "add" -> fun(IntType, fun(IntType, IntType, primProv), primProv),
      "+" -> fun(IntType, fun(IntType, IntType, primProv), primProv),
      "<" -> fun(IntType, fun(IntType, BoolType, primProv), primProv),
      "id" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(v, v, primProv))
      },
      "if" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v, primProv), primProv), primProv))
      },
    )
  }
  
  /** The main type inference function */
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0, throw _)) catch {
          case err: TypeError => Left(err) }
        val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(errProv)(0))))
      case Nil => Nil
    }
  
  // Saldy, the version above does not work in JavaScript as it raises a
  //    "RangeError: Maximum call stack size exceeded"
  // So we have to go with this uglier one:
  def inferTypesJS(
    pgrm: Pgrm,
    ctx: Ctx = builtins,
    stopAtFirstError: Boolean = true,
  ): List[Either[TypeError, PolymorphicType]] = {
    var defs = pgrm.defs
    var curCtx = ctx
    var res = collection.mutable.ListBuffer.empty[Either[TypeError, PolymorphicType]]
    while (defs.nonEmpty) {
      val (isrec, nme, rhs) = defs.head
      defs = defs.tail
      val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(curCtx, 0, throw _)) catch {
        case err: TypeError =>
          if (stopAtFirstError) defs = Nil
          Left(err)
      }
      res += ty_sch
      val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
      curCtx += (nme -> ty_sch.getOrElse(freshVar(errProv)(0)))
    }
    res.toList
  }
  
  def typeBlk(blk: Blk, ctx: Ctx = builtins, allowPure: Bool = false)
        : List[List[Diagnostic] -> PolymorphicType]
        = blk.stmts match {
    case s :: stmts =>
      val diags = mutable.ListBuffer.empty[Diagnostic]
      val (newCtx, ty) = typeStatement(s, allowPure)(ctx, 0, diags += _)
      diags.toList -> ty :: typeBlk(Blk(stmts), newCtx, allowPure)
    case Nil => Nil
  }
  def typeStatement(s: Statement, allowPure: Bool = false)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): Ctx -> PolymorphicType = s match {
    case LetS(isrec, Var(nme), rhs) =>
      val ty_sch = typeLetRhs(isrec, nme, rhs)
      (ctx + (nme -> ty_sch)) -> ty_sch
    case LetS(isrec, pat, rhs) => lastWords("Not yet supported: pattern " + pat)
    case t @ Tup(fs) if !allowPure => // Note: not sure this is still used!
      val thing = fs match {
        case (S(_), _) :: Nil => "field"
        case Nil => "empty tuple"
        case _ => "tuple"
      }
      warn(s"Useless $thing in statement position.", t.toLoc)
      ctx -> PolymorphicType(0, typeTerm(t))
    case t: Term =>
      val ty = typeTerm(t)
      if (!allowPure) {
        if (t.isInstanceOf[Var] || t.isInstanceOf[Lit])
          warn("Pure expression does nothing in statement position.", t.toLoc)
        else
          constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")),
            UnitType)(raise = raise, prov = TypeProvenance(t.toLoc, t.describe)) // TODO add explanation message
      }
      ctx -> PolymorphicType(0, ty)
  }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): SimpleType =
    typeTerm(term)(ctx, lvl, throw _)
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1, raise)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe))
      e_ty
    } else typeTerm(rhs)(ctx, lvl + 1, raise)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProxyType(ty)(prov)
    // TODO switch to return this in perf mode:
    // ty
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): SimpleType
        = trace(s"$lvl. Typing $term") {
    import TypeProvenance.{apply => tp}
    implicit val prov: TypeProvenance = TypeProvenance(term.toLoc, term.describe)
    term match {
      case Var(name) =>
        val ty = ctx.getOrElse(name, {
          // TODO: delay type expansion to message display and show the expected type here!
          err("identifier not found: " + name, term.toLoc)
          freshVar(tp(term.toLoc, "unknown variable"))
        }).instantiate
        mkProxy(ty, tp(term.toLoc, term.describe))
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case Lam(v @ Var(name), body) =>
        val param = freshVar(tp(v.toLoc, "parameter"))
        val body_ty = typeTerm(body)(ctx + (name -> param), lvl, raise)
        FunctionType(param, body_ty, tp(term.toLoc, "function"))
      case Lam(lhs, rhs) => ???
      case App(f, a) =>
        val f_ty = typeTerm(f)
        val a_ty = typeTerm(a)
        val res = freshVar(prov)
        val arg_ty = mkProxy(a_ty, tp(a.toCoveringLoc, "argument"))
        val fun_ty = mkProxy(f_ty, tp(f.toCoveringLoc, "applied expression"))
        constrain(fun_ty, FunctionType(arg_ty, res, prov))
        res
      case lit: Lit => PrimType(lit, tp(term.toLoc, "constant literal"))
      case Sel(obj, name) =>
        val o_ty = typeTerm(obj)
        val res = freshVar(prov)
        val obj_ty_ = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
        constrain(obj_ty_, RecordType((name, res) :: Nil, prov))
        res
      case Rcd(fs) => // TODO rm: no longer used?
        RecordType(fs.map { case (n, t) => (n, typeTerm(t)) }, tp(term.toLoc, "record literal"))
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl, raise)
      case tup: Tup =>
        typeTerms(tup :: Nil, false, Nil)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case Blk(stmts) => typeTerms(stmts, false, Nil)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Str] -> SimpleType])
        (implicit ctx: Ctx, lvl: Int, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(nme) -> trm :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, trm) :: ofs) :: sts =>
      val ty = if (ofs.isEmpty) typeTerm(Bra(rcd, trm)) else typeTerm(trm)
      val newCtx = no.fold(ctx)(n => ctx + (n -> ty))
      typeTerms(Tup(ofs) :: sts, rcd, (no, ty) :: fields)(newCtx, lvl, raise, prov)
    case (trm: Term) :: Nil =>
      if (fields.nonEmpty)
        warn("Previous field definitions are discarded by this returned expression.", trm.toLoc)
      typeTerm(trm)
    // case (trm: Term) :: Nil =>
    //   assert(!rcd)
    //   val ty = typeTerm(trm)
    //   typeBra(Nil, rcd, (N, ty) :: fields)
    case s :: sts =>
      val (newCtx, ty) = typeStatement(s)
      typeTerms(sts, rcd, fields)(newCtx, lvl, raise, prov)
    case Nil =>
      // TODO actually use a tuple type if !rcd
      val fs = fields.reverseIterator.zipWithIndex.map {
        case ((N, t), i) => ("_" + (i + 1), t); case ((S(n), t), _) => (n, t)
      }.toList
      RecordType(fs, prov)
  }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: SimpleType, rhs: SimpleType)(implicit raise: Raise, prov: TypeProvenance): Unit = {
    // We need a cache to remember the subtyping tests in process; we also make the cache remember
    // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm):
    val cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty
    
    def rec(lhs: SimpleType, rhs: SimpleType)(implicit ctx: Ls[SimpleType -> SimpleType]): Unit = trace(s"C $lhs <! $rhs") {
      println(s"  where ${FunctionType(lhs, rhs, primProv).showBounds}")
      (lhs -> rhs :: ctx) |> { implicit ctx =>
        if (lhs is rhs) return
        val lhs_rhs = lhs -> rhs
        lhs_rhs match {
          // There is no need to remember the subtyping tests performed that did not involve
          // type variables, as type variables will necessary be part of any possible cycles.
          // Since these types form regular trees, there will necessarily be a point where a
          // variable part of a cycle will be matched against the same type periodically.
          case (_: TypeVariable, _) | (_, _: TypeVariable) =>
            if (cache(lhs_rhs)) return
            cache += lhs_rhs
          case _ => ()
        }
        lhs_rhs match {
          case (FunctionType(l0, r0, p0), FunctionType(l1, r1, p1)) =>
            rec(l1, l0)(Nil)
            // ^ disregard error context: we to keep them from reversing polarity (or the messages are confusing)
            rec(r0, r1)
          case (prim: PrimType, _) if rhs === prim.widen => ()
          case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
            lhs.upperBounds ::= ProxyType(rhs)(prov)
            lhs.lowerBounds.foreach(rec(_, rhs))
          case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
            rhs.lowerBounds ::= ProxyType(lhs)(prov)
            rhs.upperBounds.foreach(rec(lhs, _))
          case (_: TypeVariable, rhs0) =>
            val rhs = extrude(rhs0, lhs.level, false)
            println(s"EXTR RHS  $rhs0  ~>  $rhs  to ${lhs.level}")
            println(s" where ${rhs.showBounds}")
            println(s"   and ${rhs0.showBounds}")
            rec(lhs, rhs)
          case (lhs0, _: TypeVariable) =>
            val lhs = extrude(lhs0, rhs.level, true)
            println(s"EXTR LHS  $lhs0  ~>  $lhs  to ${rhs.level}")
            println(s" where ${lhs.showBounds}")
            println(s"   and ${lhs0.showBounds}")
            rec(lhs, rhs)
          case (ProxyType(und), _) => rec(und, rhs)
          case (_, ProxyType(und)) => rec(lhs, und)
          case _ =>
            def doesntMatch(ty: SimpleType) = msg"does not match type `${ty.expNeg}`"
            def doesntHaveField(n: Str) = msg"does not have field '$n'"
            val failureOpt = lhs_rhs match {
              case (RecordType(fs0, p0), RecordType(fs1, p1)) =>
                var fieldErr: Opt[Message] = N
                fs1.foreach { case (n1, t1) =>
                  fs0.find(_._1 === n1).fold {
                    if (fieldErr.isEmpty) fieldErr = S(doesntHaveField(n1))
                  } { case (n0, t0) => rec(t0, t1) }
                }
                fieldErr
              case (_, FunctionType(_, _, _)) => S(msg"is not a function")
              case (_, RecordType((n, _) :: Nil, _)) => S(doesntHaveField(n))
              case _ => S(doesntMatch(lhs_rhs._2))
            }
            failureOpt.foreach { failure =>
              println(s"CONSTRAINT FAILURE: $lhs <: $rhs")
              val detailedContext = if (explainErrors)
                  msg"[info] Additional Explanations below:" -> N ::
                  ctx.tail.reverseIterator.flatMap { case (l, r) =>
                    msg"[info] While constraining ${l.prov.desc} of type ${l.expPos}" -> l.prov.loco ::
                    msg"[info] to be a subtype of ${r.prov.desc} type ${r.expNeg}" -> r.prov.loco ::
                    Nil
                  }.toList
                else Nil
              
              var betterLhsProv = lhs.prov.optionIf(_.loco.isDefined)
              ctx.tail.foreach { case (l, r) =>
                if (betterLhsProv.isEmpty && l.prov.loco.isDefined && (l.unwrapProxies === lhs || r.unwrapProxies === rhs))
                  betterLhsProv = S(l.prov)
              }
              val lhsProv = betterLhsProv.getOrElse(lhs.prov)
              assert(lhsProv.loco.isDefined) // TODO use soft assert
              
              lazy val tighestRelevantFailure = ctx.dropWhile(_._1 === lhs).collectFirst {
                case (l, r) if l.prov.loco.exists(ll => prov.loco/* .exists */.forall(ll touches _)) => (l, r)
              }
              
              // TODO use or rm:
              // val tighestLocatedLHS = ctx.dropWhile(_._1 === lhs).collectFirst {
              //   case (l, r) if l.prov.loco.isDefined => (l, r)
              // }
              
              val tighestLocatedRHS = // TODO try to re-enable this one:
              //   ctx.dropWhile(_._2.prov.loco.forall(rl => rhs.prov.loco.exists(_.touches(rl)))).collectFirst {
              //     case lr @ (l, r) if r.prov.loco.isDefined => lr }
                ctx.dropWhile(_._2.prov.loco.forall(rl => prov.loco.exists(_.touches(rl)))).collectFirst {
                  case lr @ (l, r) if r.prov.loco.isDefined => lr }
              
              val msgs: Ls[Message -> Opt[Loc]] = List(
                msg"Type mismatch in ${prov.desc}:" -> prov.loco :: Nil,
                msg"expression of type `${lhs.expPos}` $failure" -> lhsProv.loco :: Nil,
                tighestRelevantFailure.collect { case (l, r) if l.prov.loco.exists(ll => lhsProv.loco.forall(_ =/= ll)) =>
                  val fail = (l, r) match {
                    case (RecordType(fs0, p0), RecordType(fs1, p1)) =>
                      (fs0.map(_._1).toSet -- fs1.map(_._1).toSet).headOption.fold(msg"does not match type `${r.expNeg}`") { n1 =>
                        doesntHaveField(n1)
                      }
                    case (fun, FunctionType(_, _, _))
                      if !fun.unwrapProxies.isInstanceOf[FunctionType] => msg"is not a function"
                    case (rec, RecordType((n, _) :: Nil, _))
                      if !rec.unwrapProxies.isInstanceOf[RecordType] => doesntHaveField(n)
                    case _ => doesntMatch(r)
                  }
                  msg"but it flows into ${l.prov.desc}${
                      if (l.unwrapProxies === lhs.unwrapProxies) msg"" else msg" of type `${l.expPos}`"
                    }" -> l.prov.loco ::
                  msg"which $fail" -> N ::
                  Nil
                }.toList.flatten,
                tighestLocatedRHS.collect { case (l, r) =>
                  // Note: in principle, we could track the error recursively, arbitrarily deeply,
                  // which could be useful — indeed, this hint will typically only show the function application
                  // where the type variable registered its problematic constraint, but it does not show how
                  // that constraint came to be registered!
                  msg"Note: constraint arises from ${r.prov.desc}:" -> r.prov.loco :: Nil
                }.toList.flatten,
                detailedContext,
              ).flatten
              raise(TypeError(msgs))
            }
        }
      }
    }()
    rec(lhs, rhs)(Nil)
  }
  
  /** Copies a type up to its type variables of wrong level (and their extruded bounds). */
  def extrude(ty: SimpleType, lvl: Int, pol: Boolean)
      (implicit cache: MutMap[TypeVariable, TypeVariable] = MutMap.empty): SimpleType =
    if (ty.level <= lvl) ty else ty match {
      case FunctionType(l, r, p) => FunctionType(extrude(l, lvl, !pol), extrude(r, lvl, pol), p)
      case RecordType(fs, p) => RecordType(fs.map(nt => nt._1 -> extrude(nt._2, lvl, pol)), p)
      case tv: TypeVariable => cache.getOrElse(tv, {
        val nv = freshVar(tv.prov)(lvl)
        cache += (tv -> nv)
        if (pol) { tv.upperBounds ::= nv
          nv.lowerBounds = tv.lowerBounds.map(extrude(_, lvl, pol)) }
        else { tv.lowerBounds ::= nv
          nv.upperBounds = tv.upperBounds.map(extrude(_, lvl, pol)) }
        nv
      })
      case p @ ProxyType(und) => ProxyType(extrude(und, lvl, pol))(p.prov)
      case PrimType(_, _) => ty
    }
  
  def err(msg: Message, loco: Opt[Loc])(implicit raise: Raise): Unit =
    raise(TypeError((msg, loco) :: Nil))
  
  def warn(msg: String, loco: Opt[Loc])(implicit raise: Raise): Unit =
    raise(Warning(msg, loco))
  
  private var freshCount = 0
  def freshVar(p: TypeProvenance)(implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, Nil, Nil)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  
  def freshenAbove(lim: Int, ty: SimpleType)(implicit lvl: Int): SimpleType = {
    val freshened = MutMap.empty[TypeVariable, TypeVariable]
    def freshen(ty: SimpleType): SimpleType = ty match {
      case tv: TypeVariable =>
        if (tv.level > lim) freshened.get(tv) match {
          case Some(tv) => tv
          case None =>
            val v = freshVar(tv.prov)
            freshened += tv -> v
            // v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
            // v.upperBounds = tv.upperBounds.mapConserve(freshen)
            //  ^ the above are more efficient, but they lead to a different order
            //    of fresh variable creations, which leads to some types not being
            //    simplified the same when put into the RHS of a let binding...
            v.lowerBounds = tv.lowerBounds.reverse.map(freshen).reverse
            v.upperBounds = tv.upperBounds.reverse.map(freshen).reverse
            v
        } else tv
      case FunctionType(l, r, p) => FunctionType(freshen(l), freshen(r), p)
      case RecordType(fs, p) => RecordType(fs.map(ft => ft._1 -> freshen(ft._2)), p)
      case p @ ProxyType(und) => ProxyType(freshen(und))(p.prov)
      case PrimType(_, _) => ty
    }
    freshen(ty)
  }
  
  
  // The data types used for type inference:
  
  case class TypeProvenance(loco: Opt[Loc], desc: Str)
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int): SimpleType
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    val prov: TypeProvenance = body.prov
    def instantiate(implicit lvl: Int) = freshenAbove(level, body)
  }
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  case class FunctionType(lhs: SimpleType, rhs: SimpleType, prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  case class RecordType(fields: List[(String, SimpleType)], prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  /** The sole purpose of ProxyType is to store additional type provenance info. */
  case class ProxyType(underlying: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = underlying.level
    override def toString = s"[$underlying]"
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  case class PrimType(id: SimpleTerm, prov: TypeProvenance) extends SimpleType {
    def widen: PrimType = id match {
      case _: IntLit => IntType
      case _: StrLit => StrType
      case _: DecLit => DecType
      case _ => this
    }
    def level: Int = 0
    override def toString = id.idStr
  }
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable {
    private[funtypes] val uid: Int = { freshCount += 1; freshCount - 1 }
    private[funtypes] var recursiveFlag = false // used temporarily by `compactType`
    lazy val asTypeVar = new TypeVar("α", uid)
    override def toString: String = "α" + uid + "'" * level
    override def hashCode: Int = uid
  }
  
  trait CompactTypeOrVariable
  
  
  type PolarVariable = (TypeVariable, Boolean)
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool = true): Type = {
    val recursive = mutable.Map.empty[PolarVariable, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(inProcess: Set[PolarVariable]): Type = st match {
      case tv: TypeVariable =>
        val tv_pol = tv -> polarity
        if (inProcess.contains(tv_pol))
          recursive.getOrElseUpdate(tv_pol, freshVar(tv.prov)(0).asTypeVar)
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + tv_pol))
          val mrg = if (polarity) Union else Inter
          val res = boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
          recursive.get(tv_pol).fold(res)(Recursive(_, res))
        }
      case FunctionType(l, r, _) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs, _) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case ProxyType(und) => go(und, polarity)(inProcess)
      case PrimType(n, _) => Primitive(n.idStr)
    }
    go(st, polarity)(Set.empty)
  }
  
  
}
