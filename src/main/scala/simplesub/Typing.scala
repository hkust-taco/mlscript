package simplesub

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.util.chaining._
import Syntax._
import scala.annotation.tailrec

final case class TypeError(msg: String) extends Exception(msg)

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  In order to turn the resulting TypeShape into a Type or a Pos.Type, use `expandType` and `expandPosType`.
 */
class Typing {
  
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[PolymorphicType] = pgrm.defs match {
    case (isrec, nme, rhs) :: defs =>
      val ty_sch = typeLetRhs(isrec, nme, rhs)(ctx, 0)
      ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch))
    case Nil => Nil
  }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): TypeShape = {
    typeTerm(term)(ctx, lvl)
  }
  
  type Ctx = Map[String, TypeScheme]
  
  val BoolType: TypeCtor = TypeCtor("Bool")
  val IntType: TypeCtor = TypeCtor("Int")
  
  val builtins: Ctx = Map(
    "true" -> BoolType,
    "false" -> BoolType,
    "not" -> FunctionType(BoolType, BoolType),
    "succ" -> FunctionType(IntType, IntType),
    "add" -> FunctionType(IntType, FunctionType(IntType, IntType)),
    "if" -> {
      val v = freshVar(1)
      PolymorphicType(0, FunctionType(BoolType, FunctionType(v, FunctionType(v, v))))
    }
  )
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)(implicit ctx: Ctx, lvl: Int): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(lvl + 1)
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1)
      constrain(ty, e_ty)
      ty
    } else typeTerm(rhs)(ctx, lvl + 1)
    PolymorphicType(lvl, res)
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, lvl: Int): TypeShape = {
    lazy val res = freshVar
    term match {
      case Var(name) =>
        ctx.getOrElse(name, err("identifier not found: " + name)).instantiate
      case Lam(name, body) =>
        val param = freshVar
        val body_ty = typeTerm(body)(ctx + (name -> param), lvl)
        FunctionType(param, body_ty)
      case App(f, a) =>
        val f_ty = typeTerm(f)
        val a_ty = typeTerm(a)
        // ^ Note: Interesting things happen if we introduce an intermediate variable here,
        //    as in `val a_ty = freshVar; constrain(typeTerm(a), a_ty); ...`
        //    e.g., (fun x -> x x) becomes typed as `('a ∧ ('a -> 'b)) -> 'b` instead of `('a -> 'b) as 'a -> 'b`
        //    but thankfully I think these two types are equivalent.
        constrain(f_ty, FunctionType(a_ty, res))
        res
      case Lit(n) =>
        IntType
      case Sel(obj, name) =>
        val obj_ty = typeTerm(obj)
        constrain(obj_ty, RecordType((name, res) :: Nil))
        res
      case Rcd(fs) =>
        RecordType(fs.map { case (n, t) => (n, typeTerm(t)) })
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl)
    }
  }
  
  /** Constrains the types to enforce a subtyping relationship `lhs` <: `rhs`. */
  def constrain(lhs: TypeShape, rhs: TypeShape)
      // we need a cache to remember the subtyping tests in process; we also make the cache remember
      // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm)
      (implicit cache: MutSet[(TypeShape, TypeShape)] = MutSet.empty)
  : Unit = {
    if (lhs is rhs) return
    val lhs_rhs = lhs -> rhs
    lhs_rhs match {
      // There is no need to remember the subtyping tests performed that did not involve
      // type variables, as type variables will necessary be part of any possible cycles.
      // Since these types form regular trees, there will necessarily be a point where a
      // variable part of a cycle will be matched against the same type periodically.
      case (_: TypeVariable, _) | (_, _: TypeVariable) =>
      // case (_: TypeVariable, _: TypeVariable) =>
      //  ^ the tests pass with this version, but it feels wrong: I think it could loop indefinitely
      //    if the two variables never meet because their cycle lengths are in phase but shifted
        if (cache(lhs_rhs)) return
        cache += lhs_rhs
      case _ => ()
    }
    lhs_rhs match {
      case (FunctionType(l0, r0), FunctionType(l1, r1)) =>
        constrain(l1, l0)
        constrain(r0, r1)
      case (RecordType(fs0), RecordType(fs1)) =>
        fs1.foreach { case (n1, t1) =>
          fs0.find(_._1 === n1).fold(
            err(s"missing field: $n1 in ${lhs.show}")
          ) { case (n0, t0) => constrain(t0, t1) }
        }
      case (lhs: TypeVariable, rhs0) if rhs.level <= lhs.level =>
        lhs.upperBounds ::= rhs
        lhs.lowerBounds.foreach(constrain(_, rhs))
      case (lhs0, rhs: TypeVariable) if lhs.level <= rhs.level =>
        rhs.lowerBounds ::= lhs
        rhs.upperBounds.foreach(constrain(lhs, _))
      case (_: TypeVariable, rhs0) =>
        val rhs = extrude(rhs0, lhs.level)
        constrain(rhs, rhs0)
        constrain(lhs, rhs)
      case (lhs0, _: TypeVariable) =>
        val lhs = extrude(lhs0, rhs.level)
        constrain(lhs0, lhs)
        constrain(lhs, rhs)
      case _ => err(s"cannot constrain ${lhs.show} <: ${rhs.show}")
    }
  }
  
  /** Copies a type up to its type variables of wrong level. */
  def extrude(ty: TypeShape, lvl: Int): TypeShape = {
    if (ty.level <= lvl) ty else ty match {
      case FunctionType(l, r) => FunctionType(extrude(l, lvl), extrude(r, lvl))
      case RecordType(fs) => RecordType(fs.map(nt => nt._1 -> extrude(nt._2, lvl)))
      case tv: TypeVariable => freshVar(lvl)
      case TypeCtor(_) => ty
    }
  }
  
  def err(msg: String): Nothing = throw TypeError(msg)
  
  private var freshCount = 0
  def freshVar(implicit lvl: Int): TypeVariable = new TypeVariable(lvl, Nil, Nil)
  
  
  // The main data types for type inference
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int): TypeShape
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: TypeShape) extends TypeScheme {
    def instantiate(implicit lvl: Int) = body.freshenAbove(level)
  }
  /** A type without universally quantified type variables. */
  sealed abstract class TypeShape extends TypeScheme with TypeShapeImpl {
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  case class FunctionType(lhs: TypeShape, rhs: TypeShape) extends TypeShape {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  case class RecordType(fields: List[(String, TypeShape)]) extends TypeShape {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  case class TypeCtor(name: String) extends TypeShape {
    def level: Int = 0
    override def toString = name
  }
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level lower than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[TypeShape],
      var upperBounds: List[TypeShape],
  ) extends TypeShape {
    private val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asUniqueVariable = new TypeVar("α", uid)
    override def toString: String = "α" + uid + "'" * level
  }
  
  
  // Helper methods
  
  sealed trait TypeShapeImpl { self: TypeShape =>
    def freshenAbove(lim: Int)(implicit lvl: Int): TypeShape = {
      val freshened = MutMap.empty[TypeVariable, TypeVariable]
      def freshen(ty: TypeShape): TypeShape = ty match {
        case tv: TypeVariable =>
          if (tv.level > lim) freshened.get(tv) match {
            case Some(tv) => tv
            case None =>
              val v = freshVar
              freshened += tv -> v
              v.lowerBounds = tv.lowerBounds.mapConserve(freshen)
              v.upperBounds = tv.upperBounds.mapConserve(freshen)
              v
          } else tv
        case FunctionType(l, r) => FunctionType(freshen(l), freshen(r))
        case RecordType(fs) => RecordType(fs.map(ft => ft._1 -> freshen(ft._2)))
        case TypeCtor(_) => ty
      }
      freshen(this)
    }
    def children: List[TypeShape] = this match {
      case tv: TypeVariable => tv.lowerBounds ::: tv.upperBounds
      case FunctionType(l, r) => l :: r :: Nil
      case RecordType(fs) => fs.map(_._2)
      case TypeCtor(_) => Nil
    }
    def getVars: Set[TypeVariable] = {
      val res = MutSet.empty[TypeVariable]
      @tailrec def rec(queue: List[TypeShape]): Unit = queue match {
        case (tv: TypeVariable) :: tys =>
          if (res(tv)) rec(tys)
          else { res += tv; rec(tv.children ::: tys) }
        case ty :: tys => rec(ty.children ::: tys)
        case Nil => ()
      }
      rec(this :: Nil)
      res.toSet
    }
    def show: String = expandPosType(this, simplify = false).show
    def showBounds: String =
      getVars.iterator.filter(tv => (tv.upperBounds ++ tv.lowerBounds).nonEmpty).map(tv =>
        tv.toString
          + (if (tv.lowerBounds.isEmpty) "" else " :> " + tv.lowerBounds.mkString(" | "))
          + (if (tv.upperBounds.isEmpty) "" else " <: " + tv.upperBounds.mkString(" & "))
      ).mkString(", ")
  }
  
  
  // Conversion into proper immutable type representations
  
  def expandType(tv: TypeShape, simplify: Boolean): Type = {
    val polarities = MutMap.empty[TypeVar, Option[Boolean]]
    def go(ts: TypeShape, polarity: Boolean)(inProcess: Set[TypeVariable]): Type = ts match {
      case tv: TypeVariable =>
      val uv = tv.asUniqueVariable
        val newPol = Some(polarity)
        val oldPol = polarities.getOrElseUpdate(uv, newPol)
        if (oldPol =/= newPol) polarities(uv) = None
        if (inProcess(tv)) uv
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + tv))
          val isRecursive = boundTypes.exists(_.freeVars(uv))
          val v: Type = if (isRecursive) if (polarity) Bot else Top else uv
          val body = boundTypes.foldLeft(v)(if (polarity) Union else Inter)
          if (isRecursive) Recursive(uv, body) else body
        }
      case FunctionType(l, r) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case TypeCtor(n) => Ctor(n)
    }
    val ty = go(tv, true)(Set.empty)
    def doSimplify(ty: Type): Type = ty match {
      case uv: TypeVar => polarities.get(uv) match {
        case Some(Some(true)) => Bot
        case Some(Some(false)) => Top
        case _ => ty
      }
      case _ => ty.map(doSimplify)
    }
    if (simplify) doSimplify(ty) else ty
  }
  
  def expandPosType(tv: TypeShape, simplify: Boolean): Pos.Type = {
    val polarities = MutMap.empty[TypeVariable, Option[Polarity]]
    def go(ts: TypeShape, pol: Polarity)
          (implicit inProcess: Set[TypeVariable]): Set[TypeVariable] => pol.Type = {
      import pol.empty.{copy => mk}
      ts match {
        case tv: TypeVariable =>
          val newPol = Some(pol)
          val oldPol = polarities.getOrElseUpdate(tv, newPol)
          if (oldPol =/= newPol) polarities(tv) = None
          if (inProcess(tv)) _ => mk(atoms = Set(tv.asUniqueVariable))
          else {
            val bounds = if (pol === Pos) tv.lowerBounds else tv.upperBounds
            val boundsRec = bounds.map(go(_, pol)(inProcess + tv))
            ctx => {
              val boundsRes = boundsRec.map(_(ctx))
              val uv = tv.asUniqueVariable
              val isRecursive = boundsRes.exists(_.freeVariables(uv))
              boundsRes.foldLeft(
                if (isRecursive) mk(rec = Some(uv))
                else if (ctx(tv)) mk(atoms = Set(uv)) else mk()
              )(pol.merge(_, _))
            }
          }
        case FunctionType(l, r) =>
          val l2 = go(l, !pol)
          val r2 = go(r, pol)
          ctx => mk(fun = Some(l2(ctx) -> r2(ctx)))
        case RecordType(fs) =>
          val fs2 = fs.map(nt => nt._1 -> go(nt._2, pol))
          ctx => mk(fields = Some(fs2.iterator.map(nt => nt._1 -> nt._2(ctx)).toMap))
        case TypeCtor(n) => _ => mk(atoms = Set(Ctor(n)))
      }
    }
    go(tv, Pos)(Set.empty)(
      polarities.iterator.filter(!simplify || _._2.isEmpty).map(_._1).toSet)
  }
  
  
}
