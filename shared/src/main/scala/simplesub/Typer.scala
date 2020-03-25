package simplesub

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec

final case class TypeError(msg: String) extends Exception(msg)

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a simplesub.Type, we use `expandCompactType`.
 */
class Typer(protected val dbg: Boolean) extends TyperHelpers {
  
  // Shadow Predef functions with debugging-flag-enabled ones:
  def println(msg: => Any): Unit = if (dbg) scala.Predef.println(msg)
  def assert(assertion: => Boolean): Unit = if (dbg) scala.Predef.assert(assertion)
  
  
  // The main type inference functions:
  
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0)) catch {
          case err: TypeError => Left(err)
        }
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(0))))
      case Nil => Nil
    }
  // ^ Saldy, the version above does not work in JavaScript as it raises a
  //      "RangeError: Maximum call stack size exceeded"
  
  // So we have to go with this ugly one:
  def inferTypesUgly(
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
      val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(curCtx, 0)) catch {
        case err: TypeError =>
          if (stopAtFirstError) defs = Nil
          Left(err)
      }
      res += ty_sch
      curCtx += (nme -> ty_sch.getOrElse(freshVar(0)))
    }
    res.toList
  }
  
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): SimpleType = {
    typeTerm(term)(ctx, lvl)
  }
  
  type Ctx = Map[String, TypeScheme]
  
  val BoolType: PrimType = PrimType("bool")
  val IntType: PrimType = PrimType("int")
  
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
  def typeTerm(term: Term)(implicit ctx: Ctx, lvl: Int): SimpleType = {
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
  def constrain(lhs: SimpleType, rhs: SimpleType)
      // we need a cache to remember the subtyping tests in process; we also make the cache remember
      // past subtyping tests for performance reasons (it reduces the complexity of the algoritghm)
      (implicit cache: MutSet[(SimpleType, SimpleType)] = MutSet.empty)
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
      case (lhs: TypeVariable, rhs) if rhs.level <= lhs.level =>
        lhs.upperBounds ::= rhs
        lhs.lowerBounds.foreach(constrain(_, rhs))
      case (lhs, rhs: TypeVariable) if lhs.level <= rhs.level =>
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
  def extrude(ty: SimpleType, lvl: Int): SimpleType = {
    if (ty.level <= lvl) ty else ty match {
      case FunctionType(l, r) => FunctionType(extrude(l, lvl), extrude(r, lvl))
      case RecordType(fs) => RecordType(fs.map(nt => nt._1 -> extrude(nt._2, lvl)))
      case tv: TypeVariable => freshVar(lvl)
      case PrimType(_) => ty
    }
  }
  
  def err(msg: String): Nothing = throw TypeError(msg)
  
  private var freshCount = 0
  def freshVar(implicit lvl: Int): TypeVariable = new TypeVariable(lvl, Nil, Nil)
  
  
  // The main data types for type inference:
  
  /** A type that potentially contains universally quantified type variables,
   *  and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme {
    def instantiate(implicit lvl: Int): SimpleType
  }
  /** A type with universally quantified type variables
   *  (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    def instantiate(implicit lvl: Int) = body.freshenAbove(level)
  }
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    def level: Int
    def instantiate(implicit lvl: Int) = this
  }
  case class FunctionType(lhs: SimpleType, rhs: SimpleType) extends SimpleType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"($lhs -> $rhs)"
  }
  case class RecordType(fields: List[(String, SimpleType)]) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  case class PrimType(name: String) extends SimpleType {
    def level: Int = 0
    override def toString = name
  }
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
   *  Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
  ) extends SimpleType with CompactTypeOrVariable {
    private[simplesub] val uid: Int = { freshCount += 1; freshCount - 1 }
    private[simplesub] var recursiveFlag = false // used temporarily by `compactType`
    lazy val asTypeVar = new TypeVar("α", uid)
    override def toString: String = "α" + uid + "'" * level
    override def hashCode: Int = uid
  }
  
  
  // Compact types representation, useful for simplification:
  
  sealed trait CompactTypeOrVariable
  
  /** Depending on whether it occurs in positive or negative position,
   * this represents either a union or an intersection, respectively,
   * of different type components.  */
  case class CompactType(
    vars: Set[TypeVariable],
    prims: Set[PrimType],
    rec: Option[SortedMap[String, CompactType]],
    fun: Option[(CompactType, CompactType)])
  extends CompactTypeOrVariable {
    override def toString = (
      vars.toList
      ::: prims.toList
      ::: rec.map(_.map(fs => fs._1 + ": " + fs._2).mkString("{",", ","}")).toList
      ::: fun.map(lr => lr._1.toString + " -> " + lr._2).toList
    ).mkString("‹", ", ", "›")
  }
  object CompactType {
    val empty: CompactType = CompactType(Set.empty, Set.empty, None, None)
    def merge(pol: Boolean)(lhs: CompactType, rhs: CompactType): CompactType = {
      val rec = mergeOptions(lhs.rec, rhs.rec) { (lhs, rhs) =>
        if (pol) lhs.flatMap { case (k, v) => rhs.get(k).map(k -> merge(pol)(v, _)) }
        else mergeSortedMap(lhs, rhs)(merge(pol)) }
      val fun = mergeOptions(lhs.fun, rhs.fun){
        case ((l0,r0), (l1,r1)) => (merge(!pol)(l0, l1), merge(pol)(r0, r1)) }
      CompactType(lhs.vars ++ rhs.vars, lhs.prims ++ rhs.prims, rec, fun)
    }
  }
  
  case class CompactTypeScheme(term: CompactType, recVars: Map[TypeVariable, CompactType])
  
  
}
