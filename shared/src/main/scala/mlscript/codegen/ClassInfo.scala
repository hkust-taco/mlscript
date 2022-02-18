package mlscript.codegen

import mlscript.utils._, shorthands._
import scala.collection.immutable.{Map, Set, HashSet}
import mlscript.{ TypeVar, SourceCode, Type, Union, TypeName, Inter, Record, Tuple,
  Top, Bot, Literal, Function, Recursive, AppliedType, Neg, Rem, Bounds, WithExtension,
  IntLit, DecLit, StrLit, Arr, Cls, Trt, Als }
import mlscript.{JSBackend, JSLit}
import mlscript.ShowCtx
import mlscript.Typer
import mlscript.TypeDef
import mlscript.Terms

final case class TypingUnitError(message: String) extends Exception(message)

/** Helper methods for finding type information for a particular typing unit.
  * The typing unit can be a block of statements or an entire file or others as
  * implemented.
  *
  * It is initialized with mappings for the type definitions in a typing unit.
  */
final case class ClassInfo(
    typeAliasMap: Map[String, List[String] -> Type],
    traitNames: Set[String],
    classNames: Set[String]
) {
  // This function collects two things:
  // 1. fields from a series of intersection of records,
  // 2. name of the base class.
  // Only one base class is allowed.
  def getBaseClassAndFields(ty: Type): (Ls[Str], Opt[Str]) = ty match {
    // `class A` ==> `class A {}`
    case Top => Nil -> N
    // `class A { <items> }` ==>
    // `class A { constructor(fields) { <items> } }`
    case Record(fields) => fields.map(_._1.name) -> N
    // `class B: A` ==> `class B extends A {}`
    // If `A` is a type alias, it is replaced by its real type.
    // Otherwise just use the name.
    case TypeName(name) =>
      if (traitNames contains name)
        Nil -> N
      else
        typeAliasMap get name match {
          // The base class is not a type alias.
          case N => Nil -> S(name)
          // The base class is a type alias with no parameters.
          // Good, just make sure all term is normalized.
          case S(Nil -> body) => getBaseClassAndFields(substitute(body))
          // The base class is a type alias with parameters.
          // Oops, we don't support this.
          case S(tparams -> _) =>
            throw TypingUnitError(
              s"type $name expects ${tparams.length} type parameters but nothing provided"
            )
        }
    // `class C: { <items> } & A` ==>
    // `class C extends A { constructor(fields) { <items> } }`
    case Inter(Record(entries), ty) =>
      val (fields, cls) = getBaseClassAndFields(ty)
      entries.map(_._1.name) ++ fields -> cls
    // `class C: { <items> } & A` ==>
    // `class C extends A { constructor(fields) { <items> } }`
    case Inter(ty, Record(entries)) =>
      val (fields, cls) = getBaseClassAndFields(ty)
      fields ++ entries.map(_._1.name) -> cls
    // `class C: <X> & <Y>`: resolve X and Y respectively.
    case Inter(ty1, ty2) =>
      val (fields1, cls1) = getBaseClassAndFields(ty1)
      val (fields2, cls2) = getBaseClassAndFields(ty2)
      (cls1, cls2) match {
        case (N, N) =>
          fields1 ++ fields2 -> N
        case (N, S(cls)) =>
          fields1 ++ fields2 -> S(cls)
        case (S(cls), N) =>
          fields1 ++ fields2 -> S(cls)
        case (S(cls1), S(cls2)) =>
          if (cls1 === cls2) {
            fields1 ++ fields2 -> S(cls1)
          } else {
            throw TypingUnitError(s"Cannot have two base classes: $cls1, $cls2")
          }
      }
    // `class C: F[X]` and (`F[X]` => `A`) ==> `class C extends A {}`
    // For applied types such as `Id[T]`, normalize them before translation.
    // Do not forget to normalize type arguments first.
    case AppliedType(TypeName(base), targs) =>
      if (traitNames contains base)
        Nil -> N
      else
        getBaseClassAndFields(applyTypeAlias(base, targs map { substitute(_) }))
    // There is some other possibilities such as `class Fun[A]: A -> A`.
    // But it is not achievable in JavaScript.
    case Rem(_, _) | TypeVar(_, _) | Literal(_) | Recursive(_, _) | Bot | Top |
        Tuple(_) | Neg(_) | Bounds(_, _) | WithExtension(_, _) |
        Function(_, _) | Union(_, _) | Arr(_) =>
      throw TypingUnitError(s"unable to derive from type $ty")
  }

  // This function normalizes a type, removing all `AppliedType`s.
  private def substitute(
      body: Type,
      subs: collection.immutable.HashMap[Str, Type] =
        collection.immutable.HashMap.empty
  ): Type = {
    body match {
      case Neg(ty) =>
        Neg(substitute(ty, subs))
      case AppliedType(TypeName(name), targs) =>
        applyTypeAlias(name, targs map { substitute(_, subs) })
      case Function(lhs, rhs) =>
        Function(substitute(lhs, subs), substitute(rhs, subs))
      case Inter(lhs, rhs) =>
        Inter(substitute(lhs, subs), substitute(rhs, subs))
      case Record(fields) =>
        Record(fields map { case (k, v) => k -> substitute(v, subs) })
      case Union(lhs, rhs) =>
        Union(substitute(lhs, subs), substitute(rhs, subs))
      case Tuple(fields) =>
        Tuple(fields map { case (k, v) => k -> substitute(v, subs) })
      case TypeName(name) =>
        subs get name match {
          case N =>
            typeAliasMap get name match {
              case N              => TypeName(name)
              case S(Nil -> body) => substitute(body, subs)
              case S(tparams -> _) =>
                throw TypingUnitError(
                  s"type $name expects ${tparams.length} type parameters but nothing provided"
                )
            }
          case S(ty) => ty
        }
      case Recursive(uv, ty) => Recursive(uv, substitute(ty, subs))
      case Rem(ty, fields)   => Rem(substitute(ty, subs), fields)
      case Bot | Top | _: Literal | _: TypeVar | _: Bounds | _: WithExtension =>
        body
      case Arr(_) =>
        throw TypingUnitError(s"type Arr is not supported currently")
    }
  }

  // This function normalizes something like `T[A, B]`.
  private def applyTypeAlias(name: Str, targs: Ls[Type]): Type =
    typeAliasMap get name match {
      case S(tparams -> body) =>
        assert(targs.length === tparams.length, targs -> tparams)
        substitute(
          body,
          collection.immutable.HashMap(
            tparams zip targs map { case (k, v) => k -> v }: _*
          )
        )
      case N =>
        if (classNames contains name) {
          // For classes with type parameters, we just erase the type parameters.
          TypeName(name)
        } else {
          throw TypingUnitError(s"type $name is not defined")
        }
    }
}
