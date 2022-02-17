package mlscript.codegen.typescript

import mlscript.utils._
import mlscript.{ TypeVar, SourceCode, Type, Union, TypeName, Inter, Record, Tuple,
  Top, Bot, Literal, Function, Recursive, AppliedType, Neg, Rem, Bounds, WithExtension,
  IntLit, DecLit, StrLit, Arr }
import mlscript.{JSBackend, JSLit}
import mlscript.ShowCtx
import mlscript.Typer
import mlscript.TypeDef
import mlscript.Terms
import mlscript.codegen.Scope
import mlscript.SourceLine
import scala.collection.mutable.{ListBuffer, Map => MutMap}

final case class IllFormedTsTypeError(message: String) extends Exception(message);

/** Typescript typegen code builder for an mlscript typing unit
  */
final case class TsTypegenCodeBuilder() {
  // store converted mlscript type definitions and terms created in mlscript
  // use typeScope and termScope to generate non-conflicting names for both
  private val typeScope: Scope = Scope()
  private val termScope: Scope = Scope()
  private val typegenCode: ListBuffer[SourceCode] = ListBuffer.empty;

  /** Return complete typegen code for current typing unit
    *
    * @return
    *   SourceCode
    */
  def toSourceCode(): SourceCode = {
    SourceCode("// start ts") +=: typegenCode
    typegenCode += SourceCode("// end ts")
    SourceCode.bulkConcat(typegenCode)
  }

  /** Context for converting a statement or type definition
    * 
    *
    * @param existingTypeVars
    *   type variables defined for the current type
    * @param typeVarMapping
    *   mapping from type variables to their clash-free parameter names
    * @param termScope
    *   scope for argument names
    * @param typeScope
    *   scope for type parameter names
    */
  protected case class TypegenContext(
      val existingTypeVars: Map[TypeVar, String],
      // Mapping type variables existing and new ones
      // to clash-free type names generated for current typing unit
      val typeVarMapping: MutMap[TypeVar, String],
      // a scope for generating unique argument names
      val termScope: Scope,
      // a scope for generating unique type parameter names
      val typeScope: Scope
  ) {
    /** Try to find name for type variable in mapping. If it
      * doesn't exist check existing type variable names mapping
      * 
      * @param t TypeVar
      * @return
      *   Left[String, None] is from type var mapping
      *   Right[None, String] is from existing type variable names
      */
    def findTypeVarName(t: TypeVar): Either[String, String] = {
      this.typeVarMapping.get(t).map(Left(_)).getOrElse({
        this.existingTypeVars
          .get(t)
          .map(Right(_))
          .getOrElse(
            throw IllFormedTsTypeError(s"Did not find mapping for type variable $t. Unable to generated ts type.")
          )
      })
    }
  }

  object TypegenContext {
    def apply(mlType: Type): TypegenContext = {
      val existingTypeVars = ShowCtx.mk(mlType :: Nil, "").vs;
      // initialize local term scope with global term scope as parent
      // this will reduce cases where global names are similar to function
      // argument names. For e.g. the below case will be avoided
      // export const arg0: int
      // export const f: (arg0: int) => int
      TypegenContext(existingTypeVars, MutMap.empty, Scope(Seq.empty, termScope), Scope())
    }
  }

  /** Converts a term definition to its typescript declaration including any adhoc type aliases created for it
    *
    * @param mlType
    *   the type to be converted to source code
    * @param termName
    *   name of term that's been declared. If none is given default "res" is used to indicate type of value of result
    *   from evaluating the term
    * @return
    */
  def addTypeGenDefinition(mlType: Type, termName: Option[String]): Unit = {
    // `res` definitions are allowed to be shadowed
    val defName = termName match {
      case Some(name) => {
        if (termScope.has(name)) {
          throw new IllFormedTsTypeError(s"A declaration with name $termName already exists.")
        } else {
          termScope.allocateJavaScriptName(name)
          name
        }
      }
      case None => "res"
    }

    // Create a mapping from type var to their friendly name for lookup
    val typegenCtx = TypegenContext(mlType)
    val tsType = toTsType(mlType)(typegenCtx, Some(true));
    val typeParams = typegenCtx.typeVarMapping.iterator.map(tup => SourceCode(tup._2)).toList

    typegenCode += (SourceCode(s"export declare const $defName") ++
      SourceCode.paramList(typeParams) ++ SourceCode.colon ++ tsType)
  }

  /** Converts an mlscript type to source code representation of the ts type. It also keep tracks of extra type
    * variables and type parameters defined through the context.
    *
    * polarity tracks polarity of the current type.
    * * Some(true) - positive polarity
    * * Some(false) - negative polarity
    * * None - no polarity (invariant)
    *
    * @param mlType
    *   mlscript type to convert
    * @param typegenCtx
    *   type generation context for allocating new names
    * @param pol
    *   polarity of type
    * @return
    */
  private def toTsType(mlType: Type)(implicit
      typegenCtx: TypegenContext,
      pol: Option[Boolean]
  ): SourceCode = {
    mlType match {
      // these types do not mutate typegen context
      case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
        SourceCode("boolean")
      case Union(lhs, rhs) =>
        SourceCode.sepBy(
          List(toTsType(lhs), toTsType(rhs)),
          SourceCode.separator
        )
      case Inter(lhs, rhs) =>
        SourceCode.sepBy(
          List(toTsType(lhs), toTsType(rhs)),
          SourceCode.ampersand
        )
      case Record(fields) =>
        SourceCode.recordWithEntries(
          fields.map(entry => (SourceCode(entry._1.name), toTsType(entry._2)))
        )
      // unwrap extra parenthesis when tuple has single element
      case Tuple(fields)  => SourceCode.horizontalArray(fields.map(field => toTsType(field._2)))
      case Top            => SourceCode("unknown")
      case Bot            => SourceCode("never")
      case TypeName(name) => SourceCode(name)
      case Literal(IntLit(n)) =>
        SourceCode(n.toString + (if (JSBackend isSafeInteger n) "" else "n"))
      case Literal(DecLit(n)) => SourceCode(n.toString)
      case Literal(StrLit(s)) => SourceCode(JSLit.makeStringLiteral(s))

      // these types may mutate typegen context by argCounter, or
      // by creating new type aliases
      case Function(lhs, rhs) =>
        val arg = typegenCtx.termScope.allocateJavaScriptName("arg");

        // flip polarity for input type of function
        val lhsTypeSource = toTsType(lhs)(typegenCtx, pol.map(!_));
        val rhsTypeSource = toTsType(rhs);

        (SourceCode(s"$arg") ++ SourceCode.colon ++ lhsTypeSource).parenthesized ++
          SourceCode.fatArrow ++ rhsTypeSource
      // a recursive type is aliased as a self referencing type
      // NOTE: It is assumed that inside the body type there cannot be another recursive
      // type with the same typevar as uv as in ((f as f) as f) is not possible
      case Recursive(uv, body) =>
        val friendlyName = toTsType(uv)
        // allocate the clash-free name for uv in typegen scope
        // update mapping from type variables to
        val uvNewName = typeScope.allocateJavaScriptName(friendlyName.toString())
        typegenCtx.typeVarMapping += ((uv, uvNewName))
        val bodyType = toTsType(body)
        // remove type variable mapping so that it doesn't add a type parameter
        typegenCtx.typeVarMapping -= (uv)

        // self referencing alias for the recursive type
        typegenCode += (SourceCode("export type ") ++ SourceCode(uvNewName) ++ SourceCode.equalSign ++ bodyType)
        SourceCode(uvNewName)
      case AppliedType(base, targs) =>
        if (targs.length =/= 0) {
          SourceCode(base.name) ++ SourceCode.openAngleBracket ++
            SourceCode.sepBy(targs.map(toTsType(_))) ++ SourceCode.closeAngleBracket
        } else {
          // no type arguments required then print without brackets
          SourceCode(base.name)
        }
      // Neg requires creating a parameterized type alias to hold the negated definition
      case Neg(base) =>
        // Negative type only works in positions of positive polarity
        if (pol === Some(false)) {
          throw IllFormedTsTypeError(
            s"Cannot generate type for negated type at negative polarity for $mlType"
          )
        }

        // try to allocate common Negate type alias
        if (!typeScope.has("Neg")) {
          typeScope.allocateJavaScriptName("Neg")
          typegenCode += SourceCode("type Neg<NegatedType, FromType> = FromType extends NegatedType ? never: FromType")
        }

        // introduce a new type parameter for the `FromType`
        val typeParam = typegenCtx.typeScope.allocateJavaScriptName("t")
        typegenCtx.typeVarMapping += ((TypeVar(Right(typeParam), None), typeParam))

        val baseType = toTsType(base)
        SourceCode(s"Neg<$baseType, $typeParam>")
      case Rem(base, names) =>
        SourceCode("Omit") ++
          SourceCode.openAngleBracket ++ toTsType(base) ++ SourceCode.commaSpace ++
          SourceCode.record(names.map(name => SourceCode(name.name))) ++
          SourceCode.closeAngleBracket
      case Bounds(lb, ub) =>
        pol match {
          // positive polarity takes upper bound
          case Some(true) => toTsType(ub)
          // negative polarity takes lower bound
          case Some(false) => toTsType(lb)
          // TODO: Yet to handle invariant types
          case None =>
            throw IllFormedTsTypeError(s"Cannot generate type for invariant type $mlType")
        }
      case WithExtension(base, rcd) =>
        toTsType(Inter(Rem(base, rcd.fields.map(tup => tup._1)), rcd))
      // get clash free name for type variable
      case t @ TypeVar(_, _) =>
        typegenCtx.findTypeVarName(t).fold(
          name => SourceCode(name),
          // type variable has been accessed for the first time
          // allocate a clash free name in type variable mapping
          friendlyName => {
            val newName = typegenCtx.typeScope.allocateJavaScriptName(s"t$friendlyName")
            typegenCtx.typeVarMapping += ((t, newName))
            SourceCode(newName)
          }
        )
      case Arr(_) => throw IllFormedTsTypeError(s"Array type currently not supported for $mlType")
    }
  }
}
