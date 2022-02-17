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
import scala.collection.mutable.{ListBuffer => MutListBuffer}

final case class IllFormedTsTypeError(message: String) extends Exception(message);

/** Typescript typegen code builder for an mlscript typing unit
  */
final case class TsTypegenCodeBuilder() {
  // store type definitions created in mlscript and created by type generation
  // this makes it possible to generate non-conflicting names for new types
  // initialize with existing type definition names
  // TODO: implement type generation for type definitions and add names there
  // private val typegenScope: Scope = Scope(typeDefs.map(_.nme.name))
  private val typegenScope: Scope = Scope()
  private val typegenCode: MutListBuffer[SourceCode] = MutListBuffer.empty;

  /** Return complete generated typegen code
    *
    * @return
    *   SourceCode
    */
  def toSourceCode(): SourceCode = {
    for (code <- typegenCode) {
      println(code.toString())
    }
    SourceCode("// start ts") +=: typegenCode
    typegenCode += SourceCode("// end ts")
    SourceCode.bulkConcat(typegenCode)
  }

  /** Converts a definition to its typescript type declarations, including any new type aliases created in order to
    * represent it's type.
    *
    * @param mlType
    *   the type to be converted to source code
    * @param termName
    *   name of term that's been declared. If none is given default "res" is used to indicate type of value of result
    *   from evaluating the term
    * @return
    */
  def addTypeGenDefinition(mlType: Type, termName: Option[String]): Unit = {
    val typegenCtx = ToTsTypegenContext.empty;

    val defName = termName match {
      case Some(name) => {
        try {
          typegenScope.allocateJavaScriptName(name)
          name
        } catch {
          case _: Throwable => throw new IllFormedTsTypeError(s"A declaration with name $termName already exists.")
        }
      }
      case None => "res"
    }
    // allocate term name to current type unit context

    // Create a mapping from type var to their friendly name for lookup
    // Also add them as type parameters to the current type because typescript
    // uses parametric polymorphism
    typegenCtx.existingTypeVars = ShowCtx.mk(mlType :: Nil, "").vs;
    val tsType = toTsType(mlType)(typegenCtx, Some(true));

    typegenCtx.newTypeParams = typegenCtx.newTypeParams ++ typegenCtx.existingTypeVars.map(tup => SourceCode(tup._2));
    typegenCode += (SourceCode(s"export declare const $defName") ++
      SourceCode.paramList(typegenCtx.newTypeParams) ++ SourceCode.colon ++ tsType)
  }

  /** The context while converting mlscript types to typescript representation.
    *
    * newTypeAlias and typeParams stores information of any new type aliases and params defined when converting. This
    * information is collected to arrange the source code in proper order.
    *
    * Existing type vars is used to maintain a mapping from originally created type variables to their names. This is
    * then used to resolve `TypeVar` to their SourceCode representation.
    *
    * @param existingTypeVars
    * @param newTypeAlias
    * @param typeParams
    */
  class ToTsTypegenContext(
      var existingTypeVars: Map[TypeVar, String] = Map.empty,
      // adhoc type parameters introduced during conversion
      var newTypeParams: List[SourceCode] = List.empty,
      // a scope for generating unique argument names
      val argScope: Scope = Scope.apply()
  )

  object ToTsTypegenContext {
    def empty: ToTsTypegenContext = new ToTsTypegenContext();
  }

  /** Converts an mlscript type to source code representation of the ts type. It also keep tracks of extra type
    * variables and type parameters defined through the context.
    *
    * polarity tracks polarity of the current type. Some(true) - positive polarity Some(false) - negative polarity None
    * - no polarity (invariant)
    *
    * Takes a context to maintain state.
    * @param ctx
    * @return
    */
  private def toTsType(mlType: Type)(implicit
      typegenCtx: ToTsTypegenContext,
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
      case Tuple(fields) =>
        if (fields.length === 1) {
          (toTsType(fields(0)._2))
        } else {
          SourceCode.horizontalArray(fields.map(field => toTsType(field._2)))
        }
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
        val arg = typegenCtx.argScope.allocateJavaScriptName("arg");

        // flip polarity for input type of function
        val lhsTypeSource = toTsType(lhs)(typegenCtx, pol.map(!_));
        val rhsTypeSource = toTsType(rhs);

        (SourceCode(s"$arg") ++ SourceCode.colon ++ lhsTypeSource).parenthesized ++
          SourceCode.fatArrow ++ rhsTypeSource
      // a recursive type is wrapped in a self referencing Recursion type
      // this wrapped form is used only inside it's body
      // NOTE: It is assumed that inside the body type there cannot be another recursive
      // type with the same typevar as uv
      // as in ((f as f) as f) is not possible
      case Recursive(uv, body) =>
        // get the the friendly name for uv
        val uvTypeName = toTsType(uv)
        // allocate the friendly in typegen scope
        // fails with exception if name already exists
        // TODO: handle it
        typegenCtx.argScope.allocateJavaScriptName(uvTypeName.toString())

        // self referencing alias for the recursive type
        typegenCode += (SourceCode("type ") ++ uvTypeName ++ SourceCode.equalSign ++ toTsType(body))
        uvTypeName
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
        // Negative type only works in positions of negative polarity
        if (pol =/= Some(false)) {
          throw IllFormedTsTypeError(
            s"Cannot generate type for negated type at negative polarity for $mlType"
          )
        }

        // try to allocate common Negate type alias
        // skip if it already exists
        try {
          typegenScope.allocateJavaScriptName("Neg")
          typegenCode += SourceCode("type Neg<NegatedType, FromType> = FromType extends NegatedType ? never: FromType")
        } catch {
          case _: Throwable => ()
        }

        // introduce a new type parameter for the `FromType`
        // and add it to type parameters of current context
        val typeParam = typegenScope.allocateJavaScriptName()
        typegenCtx.newTypeParams = SourceCode(typeParam) +: typegenCtx.newTypeParams;
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
      // type variables friendly names have been pre-calculated in the context
      // throw an error if it doesn't exist
      case t @ TypeVar(_, _) =>
        print(typegenCtx.existingTypeVars)
        typegenCtx.existingTypeVars
          .get(t)
          .map(s => SourceCode(s))
          .getOrElse(
            throw IllFormedTsTypeError(s"Did not find mapping for type variable $t. Unable to generated ts type.")
          )
      case Arr(_) => throw IllFormedTsTypeError(s"Array type currently not supported for $mlType")
    }
  }
}
