package mlscript.codegen.typescript

import mlscript.utils._
import mlscript.{ TypeVar, SourceCode, Type, Union, TypeName, Inter, Record, Tuple,
  Top, Bot, Literal, Function, Recursive, AppliedType, Neg, Rem, Bounds, WithExtension,
  IntLit, DecLit, StrLit, Arr }
import mlscript.{JSBackend, JSLit}
import mlscript.ShowCtx

final case class IllFormedTsTypeError(message: String) extends Exception(message);

/** A class to hold to the context while converting mlscript types to typescript representation.
  *
  * polarity tracks polarity of the current type. * Some(true) - positive polarity * Some(false) - negative polarity *
  * None - no polarity (invariant)
  *
  * argCounter tracks number of new argument variable names introduced and then is used to generate unique names
  *
  * newTypeAlias and typeParams stores information of any new type aliases and params defined when converting. This
  * information is collected to arrange the source code in proper order.
  *
  * Existing type vars is used to maintain a mapping from originally created type variables to their names. This is then
  * used to resolve `TypeVar` to their SourceCode representation.
  *
  * @param polarity
  * @param argCounter
  * @param existingTypeVars
  * @param newTypeAlias
  * @param typeParams
  */
class ToTsTypegenContext(
    var polarity: Option[Boolean] = Some(true),
    var argCounter: Int = 0,
    var existingTypeVars: Map[TypeVar, String] = Map.empty,
    // adhoc type vars introduced during conversion
    var newTypeAlias: List[SourceCode] = List.empty,
    // adhoc type parameters introduced during conversion
    var newTypeParams: List[SourceCode] = List.empty
) {

  /** Polarity of a type is flipped if it's at function input. No change if it's None.
    *
    * @param newPolarity
    */
  def flipPolarity: Unit = {
    this.polarity = this.polarity.map(prev => !prev)
  }
}

object ToTsTypegenContext {
  def empty: ToTsTypegenContext = new ToTsTypegenContext();
}

object TsTypegen {

  /** Converts a term to its typescript type declarations, including any new type aliases
    * created in order to represent it's type
    *
    * @param mlType
    *   the type to be converted to source code
    * @param termName
    *   name of term that's been declared. If none is given default "res"
    *   is used to indicate type of value of result from evaluating the term
    * @return
    */
  def toTsTypeSourceCode(mlType: Type, termName: Option[String] = None): SourceCode = {
    val ctx = ToTsTypegenContext.empty;

    // Create a mapping from type var to their friendly name for lookup
    // Also add them as type parameters to the current type because typescript
    // uses parametric polymorphism
    ctx.existingTypeVars = ShowCtx.mk(mlType :: Nil, "").vs;
    val tsType = TsTypegen.toTsType(mlType, ctx);

    ctx.newTypeParams = ctx.newTypeParams ++ ctx.existingTypeVars.map(tup => SourceCode(tup._2));
    termName match {
      // term definitions bound to names are exported
      // as declared variables with their derived types
      case Some(name) =>
        SourceCode("// start ts") +
        SourceCode.concat(ctx.newTypeAlias) + (SourceCode(s"export declare const $name") ++
        SourceCode.paramList(ctx.newTypeParams) ++ SourceCode.colon ++ tsType) +
        SourceCode("// end ts")
      // terms definitions not bound to names are not exported by default
      // they are bound to an implicit res variable and the type of res
      // is shown here
      case None =>
        SourceCode("// start ts") +
        SourceCode.concat(ctx.newTypeAlias) +
        (SourceCode(s"type res") ++ SourceCode.paramList(ctx.newTypeParams) ++ SourceCode.equalSign ++ tsType) +
        SourceCode("// end ts")
    }
  }

  /** Converts an mlscript type to source code representation of the ts type. It also keep tracks of extra type
    * variables and type parameters defined through the context.
    *
    * Takes a context to maintain state.
    * @param ctx
    * @return
    */
  def toTsType(implicit
      mlType: Type,
      ctx: ToTsTypegenContext,
  ): SourceCode = {
    mlType match {
      // these types do not mutate typegen context
      case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
        SourceCode("boolean")
      case Union(lhs, rhs) =>
        SourceCode.sepBy(
          List(toTsType(lhs, ctx), toTsType(rhs, ctx)),
          SourceCode.separator
        )
      case Inter(lhs, rhs) =>
        SourceCode.sepBy(
          List(toTsType(lhs, ctx), toTsType(rhs, ctx)),
          SourceCode.ampersand
        )
      case Record(fields) =>
        SourceCode.recordWithEntries(
          fields.map(entry => (SourceCode(entry._1.name), toTsType(entry._2, ctx)))
        )
      // unwrap extra parenthesis when tuple has single element
      case Tuple(fields) =>
        if (fields.length === 1) {
          (toTsType(fields(0)._2, ctx))
        } else {
          SourceCode.horizontalArray(fields.map(field => toTsType(field._2, ctx)))
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
        val currArgCount = ctx.argCounter;
        val currPolarity = ctx.polarity;

        ctx.argCounter += 1;
        ctx.flipPolarity
        val lhsTypeSource = toTsType(lhs, ctx);
        ctx.polarity = currPolarity;

        val rhsTypeSource = toTsType(rhs, ctx);

        (SourceCode(s"arg${currArgCount}") ++ SourceCode.colon ++ lhsTypeSource).parenthesized ++
        SourceCode.fatArrow ++ rhsTypeSource
      // a recursive type is wrapped in a self referencing Recursion type
      // this wrapped form is used only inside it's body
      case Recursive(uv, body) =>
        val uvTsType = toTsType(uv, ctx)

        // use modified context for converting body type. This will replace
        // all use of uv type var with it's wrapped type.
        ctx.newTypeAlias = (SourceCode("type ") ++ uvTsType ++
          SourceCode.equalSign ++ toTsType(body, ctx)) +: ctx.newTypeAlias

        // recursive type is no longer a type variable it's an alias instead
        ctx.existingTypeVars = ctx.existingTypeVars.removed(uv)

        uvTsType
      // this occurs when polymorphic types (usually classes) are applied
      case AppliedType(base, targs) =>
        if (targs.length =/= 0) {
          SourceCode(base.name) ++ SourceCode.openAngleBracket ++
          SourceCode.sepBy(targs.map(toTsType(_, ctx))) ++ SourceCode.closeAngleBracket
        } else {
          // no type arguments required then print without brackets
          SourceCode(base.name)
        }
      // Neg requires creating a parameterized type alias to hold the negated definition
      case Neg(base) =>
        // Negative type only works in positions of negative polarity
        if (ctx.polarity =/= Some(false)) {
          throw IllFormedTsTypeError(
            s"Cannot generate type for negated type at negative polarity for $mlType"
          )
        }
        val typeParam = s"T${ctx.argCounter}";
        ctx.argCounter += 1;
        val typeAliasName = s"talias${ctx.argCounter}<$typeParam>"
        ctx.argCounter += 1;
        val typeAlias = s"type $typeAliasName = $typeParam extends ${toTsType(base, ctx)} ? never : $typeParam"

        ctx.newTypeParams = SourceCode(typeParam) +: ctx.newTypeParams;
        ctx.newTypeAlias = SourceCode(typeAlias) +: ctx.newTypeAlias;
        SourceCode(typeAliasName)
      case Rem(base, names) =>
        SourceCode("Omit") ++
          SourceCode.openAngleBracket ++ toTsType(base, ctx) ++ SourceCode.commaSpace ++
          SourceCode.record(names.map(name => SourceCode(name.name))) ++
          SourceCode.closeAngleBracket
      case Bounds(lb, ub) =>
        ctx.polarity match {
          // positive polarity takes upper bound
          case Some(true) => toTsType(ub, ctx)
          // negative polarity takes lower bound
          case Some(false) => toTsType(lb, ctx)
          // TODO: Yet to handle invariant types
          case None =>
            throw IllFormedTsTypeError(s"Cannot generate type for invariant type $mlType")
        }
      case WithExtension(base, rcd) =>
        toTsType(Inter(Rem(base, rcd.fields.map(tup => tup._1)), rcd), ctx)
      // type variables friendly names have been pre-calculated in the context
      // throw an error if it doesn't exist
      case t @ TypeVar(_, _) =>
        print(ctx.existingTypeVars)
        ctx.existingTypeVars
          .get(t)
          .map(s => SourceCode(s))
          .getOrElse(
            throw IllFormedTsTypeError(s"Did not find mapping for type variable $t. Unable to generated ts type.")
          )
      case Arr(_) => throw IllFormedTsTypeError(s"Array type currently not supported for $mlType")
    }
  }
}
