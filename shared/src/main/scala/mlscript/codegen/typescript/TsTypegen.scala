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
import mlscript.SourceLine
import scala.collection.mutable.{ListBuffer, Map => MutMap}
import mlscript.codegen.Scope

final case class IllFormedTsTypeError(message: String) extends Exception(message);

/** Typescript typegen code builder for an mlscript typing unit
  */
final case class TsTypegenCodeBuilder() {
  // store converted mlscript type definitions and terms created in mlscript
  // use typeScope and termScope to generate non-conflicting names for both
  private val typeScope: Scope = Scope("globalTypeScope")
  private val termScope: Scope = Scope("globalTermScope")
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
    * @param typeVarMapping
    *   mapping from type variables to their clash-free parameter names
    * @param recTypeVarSet
    *   Set of recursive type variables for the type where context was intialized
    * @param recTypeVarSet
    *   Set of non-recursive type variables for the type where context was intialized
    * @param termScope
    *   scope for argument names
    * @param typeScope
    *   scope for type parameter names
    */
  protected case class TypegenContext(
      val typeVarMapping: MutMap[TypeVar, SourceCode],
      val recTypeVarSet: Set[TypeVar],
      val nonRecTypeVarSet: Set[TypeVar],
      val termScope: Scope,
      val typeScope: Scope
  )

  object TypegenContext {
    def apply(mlType: Type): TypegenContext = {
      val existingTypeVars = ShowCtx.mk(mlType :: Nil, "").vs
      val (recVarSet, nonRecVarSet) = mlType.partitionRecTypeVarSet
      val typegenTypeScope = Scope("localTypeScope", List.empty, typeScope)
      val typegenTermScope = Scope("localTermScope", List.empty, termScope)
      val typeVarMapping = MutMap.empty[TypeVar, SourceCode]
      existingTypeVars.iterator.foreach(kv => {
        val name = typegenTypeScope.declareRuntimeSymbol(kv._2)
        typeVarMapping += ((kv._1, SourceCode(kv._2)))
      })

      // initialize local term scope with global term scope as parent
      // this will reduce cases where global names are similar to function
      // argument names. For e.g. the below case will be avoided
      // export const arg0: int
      // export const f: (arg0: int) => int
      TypegenContext(typeVarMapping, recVarSet, nonRecVarSet, typegenTermScope, typegenTypeScope)
    }

    // create a context with pre-created type var to name mapping
    def apply(mlType: Type, typeVarMapping: MutMap[TypeVar, SourceCode]): TypegenContext = {
      val (recVarSet, nonRecVarSet) = mlType.partitionRecTypeVarSet
      val typegenTypeScope = Scope("localTypeScope", List.empty, typeScope)
      val typegenTermScope = Scope("localTermScope", List.empty, termScope)
      TypegenContext(typeVarMapping, recVarSet, nonRecVarSet, typegenTermScope, typegenTypeScope)
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
  def addTypeGenTermDefinition(mlType: Type, termName: Option[String]): Unit = {
    // `res` definitions are allowed to be shadowed
    val defName = termName match {
      case Some(name) => {
        if (termScope.existsRuntimeSymbol(name)) {
          throw new IllFormedTsTypeError(s"A declaration with name $termName already exists.")
        } else {
          termScope.declareRuntimeSymbol(name)
          name
        }
      }
      case None => "res"
    }

    // Create a mapping from type var to their friendly name for lookup
    val typegenCtx = TypegenContext(mlType)
    val tsType = toTsType(mlType)(typegenCtx, Some(true), false);
    // only use non recursive type variables for type parameters
    val typeParams = typegenCtx.typeVarMapping.iterator
      .filter(tup => typegenCtx.nonRecTypeVarSet.contains(tup._1))
      .map(_._2)
      .toList

    typegenCode += (SourceCode(s"export declare const $defName") ++
      SourceCode.paramList(typeParams) ++ SourceCode.colon ++ tsType)
  }

  /** Converts an mlscript type to source code representation of the ts type. It also keep tracks of extra type
    * variables and type parameters defined through the context.
    *
    * polarity tracks polarity of the current type. * Some(true) - positive polarity * Some(false) - negative polarity *
    * None - no polarity (invariant)
    *
    * @param mlType
    *   mlscript type to convert
    * @param typegenCtx
    *   type generation context for allocating new names
    * @param pol
    *   polarity of type
    * @param funcArg
    *   true if Tuple type is the lhs of a function. Used to translate tuples as multi-parameter functions
    * @return
    */
  private def toTsType(mlType: Type)(implicit
      typegenCtx: TypegenContext,
      pol: Option[Boolean],
      funcArg: Boolean
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
      case Tuple(fields) =>
        // tuple that is a function argument becomes
        // multi-parameter argument list
        if (funcArg) {
          val argList = fields
            .map(field => {
              val arg = typegenCtx.termScope.declareRuntimeSymbol("arg");
              val argType = toTsType(field._2)
              SourceCode(s"$arg: ") ++ argType
            })
            .toList
          SourceCode.sepBy(argList).parenthesized
        }
        // regular tuple becomes fixed length array
        else {
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
        val arg = typegenCtx.termScope.declareRuntimeSymbol("arg");

        // flip polarity for input type of function
        // lhs translates to the complete argument list
        val lhsTypeSource = toTsType(lhs)(typegenCtx, pol.map(!_), true);
        val rhsTypeSource = toTsType(rhs);

        lhsTypeSource ++ SourceCode.fatArrow ++ rhsTypeSource
      // a recursive type is aliased as a self referencing type
      case Recursive(uv, body) =>
        // allocate the clash-free name for uv in typegen scope
        // update mapping from type variables to
        val uvName = toTsType(uv)
        val typeVarMapping = typegenCtx.typeVarMapping
        // create new type gen context and recalculate rec var and
        // non-rec var for current type
        val nestedTypegenCtx = TypegenContext(mlType, typeVarMapping)

        // recursive type does not have any other type variables
        // (except itself)
        if (nestedTypegenCtx.nonRecTypeVarSet.size === 0) {
          val bodyType = toTsType(body)(typegenCtx, pol, funcArg);
          typegenCode += (SourceCode(s"export type $uvName") ++
            SourceCode.equalSign ++ bodyType)
          uvName
        }
        // recursive type has other type variables
        // so now it is an applied type
        else {
          val uvTypeParams = typeVarMapping.iterator
            .filter(tup => nestedTypegenCtx.nonRecTypeVarSet.contains(tup._1))
            .map(_._2)
            .toList
          val uvAppliedName = uvName ++ SourceCode.paramList(uvTypeParams)
          typeVarMapping += ((uv, uvAppliedName))
          val bodyType = toTsType(body)(nestedTypegenCtx, pol, funcArg);
          typegenCode += (SourceCode(s"export type $uvAppliedName") ++
            SourceCode.equalSign ++ bodyType)
          uvAppliedName
        }

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
        if (!typeScope.existsRuntimeSymbol("Neg")) {
          typeScope.declareRuntimeSymbol("Neg")
          typegenCode += SourceCode("type Neg<NegatedType, FromType> = FromType extends NegatedType ? never: FromType")
        }

        // introduce a new type parameter for the `FromType`
        val typeParam = typegenCtx.typeScope.declareRuntimeSymbol()
        typegenCtx.typeVarMapping += ((TypeVar(Right(typeParam), None), SourceCode(typeParam)))

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
        typegenCtx.typeVarMapping
          .get(t)
          .getOrElse({
            throw IllFormedTsTypeError(s"Did not find mapping for type variable $t. Unable to generated ts type.")
          })
      case Arr(_) => throw IllFormedTsTypeError(s"Array type currently not supported for $mlType")
    }
  }
}
