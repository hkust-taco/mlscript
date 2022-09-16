package mlscript
package codegen.typescript

import scala.collection.mutable.{ListBuffer, Map => MutMap, SortedMap => MutSortedMap}
import scala.collection.immutable.Set

import mlscript.codegen.CodeGenError
import mlscript.utils._, shorthands._
import mlscript.codegen._

/** Typescript typegen code builder for an mlscript typing unit
  */
final class TsTypegenCodeBuilder {
  private val typeScope: Scope = Scope("globalTypeScope")
  private val termScope: Scope = Scope("globalTermScope")
  private val typegenCode: ListBuffer[SourceCode] = ListBuffer.empty

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
    * @param termScope
    *   scope for argument names
    * @param typeScope
    *   scope for type parameter names
    */
  protected case class TypegenContext(
      typeVarMapping: MutSortedMap[TypeVar, String],
      termScope: Scope,
      typeScope: Scope,
  )

  object TypegenContext {

    def apply(mlType: Type): TypegenContext = {
      val existingTypeVars = ShowCtx.mk(mlType :: Nil, "").vs
      val typegenTypeScope = typeScope.derive("localTypeScope")
      val typegenTermScope = termScope.derive("localTermScope")
      val typeVarMapping = existingTypeVars.to(MutSortedMap)

      // initialize local term scope with global term scope as parent
      // this will reduce cases where global names are similar to function
      // argument names. For e.g. the below case will be avoided
      // export const arg0: int
      // export const f: (arg0: int) => int
      TypegenContext(typeVarMapping, typegenTermScope, typegenTypeScope)
    }

    // create a context with pre-created type var to name mapping
    def apply(mlType: Type, typeVarMapping: MutSortedMap[TypeVar, String]): TypegenContext = {
      val typegenTypeScope = typeScope.derive("localTypeScope")
      val typegenTermScope = termScope.derive("localTermScope")
      TypegenContext(typeVarMapping, typegenTermScope, typegenTypeScope)
    }
  }

  def declareTypeDef(typeDef: TypeDef): TypeSymbol = typeScope.declareTypeSymbol(typeDef)

  /**
    * Start adding type definition and store partially translated
    * type definition as state
    *
    * @param typeDef
    */
  def addTypeDef(typeDef: TypeDef, methods: List[(String, Type)]): Unit = {
    val tySymb = typeScope.getTypeSymbol(typeDef.nme.name).getOrElse(
      throw CodeGenError(s"No type definition for ${typeDef.nme.name} exists")
    )
    tySymb match {
      case (classInfo: ClassSymbol) => addTypeGenClassDef(classInfo, methods)
      case (aliasInfo: TypeAliasSymbol) => addTypeGenTypeAlias(aliasInfo)
      case (traitInfo: TraitSymbol) => addTypegenTraitDef(traitInfo, methods)
    }
  }

  /**
    * Translate class method to typescript declaration
    *
    * @param declTypeParms type params from class or trait declaring the method
    * @param methodName
    * @param methodType
    */
  def addMethodDeclaration(declTypeParams: Set[String], methodName: String, methodType: Type): SourceCode = {
    // unwrap method function type to remove implicit this
    val methodSourceCode = methodType match {
      case Function(lhs, rhs) => {
        // Create a mapping from type var to their friendly name for lookup
        val typegenCtx = TypegenContext(rhs)

        rhs match {
          case f@Function(lhs, rhs) =>
            val lhsTypeSource = toTypegenFunctionLhs(lhs, true)(typegenCtx, Some(false))
            val rhsTypeSource = toTsType(rhs)(typegenCtx, Some(true))

            // only use free variables for type parameters
            val typeParams = typegenCtx.typeVarMapping.iterator
              .filter(tup => rhs.freeTypeVariables.contains(tup._1) &&
                // ignore class type parameters since they are implicitly part of class scope
                // if no name hint then the type variable is certainly not a class type parameter
                // its friendly name has been generated
                tup._1.nameHint.fold(true)(!declTypeParams.contains(_))
              )
              .map { case (_, varName) => SourceCode(varName)}
              .toList
            SourceCode(s"    $methodName") ++ SourceCode.paramList(typeParams) ++ lhsTypeSource ++ SourceCode.colon ++ rhsTypeSource
          case _ =>
            val tsType = toTsType(rhs)(typegenCtx, Some(true))
            // only use free variables for type parameters
            val typeParams = typegenCtx.typeVarMapping.iterator
              .filter(tup => rhs.freeTypeVariables.contains(tup._1) &&
                // ignore class type parameters since they are implicitly part of class scope
                // if no name hint then the type variable is certainly not a class type parameter
                // its friendly name has been generated
                tup._1.nameHint.fold(true)(!declTypeParams.contains(_))
              )
              .map { case (_, varName) => SourceCode(varName)}
              .toList
            // known value methods are translated to readonly attributes of the class
            if (typeParams.isEmpty) SourceCode(s"    readonly $methodName") ++ SourceCode.colon ++ tsType
            // known value methods are not allowed to have type variables in ts
            // else throw CodeGenError(s"Cannot translate known value method named $methodName free type variables")
            else SourceCode(s"    readonly $methodName") ++ SourceCode.paramList(typeParams) ++ SourceCode.colon ++ tsType
        }
      }
      // top level method type must be a function
      case _ => throw CodeGenError(s"Cannot translate malformed method: $methodName because it does not have top level function")
    }

    methodSourceCode
  }

  def addTypegenTraitDef(traitInfo: TraitSymbol, methods: List[(String, Type)]): Unit = {
    val traitName = traitInfo.lexicalName
    val traitBody = traitInfo.body
    val typeParams = traitInfo.params.iterator.map(SourceCode(_)).toList

    // extend super traits
    var traitDeclaration = SourceCode(s"export interface $traitName") ++ SourceCode.paramList(typeParams)
    val superTraits = typeScope.resolveImplementedTraits(traitBody)
    if (!superTraits.isEmpty) {
      val superTraitsCode = superTraits.map { symb =>
        val traitName = symb.lexicalName
        val traitParams = symb.params.iterator.map(SourceCode(_)).toList
        SourceCode(s"$traitName") ++ SourceCode.paramList(traitParams)
      }
      traitDeclaration ++= SourceCode(" extends ") ++ SourceCode.sepBy(superTraitsCode)
    }
    traitDeclaration ++= SourceCode.space ++ SourceCode.openCurlyBrace

    // add fields defined in the trait
    traitBody.collectBodyFieldsAndTypes
      .foreach{case (fieldVar, fieldType) => 
        val fieldCode = toTsType(fieldType)(TypegenContext(fieldType), Some(true))
        traitDeclaration += SourceCode("    ") ++ SourceCode(fieldVar.name) ++ SourceCode.colon ++ fieldCode
      }

    // add methods
    methods.foreach { case (name, methodType) =>
      traitDeclaration += addMethodDeclaration(traitInfo.params.toSet, name, methodType)
    }

    typegenCode += traitDeclaration + SourceCode.closeCurlyBrace
  }

  def addTypeGenClassDef(classInfo: ClassSymbol, methods: List[(String, Type)]): Unit = {
    val className = classInfo.lexicalName
    val classBody = classInfo.body
    val baseClass = typeScope.resolveBaseClass(classBody)
    val typeParams = classInfo.params.iterator.map(SourceCode(_)).toList

    // create mapping for class body fields and types
    // class body includes fields from all implemented traits
    val classFieldsAndType = getClassFieldAndTypes(classInfo)
    // fields can be re-declared with different types at different
    // levels of inheritance. The final type is a union of all these types
      .groupMap(_._1)(_._2)

    // extend with base class if it exists
    var classDeclaration = SourceCode(s"export declare class $className") ++ SourceCode.paramList(typeParams)
    baseClass.map(baseClass => {
      val baseClassName = baseClass.lexicalName
      val baseClassTypeParams = baseClass.params.iterator.map(SourceCode(_)).toList
      classDeclaration ++= SourceCode(s" extends ${baseClass.lexicalName}") ++ SourceCode.paramList(baseClassTypeParams)
    })
    classDeclaration ++= SourceCode.space ++ SourceCode.openCurlyBrace

    // add body fields
    classFieldsAndType
      .map {case (fieldVar, fieldTypes) => 
        val fieldTypesCode = toTypegenInheritedFields(fieldTypes)
        (SourceCode(fieldVar.name), fieldTypesCode)
      }
      .foreach({ case (fieldVar, fieldType) => {
        classDeclaration += SourceCode("    ") ++ fieldVar ++ SourceCode.colon ++ fieldType
      }})

    // constructor needs all fields including super classes
    val allFieldsAndTypes = (classFieldsAndType ++
      baseClass.map(getClassFieldAndTypes(_, true)).getOrElse(List.empty).groupMap(_._1)(_._2))
      .map {case (fieldVar, fieldTypes) =>
        val fieldTypesCode = toTypegenInheritedFields(fieldTypes)
        (SourceCode(fieldVar.name), fieldTypesCode)
      }.toList
    classDeclaration += SourceCode("    constructor(fields: ") ++
      SourceCode.recordWithEntries(allFieldsAndTypes) ++ SourceCode(")")

    // add methods
    methods.foreach { case (name, methodType) =>
      classDeclaration += addMethodDeclaration(classInfo.params.toSet, name, methodType)
    }

    typegenCode += classDeclaration + SourceCode.closeCurlyBrace
  }

  /**
    * Convert the intersections of all distinct fields
    * in the inheritance hierarchy of a trait or class
    * into SourceCode
    *
    * @param fieldTypes
    *   list of field types
    * @return
    *   SourceCode
    */
  private def toTypegenInheritedFields(fieldTypes: List[Type]): SourceCode = {
    // field types will always have 1 or more elements
    fieldTypes.distinct match {
      case fieldType :: Nil => toTsType(fieldType)(TypegenContext(fieldType), Some(true))
      case fieldTypes =>
      // multiple types are intersected hence typegen is done
      // using the precedence of the intersection operator.
      // Only distinct types are considered for intersection
      val fieldTypesCode = fieldTypes.distinct
        .map(fieldType => toTsType(fieldType, false, 2)(TypegenContext(fieldType), Some(true)))
      SourceCode.sepBy(fieldTypesCode, SourceCode.ampersand)
    }
  }

  /**
    * Type conversion for function arguments is a special case. Explicit tuples
    * are handled differently from types that hide tuples.
    * 
    * All parameters are same as `toTsType`
    *
    * @param lhs
    * @param funcArg
    * @param typePrecedence
    * @param typegenCtx
    * @param pol
    * @return
    */
  private def toTypegenFunctionLhs(lhs: Type, funcArg: Boolean = false, typePrecedence: Int = 0)(implicit
      typegenCtx: TypegenContext,
      pol: Option[Boolean],
  ): SourceCode = {
    // flip polarity for input type of function
    // lhs translates to the complete argument list
    // method definition only affects source code representation of top level function
    lhs match {
      // tuple are handled specially because
      // they create their own arg names
      case Tuple(fields) => toTsType(lhs, true)(typegenCtx, Some(false))
      // there are other types which might hide tuple arguments
      // like recursive types, AppliedTypes or bounded types
      // their tuple types can be uniformly converted
      // using a spread operator
      case _ =>
        val arg = typegenCtx.termScope.declareRuntimeSymbol("arg")
        (SourceCode(s"...$arg: ") ++ toTsType(lhs, true)(typegenCtx, Some(false))).parenthesized
    }
  }

  /**
    * List of pairs of field variables and their types for the trait including its super traits
    *
    * @param traitSymbol
    * @return
    */
  private def getTraitFieldAndTypes(body: Type): List[Var -> Type] = {
    val bodyFields = body.collectBodyFieldsAndTypes

    typeScope
      .resolveImplementedTraits(body)
      .foldLeft(bodyFields){ case (fields, symb) =>
        fields ::: getTraitFieldAndTypes(symb.body)
      }
  }

  /**
    * find all fields and types for class including all traits
    * optionally include base class fields as well
    *
    * @param classSymbol
    * @param includeBaseClass include base class fields if true, default is false
    * @return
    */
  private def getClassFieldAndTypes(classSymbol: ClassSymbol, includeBaseClass: Boolean = false): List[Var -> Type] = {
    val bodyFieldsAndTypes = classSymbol.body.collectBodyFieldsAndTypes ++
      getTraitFieldAndTypes(classSymbol.body)

    if (includeBaseClass) {
      bodyFieldsAndTypes ++
        typeScope.resolveBaseClass(classSymbol.body)
          .map(getClassFieldAndTypes(_, true))
          .getOrElse(List.empty)
    } else {
      bodyFieldsAndTypes
    }
  }

  def addTypeGenTypeAlias(aliasInfo: TypeAliasSymbol): Unit = {
    val aliasName = aliasInfo.lexicalName
    val mlType = aliasInfo.body
    // Create a mapping from type var to their friendly name for lookup
    val typegenCtx = TypegenContext(mlType)
    val tsType = toTsType(mlType)(typegenCtx, Some(true))
    // only use non recursive type variables for type parameters
    val typeParams = typegenCtx.typeVarMapping.iterator
      .filter(tup => mlType.freeTypeVariables.contains(tup._1))
      .map { case (_, varName) => SourceCode(varName)}
      .toList

    typegenCode += SourceCode(s"export type $aliasName") ++
      SourceCode.paramList(typeParams) ++ SourceCode.equalSign ++ tsType
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
    val defName = termName.getOrElse("res")

    // Create a mapping from type var to their friendly name for lookup
    val typegenCtx = TypegenContext(mlType)
    val tsType = toTsType(mlType)(typegenCtx, Some(true))
    // only use non recursive type variables for type parameters
    val typeParams = typegenCtx.typeVarMapping.iterator
      .filter(tup => mlType.freeTypeVariables.contains(tup._1))
      .map { case (_, varName) => SourceCode(varName) }
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
    * @param funcArg
    *   true if Tuple type is the lhs of a function. Used to translate tuples as multi-parameter functions
    * @param typePrecedence
    *   type precedence of an ml type when translating to ts. Decides where extra parenthesis gets placed
    * @param typegenCtx
    *   type generation context for allocating new names
    * @param pol
    *   polarity of type
    * @return
    */
  private def toTsType(mlType: Type, funcArg: Boolean = false, typePrecedence: Int = 0)(implicit
      typegenCtx: TypegenContext,
      pol: Option[Boolean],
  ): SourceCode = {
    mlType match {
      // these types do not mutate typegen context
      case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
        SourceCode("boolean")
      case u@Union(lhs, rhs) =>
        val unionCode = SourceCode.sepBy(
          List(toTsType(lhs, funcArg, this.typePrecedence(u)), toTsType(rhs, funcArg, this.typePrecedence(u))),
          SourceCode.separator
        )
        // a union has lower precedence than an intersection
        if (this.typePrecedence(u) < typePrecedence)
          unionCode.parenthesized
        else
          unionCode
      case i@Inter(lhs, rhs) =>
        SourceCode.sepBy(
          List(toTsType(lhs, funcArg, this.typePrecedence(i)), toTsType(rhs, funcArg, this.typePrecedence(i))),
          SourceCode.ampersand
        )
      case Record(fields) =>
        // ts can only handle fields that have only out type or the same in out types
        if (fields.iterator
          .map(field => field._2.in.map(in => in === field._2.out).getOrElse(true))
          .exists(!_))
            throw CodeGenError("Cannot convert mutable record field with different in out types to typescript")

        SourceCode.recordWithEntries(
          fields.map(entry => 
            if (entry._2.in.isDefined)
              (SourceCode(entry._1.name), toTsType(entry._2.out))
            else
              (SourceCode(s"readonly ${entry._1.name}"), toTsType(entry._2.out))
        ))
      case Tuple(fields) =>
        // ts can only handle fields that have only out type or the same in out types
        if (fields.iterator
          .map(field => field._2.in.map(in => in === field._2.out).getOrElse(true))
          .exists(!_))
            throw CodeGenError("Cannot convert mutable tuple field with different in out types to typescript")

        // tuple that is a function argument becomes
        // multi-parameter argument list
        // ! Note: No equivalent to readonly fields for tuples
        if (funcArg) {
          val argList = fields
            .map{ case field =>
              val arg = typegenCtx.termScope.declareRuntimeSymbol("arg")
              val argType = toTsType(field._2.out)
              SourceCode(s"$arg: ") ++ argType
            }
          SourceCode.sepBy(argList).parenthesized
        }
        // regular tuple becomes fixed length array
        else {
          val tupleArrayCode = SourceCode.horizontalArray(fields.map(field => toTsType(field._2.out)))
          // don't add a readonly if all fields in the tuple are mutable
          // this is because readonly is a weak constraint and can easily
          // be upcasted to non-readonly
          if (fields.iterator.map(_._1.isDefined).forall(identity)) {
            tupleArrayCode
          } else {
            SourceCode("readonly ") ++ tupleArrayCode
          }
        }
      case Top            => SourceCode("unknown")
      case Bot            => SourceCode("never")
      case TypeName(name) => SourceCode(name)
      case Literal(IntLit(n)) =>
        SourceCode(n.toString + (if (JSBackend isSafeInteger n) "" else "n"))
      case Literal(DecLit(n)) => SourceCode(n.toString)
      case Literal(StrLit(s)) => SourceCode(JSLit.makeStringLiteral(s))
      case Literal(UnitLit(b)) => SourceCode(if (b) "undefined" else "null")

      // these types may mutate typegen context by argCounter, or
      // by creating new type aliases
      case f@Function(lhs, rhs) =>
        // flip polarity for input type of function
        // lhs translates to the complete argument list
        // method definition only affects source code representation of top level function
        val lhsTypeSource = toTypegenFunctionLhs(lhs, true)(typegenCtx, pol.map(!_))
        val rhsTypeSource = toTsType(rhs)
        val funcSourceCode = lhsTypeSource ++ SourceCode.fatArrow ++ rhsTypeSource
        // if part of a higher precedence binary operator
        // in this case only Inter and Union is possible
        // parenthesize to maintain correct precedence
        if (this.typePrecedence(f) < typePrecedence) {
          funcSourceCode.parenthesized
        } else {
          funcSourceCode
        }
      // a recursive type is aliased as a self referencing type
      case r@Recursive(uv, body) =>
        // allocate the clash-free name for uv in typegen scope
        // update mapping from type variables to
        val uvName = typegenCtx.typeVarMapping
          .getOrElse(uv,
            throw CodeGenError(s"Did not find mapping for type variable $uv. Unable to generated ts type.")
          )
        val typeVarMapping = typegenCtx.typeVarMapping
        // create new type gen context and recalculate rec var and
        // non-rec var for current type
        val nestedTypegenCtx = TypegenContext(mlType, typeVarMapping)

        // recursive type does not have any other type variables
        // (except itself)
        if (mlType.freeTypeVariables.size === 0) {
          typeScope.declareTypeAlias(uvName, List.empty, r)
          val bodyType = toTsType(body)(typegenCtx, pol)
          typegenCode += (SourceCode(s"export type $uvName") ++
            SourceCode.equalSign ++ bodyType)
          SourceCode(uvName)
        }
        // recursive type has other type variables
        // so now it is an applied type
        else {
          val uvTypeParams = typeVarMapping.iterator
            .filter(tup => mlType.freeTypeVariables.contains(tup._1) &&
              // recursive type variable from outer scope have been converted
              // to type aliases. They do not need to be part of type parameters.
              // filter for type vars that are not declared as type aliases in type scope
              typeVarMapping.get(tup._1).flatMap(varName => typeScope.getTypeAliasSymbol(varName)).isEmpty
            )
            .map(_._2)
            .toList
          // declare type alias to record that this type var has been aliased
          typeScope.declareTypeAlias(uvName, uvTypeParams, body)
          val uvAppliedName = SourceCode(uvName) ++ SourceCode.paramList(uvTypeParams.map(SourceCode(_)))
          val bodyType = toTsType(body)(nestedTypegenCtx, pol)
          typegenCode += (SourceCode(s"export type $uvAppliedName") ++
            SourceCode.equalSign ++ bodyType)
          uvAppliedName
        }
      case AppliedType(base, targs) =>
        if (targs.length =/= 0) {
          SourceCode(base.name) ++ SourceCode.openAngleBracket ++
            SourceCode.sepBy(targs.map(toTsType(_)(typegenCtx, None))) ++ SourceCode.closeAngleBracket
        } else {
          // no type arguments required then print without brackets
          SourceCode(base.name)
        }
      // Neg requires creating a parameterized type alias to hold the negated definition
      case Neg(base) =>
        // Negative type only works in positions of positive polarity
        if (pol === Some(false)) {
          throw CodeGenError(
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
        typegenCtx.typeVarMapping += ((TypeVar(Right(typeParam), None), typeParam))

        val baseType = toTsType(base)
        SourceCode(s"Neg<$baseType, $typeParam>")
      case Rem(base, names) =>
        SourceCode("Omit") ++
          SourceCode.openAngleBracket ++ toTsType(base) ++ SourceCode.commaSpace ++
          SourceCode.sepBy(names.map(name => SourceCode(s"\"${name.name}\"")), SourceCode.separator) ++
          SourceCode.closeAngleBracket
      case Bounds(lb, ub) =>
        pol match {
          // positive polarity takes upper bound
          case Some(true) => toTsType(ub)
          // negative polarity takes lower bound
          case Some(false) => toTsType(lb)
          // TODO: Yet to handle invariant types
          case None =>
            throw CodeGenError(s"Cannot generate type for invariant type $mlType")
        }
      case WithExtension(base, rcd) =>
        toTsType(Inter(Rem(base, rcd.fields.map(tup => tup._1)), rcd))
      // get clash free name for type variable
      case t @ TypeVar(_, _) =>
        val tvarName = typegenCtx.typeVarMapping.getOrElse(t,
          throw CodeGenError(s"Did not find mapping for type variable $t. Unable to generated ts type."))

        // return type alias form if it exists
        typeScope.getTypeAliasSymbol(tvarName).map { taliasInfo =>
          SourceCode(taliasInfo.lexicalName) ++ SourceCode.paramList(taliasInfo.params.map(SourceCode(_)))
        }.getOrElse(SourceCode(tvarName))
      case Constrained(base, where) =>
        throw CodeGenError(s"Cannot generate type for `where` clause $where")
      case _: Splice | _: TypeTag =>
        throw CodeGenError(s"Cannot yet generate type for splices")
    }
  }

  /**
    * Decides the precendence of the mltype when translating to typescript
    *
    * @param mlType
    * @return
    */
  private def typePrecedence(mlType: Type): Int = mlType match {
    case _: Inter => 2
    case _: Union => 1
    case _ => 0
  }
}
