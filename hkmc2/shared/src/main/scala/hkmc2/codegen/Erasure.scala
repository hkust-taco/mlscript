package hkmc2
package codegen

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import semantics.Term.*
import hkmc2.Message.MessageContext

/** Computes the runtime representations and nominal class hierarchy that lowering needs from
  * resolved source declarations. Each instance processes one program or prelude, initializes its
  * symbols' erased signatures, and checks override compatibility during construction. Lowering
  * requires the instance constructed for its program, so it can read those completed signatures.
  *
  * Inferred representations bind their slots as declared ones do: lowering rejects unrelated
  * values and slots whose observed values have no common representation.
  */
final class Erasure(root: Statement, report: Raise)(using Config, Ctx, State):
  private given Erasure = this
  private given reporter: Diagnostic.Reporter = new Diagnostic.Reporter(report)
  private val valueTypes = mutable.Map.empty[TermShape, Opt[ErasedValueType]]

  /** Whether erasure encountered errors, including ones diagnosed in inherited signatures.
    * Signatures are initialized even on failure for later diagnostics, but the program must not
    * be lowered with those recovery representations.
    */
  def hasErrors: Bool = reporter.hasErrors

  /** Checks that lowering uses the same source root whose signatures this instance initialized. */
  def requireCompleted(statement: Statement): Unit =
    assert(root is statement, "Lowering requires completed erasure of this program")

  private def valueType(shape: TermShape): Opt[ErasedValueType] = valueTypes.getOrElseUpdate(shape, shape match
    case MarkedShape(value, _) => valueType(value)
    case ContextualShape(value, _) => valueType(value)
    case SpecializedShape(value, _, _) => valueType(value)
    case nominal: NominalInstanceView => S(nominalType(nominal.defn))
    case base: BaseShape => S(nominalType(base.defn))
    case construction: NewShape => S(
      if construction.isSaturated then ErasedType.ValueLike(S(false), construction.cls)
      else ErasedType.Function(S(false)))
    case application: AppShape => S(
      if !application.isSaturated then ErasedType.Function(S(false))
      else application.applicationHead._1 match
        case definition: DefnShape => definition.clsDef.fold[ErasedValueType](ErasedType.Unknown)(nominalType)
        case _ => ErasedType.Unknown)
    case definition: DefnShape => S(definition.defn match
      case module: ModuleOrObjectDef => nominalType(module)
      case _: TermDefinition => ErasedType.Function(S(false))
      // A class value denotes the constructor object, not an instance of that class.
      case _ => ErasedType.Unknown)
    case intro: IntroShape => intro.trm match
      case _: Lam => S(ErasedType.Function(S(false)))
      case UnitVal() => S(ErasedType.Unit)
      case Lit(_: syntax.Tree.IntLit) => S(ErasedType.Int)
      case Lit(_: syntax.Tree.DecLit) => S(ErasedType.Num)
      case Lit(_: syntax.Tree.StrLit) => S(ErasedType.Str)
      case Lit(_: syntax.Tree.BoolLit) => S(ErasedType.Bool)
      // Undefined places no constraint on the slot's representation. An undefined-only
      // slot still receives the ordinary default representation and keeps it across consumers.
      case Lit(syntax.Tree.UnitLit(false)) => N
      case Lit(syntax.Tree.UnitLit(true)) => S(ErasedType.Unknown)
    case _: CallableTypeShape => S(ErasedType.Function(S(false)))
    case _: TupleShape => S(ErasedType.Array)
    // An intersection describes one value through several interfaces, not alternative values.
    // Keep the same conservative representation as an intersection in a declared signature.
    case _: IntersectionView => S(ErasedType.Unknown)
    case _: (RecordShape | RecordTypeShape | DynShape | UnknownValueShape | OpaqueTypeShape | RigidTypeShape | ErrShape) =>
      S(ErasedType.Unknown)
    case _: InstanceShape =>
      softAssert(false, "Erasure inputs must interpret contextual instance types before completion")
      S(ErasedType.Unknown)
    case _: NamespaceProbe =>
      lastWords("Erasure inputs must filter namespace probes before completion")
  )

  private def nominalType(definition: ClassLikeDef): ErasedValueType = definition.sym match
    case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
    case _ => ErasedType.Unknown

  private def inferredType(symbol: ErasureInputs.InputSymbol): Opt[ErasedValueType] =
    if !config.language.useNewResolution then N
    else joined(summon[State].newResolverState.erasureInputs.shapes(symbol).flatMap(valueType))

  /** The representation of a slot that holds values of each of `types`, or `N` when there are none. */
  private def joined(types: Ls[ErasedValueType]): Opt[ErasedValueType] = types match
    case Nil => N
    // Unknown is a real candidate, not the identity of this join: in particular,
    // combining it with an unboxed primitive must preserve incompatibility.
    case _ => S(ErasedType.Union.mk(types))

  /** Read a delayed type in the context that completed erasure. Cloning can then
    * rename its symbol without retaining the entire cloning substitution in a thunk.
    */
  def typeSymbol(tpe: ErasedType.ValueLike): TypeSymbol = tpe.sym

  /** Erase an interpretation registered during elaboration, without installing new listeners. */
  private def erase(resolution: TypeResolution, seen: Set[TypeResolution]): ErasedValueType =
    import TypeShape.*
    if seen(resolution) || resolution.hasErrors then ErasedType.Unknown
    else
      val next = seen + resolution
      resolution.shapes.toList match
        case Nominal(defn) :: Nil => defn.sym match
          case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
          case _ => ErasedType.Unknown
        case Alias(_, rhs) :: Nil => rhs.fold(ErasedType.Unknown)(erase(_, next))
        case Union(left, right) :: Nil => ErasedType.union(erase(left, next), erase(right, next))
        case Reference(base, _, _, _) :: Nil => erase(base, next)
        case Applied(base, _) :: Nil => erase(base, next)
        case Function(_, _) :: Nil => ErasedType.Function(S(false))
        case Polymorphic(_, _, body) :: Nil => erase(body, next)
        case Unit :: Nil => ErasedType.Unit
        case Bottom :: Nil => ErasedType.Nothing
        case _ => ErasedType.Unknown

  /** Computes the runtime value representation denoted by a source type signature. With the new
    * resolver, elaboration must have registered the term's type interpretation and resolution must
    * have completed; an unknown representation yields `S(Unknown)`. The legacy resolver reads the
    * resolved syntax and can return `N` when it cannot derive a representation.
    */
  private def eraseSignature(sign: Term): Opt[ErasedValueType] =
    if config.language.useNewResolution then
      assert(sign.typeInterpretation.isDefined, "Signature was not registered during elaboration")
      S(erase(sign.typeInterpretation.get, Set.empty))
    else ErasedType.eraseSign(sign)

  /** An external input that contributed to this slot's inferred representation, if any.
    * Its provenance identifies the exposed interface even when the value flowed into a private helper.
    */
  private def externalInputOrigin(symbol: ErasureInputs.InputSymbol): Opt[UnknownValueShape] =
    val inputs = summon[State].newResolverState.erasureInputs
    if !config.language.useNewResolution || !inputs.isPrepared(symbol) then N
    else inputs.shapes(symbol).iterator.map(_.applicationHead._1).collectFirst:
      case unknown: UnknownValueShape if unknown.fromPublicInterface => unknown

  /** Rejects a slot type without a runtime representation, such as `Int32 | Str`:
    * an unboxed primitive shares no representation with any other type, so no value of such
    * a slot can be stored or passed. Reporting it once at the declaration replaces the errors
    * that each coercion into or out of the slot would report. Class headers are published
    * before declarations are erased, so canonicalizing here sees complete parent chains.
    * Rejected types return a canonical `Incompatible` marker, including inherited, already-reported conflicts.
    * `inferredSource` identifies observations used to infer the type; declared types have no such source.
    *
    * The Prelude and Runtime are erased before the runtime's symbols exist, and
    * canonicalizing a type such as `Unit` requires them. Those library declarations are not
    * checked; every other compilation unit is erased after the runtime is loaded.
    */
  private def representable(tpe: ErasedValueType, loc: Opt[Loc],
      inferredSource: Opt[ErasureInputs.InputSymbol]): ErasedValueType =
    if !summon[State].runtimeSymbolsInitialized then tpe
    else tpe.canonicalize match
      case incompatible @ ErasedType.Incompatible(lhs, rhs) if !incompatible.reported =>
        val origin =
          if lhs == ErasedType.Unknown || rhs == ErasedType.Unknown then inferredSource.flatMap(externalInputOrigin)
          else N
        val notes = origin.toList.flatMap(_.diagnostic(
          msg"The exposed interface admits values of unknown representation."))
        raise(ErrorReport(
          msg"Types '${lhs.describe}' and '${rhs.describe}' have no common representation" -> loc :: notes,
          source = Diagnostic.Source.Compilation))
        ErasedType.Incompatible(lhs, rhs)(reported = true)
      case incompatible: ErasedType.Incompatible =>
        reporter.markFailed()
        incompatible
      case _ => tpe

  /** The already-diagnosed representation error carried by a slot, if any. */
  private[codegen] def representationError(tpe: Opt[ErasedValueType]): Opt[ErasedType.Incompatible] = tpe.collect:
    case incompatible: ErasedType.Incompatible if incompatible.reported => incompatible

  /** A diagnosed parameter error that prevents checking this definition's result, if any.
    * Reuse the error in its result signature so overrides cannot mistake a skipped result for `Unknown`.
    */
  private def parameterError(td: TermDefinition): Opt[ErasedType.Incompatible] =
    td.params.iterator.flatMap(_.allParams).flatMap(p => representationError(p.sym.erasedType)).nextOption()
  
  private def declaredType(sign: Opt[Term], modulefulness: Modulefulness): Opt[ErasedValueType] =
    modulefulness.msym match
      case S(msym) => S(ErasedType.ValueLike(rsc = S(false), msym))
      case N => sign.flatMap(eraseSignature)

  /** The representation a parameter declares through an inline annotation, a module requirement,
    * or a separate function signature. Parameters without a declared interface return `N`.
    */
  private def declaredParameterType(parameter: Param): Opt[ErasedValueType] =
    declaredType(parameter.sign, parameter.modulefulness).orElse:
      if !config.language.useNewResolution then N
      else
        val resolver = parameter.sym.getState.newResolverState
        if resolver.signatureParameters.get(parameter.sym)(using resolver.context).isEmpty then N
        else
          // In `fun f: (Int) -> Int; fun f(x) = ...`, x has no inline annotation.
          // The resolver records the signature's Int in x's observed shapes and excludes argument types
          // supplied by callers. Thus inferredType reads the separately declared representation here.
          // Treat it as declared so inherited types and calls to overrides cannot change it.
          // If the signature supplies no value shapes, S(Unknown) still prevents fallback to family inference.
          S(inferredType(parameter.sym).getOrElse(ErasedType.Unknown))

  /** The result representation that `td` declares, with a result annotation or with a separate full
    * signature such as `fun f: (Int) -> Int`, whose arrows describe the written parameter lists.
    */
  private def declaredResultType(td: TermDefinition): Opt[ErasedValueType] =
    def fullResult(res: TypeResolution, count: Int, seen: Set[TypeResolution]): ErasedValueType =
      if seen(res) then ErasedType.Unknown
      else if count == 0 then erase(res, Set.empty)
      else res.shapes.toList match
        case TypeShape.Alias(_, S(rhs)) :: Nil => fullResult(rhs, count, seen + res)
        case TypeShape.Reference(base, _, _, _) :: Nil => fullResult(base, count, seen + res)
        case TypeShape.Applied(base, _) :: Nil => fullResult(base, count, seen + res)
        case TypeShape.Polymorphic(_, _, body) :: Nil => fullResult(body, count, seen + res)
        case TypeShape.Function(_, ret) :: Nil => fullResult(ret, count - 1, seen + res)
        case _ => ErasedType.Unknown
    if config.language.useNewResolution && td.sign.nonEmpty && (td.k is syntax.Fun)
        && !td.flags.hasResultAnnotation && td.params.nonEmpty && !td.modulefulness.isModuleful
    then S(fullResult(td.sign.get.typeInterpretation.get, td.params.length, Set.empty))
    else declaredType(td.resultSignature, td.modulefulness)

  /** The result of `td`, whose body produces values represented as `bodyType`. The body of an async or
    * generator function produces a payload, while its callers receive the wrapper object.
    * Resolution gives calls of such functions the same wrapper shapes.
    */
  private def wrappedResult(td: TermDefinition, bodyType: Opt[ErasedValueType]): ErasedResult[ErasedValueType] =
    if !config.language.useNewResolution then ErasedResult.Direct(bodyType)
    else td.resultWrapperAnnotation match
      case S(_: Annot.Async) => ErasedResult.Async(bodyType)
      case S(_: Annot.Generator) => ErasedResult.Generator(bodyType)
      case N => ErasedResult.Direct(bodyType)

  /** The representations of the values that calls of `td` return, for a member `td` that neither declares
    * nor inherits a result: those of the values that resolution observed its body to produce, and those that
    * the members overriding it contribute. A call resolved to `td` can dispatch to any of these members,
    * and the unannotated ones inherit the result representation of `td`.
    *
    * An overriding member contributes what its own callers receive: its declared result or its wrapper
    * object, and otherwise its own observed values with the contributions of the members overriding it.
    * `visiting` stops at inheritance cycles. The members of `handlerMembers` contribute nothing: the body of
    * a handler member produces the result of the handled expression, whereas a call of the effect member
    * it implements returns the value that the handler resumes with.
    */
  private def observedResultTypes(td: TermDefinition, overrides: OverrideChecks,
      handlerMembers: Set[TermSymbol], visiting: Set[TermSymbol]): Ls[ErasedValueType] =
    inferredType(td.tsym).toList ::: overrides.validatedOverriders.getOrElse(td.tsym, Nil).flatMap: overriding =>
      if overriding.isErroneous || visiting(overriding.tsym) || handlerMembers(overriding.tsym)
          || parameterError(overriding).isDefined then Nil
      // Erasure assigns inherited signatures before their overrides. A signature assigned earlier belongs
      // to a declaration that erasure does not infer, whose published result is all that is known.
      else if overriding.tsym.isErased then overriding.tsym.sourceDeclaredResultType.getOrElse(ErasedType.Unknown) :: Nil
      else if overriding.resultWrapperAnnotation.nonEmpty then wrappedResult(overriding, N).callType.toList
      else declaredResultType(overriding) match
        case S(declared) => declared :: Nil
        case N => observedResultTypes(overriding, overrides, handlerMembers, visiting + overriding.tsym)

  /** Computes the representation to publish on a member symbol: a value type, a getter result,
    * or a function's parameter lists and result. Parameter symbols must already have their erased
    * types. A function's physical parameter lists are its written ones: arrows in the type of a
    * function without parameter lists, as in `declare fun f: (Int) -> Str`, describe the function
    * value it returns. Unannotated overrides can obtain their result from an inherited member
    * that passed source layout validation in `overrides` and has completed erasure. Other unannotated
    * members take the result representation of their whole override family (see `observedResultTypes`).
    * Diagnosed parameter errors suppress result checking. The result signature retains the error
    * marker, as it does for an unrepresentable result, so overrides inherit it without another diagnostic.
    */
  private def erasedDefinitionSignature(td: TermDefinition, overrides: OverrideChecks,
      handlerMembers: Set[TermSymbol]): Opt[ErasedValueType | ErasedCallableSignature] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
    val resultType = parameterError(td) match
      case S(error) =>
        reporter.markFailed()
        S(error)
      case N =>
        val declaredResult = declaredResultType(td)
        val candidateResultType = declaredResult.orElse:
          // Async/generator bodies produce a payload; inherited callable results describe the wrapper,
          // and the members overriding such a function produce payloads or results of their own.
          if config.language.useNewResolution && td.resultWrapperAnnotation.nonEmpty then inferredType(td.tsym)
          // An ordinary override keeps the first specified inherited result unchanged. Infer a result
          // only when no validated base supplies one, as for a definition with no overrides.
          else overrides.validatedBases.getOrElse(td.tsym, Nil).iterator.filter(_.isErased)
            .flatMap(_.sourceDeclaredResultType).nextOption().orElse:
              // The legacy resolver observes no values, and its unannotated results stay unknown.
              if config.language.useNewResolution
              then joined(observedResultTypes(td, overrides, handlerMembers, Set.single(td.tsym)))
              else N
        candidateResultType.map:
          representable(_, td.resultSignature.orElse(td.sign).flatMap(_.toLoc).orElse(td.tsym.toLoc),
            if declaredResult.isEmpty then S(td.tsym) else N)
    val result = wrappedResult(td, resultType)
    td.k match
      case syntax.Fun =>
        val paramLists = td.params.map(LoweredParamList.fixedPrefix(_).map(_.sym.erasedType))
        // Block-level nullary functions take an implicit empty list and references auto-invoke them.
        // Member getters and global declarations denote their result directly.
        val physicalParamLists =
          if paramLists.isEmpty && td.owner.isEmpty && !declared then Nil :: Nil else paramLists
        if physicalParamLists.isEmpty then S(ErasedGetterSignature.Signature(result))
        else S(ErasedFuncSignature.Signature(physicalParamLists, result))
      case _: syntax.Val => resultType
      case syntax.RecordField => if config.language.useNewResolution then resultType else N
      case _ => N

  locally:
    val declarations = new ErasureDeclarations(root)
    val statements = declarations.statements
    val parameters = declarations.parameters.values.toList
    val parentConstructions = mutable.Set.empty[Identity[Statement]]
    def parentHead(term: Term): Unit = if parentConstructions.add(Identity(term)) then term match
      // Legacy resolution can expand a parent reference to an implicit constructor call.
      // Follow only the class head; constructions in argument expressions are real allocations.
      case ref: Resolvable if ref.expanded isnt ref => parentHead(ref.expanded)
      case New(cls, _, _) => parentHead(cls)
      case App(lhs, _) => parentHead(lhs)
      case TyApp(lhs, _) => parentHead(lhs)
      case _ => ()
    statements.foreach:
      case cls: ClassLikeDef => cls.ext.foreach(parentHead)
      case _ => ()

    val restParameters = statements.iterator.flatMap:
      case td: TermDefinition => td.params.iterator
      case cls: ClassLikeDef => cls.paramsOpt.iterator ++ cls.auxParams.iterator
      case Lam(ps, _) => Iterator.single(ps)
      case _ => Iterator.empty
    .flatMap(_.variadic.iterator.map(_.param.sym)).toSet

    def parentClasses(parent: New): Ls[ClassLikeDef] =
      (parent.cls.resolvedSym.flatMap(_.asClsOrMod).flatMap(_.defn).toList :::
        ClassValueShape.targetsOf(parent).map(ClassValueShape.definitionOf)).distinct
    def parentClass(parent: New): Opt[ClassLikeDef] = parentClasses(parent) match
      case cls :: Nil => S(cls)
      case _ => N

    // No erased representation is read until every interpretation has been validated and every
    // nominal parent header has been published, including forward and external declarations.
    val validatedTypes = mutable.Set.empty[TypeResolution]
    statements.foreach:
      case term: Term => term.typeInterpretation.foreach(_.validate(validatedTypes))
      case _ => ()
    statements.foreach:
      case cls: ClassLikeDef =>
        cls.ext.foreach: extension =>
          parentClasses(extension).foreach(Inheritance.validateParent(cls, _, extension))
        cls.sym match
          case sym: ClassLikeSymbol if sym.irClassHeader.isEmpty =>
            val parent = cls.ext match
              case N => ClassHeader.Parent.Root
              case S(parent) => parentClass(parent).flatMap(_.sym.asClsOrMod)
                .fold(ClassHeader.Parent.Unknown)(ClassHeader.Parent.Known(_))
            val termCompanion = if cls.hasDeclareModifier.isDefined then N else cls.bsym.asTrm
            sym.irClassHeader = S(ClassHeader(parent, N, termCompanion))
          case _ => ()
      case _ => ()

    // Public members replace inherited runtime keys; private members retain their declaration identity.
    // A subclass cannot implement a private declaration by introducing the same name.
    type ImplementationKey = Either[TermSymbol, MemberKey]
    // Cache effective members so subclasses share the work of checking common ancestors.
    // Definitions are keyed by identity: as case classes, they would otherwise
    // be hashed and compared through their entire bodies on every lookup.
    val effectiveMembers = mutable.Map.empty[Identity[ClassLikeDef], Map[ImplementationKey, TermSymbol]]
    def checkConstruction(term: Term & PossiblyErroneous, cls: ClassDef): Unit =
      if Inheritance.hasModifier(cls, syntax.Keyword.`abstract`) then
        term.isErroneous = true
        raise(ErrorReport(
          msg"Cannot instantiate abstract class '${cls.sym.nme}'" -> term.toLoc ::
            (msg"Abstract class defined here" -> cls.toLoc) :: Nil, source = Diagnostic.Source.Compilation))
    def members(cls: ClassLikeDef, visiting: Set[Identity[ClassLikeDef]]): Map[ImplementationKey, TermSymbol] =
      effectiveMembers.getOrElseUpdate(Identity(cls),
        if visiting(Identity(cls)) then
          raise(ErrorReport(msg"Inheritance cycle involving '${cls.sym.nme}'" -> cls.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
          Map.empty
        else
          val inherited = cls.ext.flatMap(parentClass)
            .fold(Map.empty[ImplementationKey, TermSymbol])(members(_, visiting + Identity(cls)))
          inherited ++ cls.body.members.toList.flatMap: (name, member) =>
            member.asTrm.map: symbol =>
              val key: ImplementationKey = if symbol.isPrivate then Left(symbol) else Right(MemberKey.symbol(member).getOrElse(name))
              key -> symbol
      )
    statements.foreach:
      case td: TermDefinition => Inheritance.validateMember(td)
      case cls: ClassLikeDef if !Inheritance.isExternal(cls) &&
          !Inheritance.hasModifier(cls, syntax.Keyword.`abstract`) =>
        val missing = members(cls, Set.empty).values.toList
          .distinct.filter(_.defn.exists(Inheritance.isAbstract))
          .sortBy(_.nme)
        if missing.nonEmpty then raise(ErrorReport(
          msg"${cls.sym.describeKind.capitalize} '${cls.sym.nme}' has unimplemented members" -> cls.toLoc ::
            missing.map(sym => msg"Member '${sym.nme}' requires an implementation" -> sym.toLoc),
          source = Diagnostic.Source.Compilation))
      case nw: New if nw.rft.isEmpty && !parentConstructions(Identity(nw)) =>
        parentClass(nw).collect { case cls: ClassDef => cls }.foreach(checkConstruction(nw, _))
      case app: App if !parentConstructions(Identity(app)) =>
        // Constructor functions can flow through variables and parameters; their call shapes
        // retain the declaration even when the callee has no single resolved symbol.
        def constructed(event: ShapeEvent): Ls[ClassDef] = event match
          case ActivatedShapeEvent(value, _) => constructed(value)
          case MarkedShape(value, _) => constructed(value)
          case ContextualShape(value, _) => constructed(value)
          case shape: AppShape if shape.src is app => shape.applicationHead._1 match
            case definition: DefnShape => definition.defn match
              case td: TermDefinition => td.tsym match
                case ctor: ClassCtorSymbol => ctor.associatedCls.defn.toList
                case _ => Nil
              case cls: ClassDef => cls :: Nil
              case _ => Nil
            case _ => Nil
          case _ => Nil
        val direct = app.lhs.resolvedSym.toList.flatMap:
          case ctor: ClassCtorSymbol => ctor.associatedCls.defn.toList
          case _ => Nil
        (direct ::: app.shapes.toList.flatMap(constructed)).distinct.foreach(checkConstruction(app, _))
      case _ => ()

    // Establish source argument correspondence before inheriting representations. Equal leading
    // counts alone do not suffice: optional and trailing parameters can redistribute the inputs.
    // Retain the traversed declarations: handlers remove the resumption parameter list from them.
    val observed =
      if config.language.useNewResolution then summon[State].newResolverState.erasureInputs.symbols
      else Nil
    // Observations can refer to earlier worksheet declarations. Reuse their initialized signatures
    // without reporting their override diagnostics again in this program.
    val sourceDefinitions = statements.collect { case td: TermDefinition => td }.toList.distinctBy(_.tsym)
    val definitions = (sourceDefinitions ++ observed.collect {
      case sym: TermSymbol => sym.defn }.flatten).distinctBy(_.tsym)
    val overrideChecks = new OverrideChecks(sourceDefinitions)
    overrideChecks.checkExposedSignatures()
    val inheritedParams = overrideChecks.inheritedParameters
    val parameterSymbols = parameters.iterator.map(_.sym).toSet
    /** The representations of the values that the parameter `p` receives, for a parameter that neither
      * declares nor inherits a representation: those of the values that resolution observed for it, and
      * those observed for the unannotated parameters overriding it, at any depth. Such parameters inherit
      * the representation of `p`, which must therefore admit the arguments of their members' direct calls.
      *
      * Three kinds of overriding parameters keep representations of their own and contribute nothing:
      * - An annotated parameter declares its representation. Arguments flow from the callers of the
      *   overridden member to the overriding one, so the arguments of its member's direct calls never reach `p`.
      * - A rest parameter holds an array of its arguments, whatever their representations (see `eraseParameter`).
      * - A parameter whose representation is already assigned belongs to a declaration that erasure does not
      *   infer: erasure assigns inherited parameters before the parameters overriding them.
      *
      * `visiting` stops at inheritance cycles.
      */
    def observedParameterTypes(p: Param, visiting: Set[VarSymbol]): Ls[ErasedValueType] =
      inferredType(p.sym).toList ::: overrideChecks.overridingParameters.getOrElse(p.sym, Nil).flatMap: overriding =>
        if visiting(overriding.sym) || restParameters(overriding.sym) || overriding.sym.isErased
            || declaredParameterType(overriding).isDefined
        then Nil
        else
          // Making a required slot optional additionally admits null on direct calls of the overriding member.
          val default = if overriding.flags.opt && !p.flags.opt then ErasedType.Unknown :: Nil else Nil
          default ::: observedParameterTypes(overriding, visiting + overriding.sym)
    /** Initializes a parameter's representation from its annotation or the joined representations
      * of its inherited counterparts. A rest parameter with neither gets `Array`; an ordinary
      * parameter with neither takes the representation of its whole override family (see
      * `observedParameterTypes`). Recursion initializes local inherited
      * parameters first, while `visiting` breaks inheritance cycles; pending inherited parameters
      * contribute `Unknown`. Making a required inherited parameter optional also admits its null default.
      */
    def eraseParameter(p: Param, visiting: Set[VarSymbol]): Unit =
      if !p.sym.isErased && !visiting(p.sym) then
        val declared = declaredParameterType(p)
        val erased = declared.orElse:
          inheritedParams.get(p.sym) match
            case S(inherited) =>
              // Imported parameters are already erased; erroneous inheritance cycles can leave a
              // local parameter pending. Do not read it or initialize a symbol twice on such a cycle.
              inherited.foreach: param =>
                if parameterSymbols(param.sym) then eraseParameter(param, visiting + p.sym)
              val types = inherited.map: param =>
                if param.sym.isErased then param.sym.erasedType.getOrElse(ErasedType.Unknown) else ErasedType.Unknown
              // Making a required slot optional additionally admits null on direct subclass calls.
              // Its inherited argument channel is unchanged for calls through the base interface.
              val defaults = if p.flags.opt && inherited.exists(!_.flags.opt) then ErasedType.Unknown :: Nil else Nil
              S(ErasedType.Union.mk(types ::: defaults))
            // Rest binding constructs an Array, including when lowering slices off trailing
            // arguments. Use that representation unless a declared or inherited type supplies one.
            case N => Option.when(restParameters(p.sym))(ErasedType.Array).orElse:
              // The legacy resolver observes no values, and its unannotated parameters stay unknown.
              if config.language.useNewResolution then joined(observedParameterTypes(p, Set.single(p.sym))) else N
        // Inherited parameter types can also join into a type without a representation.
        p.sym.erasedType = erased.map(representable(_, p.sign.flatMap(_.toLoc).orElse(p.toLoc),
          if declared.isEmpty && !inheritedParams.contains(p.sym) then S(p.sym) else N))
    parameters.foreach: p =>
      eraseParameter(p, Set.empty)
      // Public fields have a BlockMemberSymbol; private/auxiliary constructor fields have a TermSymbol.
      // Their source signatures belong to the parameter, not to the synthesized field definition.
      val field = p.fldSym.flatMap:
        case sym: TermSymbol => S(sym)
        case sym: BlockMemberSymbol => sym.tsym
        case _ => N
      field.foreach: sym =>
        if !sym.isErased then sym.initializeErasure:
          // Only an unannotated mutable field needs a separate type for the values assigned to it.
          // A declared type, including its reported error, is shared with the constructor parameter.
          if p.flags.mut && p.sign.isEmpty && !p.modulefulness.isModuleful && representationError(p.sym.erasedType).isEmpty
          then inferredType(sym).map(representable(_, p.toLoc, S(sym)))
          else p.sym.erasedType
    // Constructor companions have no source body. Their physical argument lists
    // are the class's lists, and a saturated call always produces its instance.
    statements.foreach:
      case cls: ClassLikeDef => cls.ctorSym.foreach: symbol =>
        if !symbol.isErased then symbol.initializeErasure:
          if config.language.useNewResolution then S(ErasedFuncSignature.Signature(
            (cls.paramsOpt.toList ::: cls.auxParams).map(LoweredParamList.fixedPrefix(_).map(_.sym.erasedType)),
            ErasedResult.Direct(S(nominalType(cls)))))
          else N
      case _ => ()
    // Erase inherited results before their overrides, guarding against erroneous inheritance cycles.
    val definitionsBySymbol = definitions.map(td => td.tsym -> td).toMap
    val handlerMembers = declarations.handlerMembers.toSet
    /** Publishes a declaration's erased signature after initializing its local inherited members,
      * so an unannotated override can inherit their result representation. Imported members already
      * have erased signatures. `visiting` breaks erroneous inheritance cycles; signature computation
      * only consults inherited results whose members have completed erasure.
      */
    def eraseDefinition(td: TermDefinition, visiting: Set[TermSymbol]): Unit =
      if !td.tsym.isErased && !visiting(td.tsym) then
        td.tsym.overriddenMembers.flatMap(definitionsBySymbol.get).foreach(eraseDefinition(_, visiting + td.tsym))
        // Definitions rejected before erasure still need initialized signatures for diagnostic recovery.
        td.tsym.initializeErasure:
          if td.isErroneous then N else erasedDefinitionSignature(td, overrideChecks, handlerMembers)
    definitions.foreach(eraseDefinition(_, Set.empty))
    def variableType(sym: ErasureInputs.InputSymbol): Opt[ErasedValueType] =
      inferredType(sym).map(representable(_, sym.toLoc, S(sym)))
    declarations.variables.foreach:
      case sym: VarSymbol if !sym.isErased => sym.erasedType = variableType(sym)
      case sym: TermSymbol if !sym.isErased => sym.initializeErasure(variableType(sym))
      // A temporary's erased type is populated at most once (see TempSymbol); without inferred inputs, it stays
      // unknown, as it was before erasure.
      case sym: TempSymbol if sym.erasedType.isEmpty => variableType(sym).foreach(tpe => sym.erasedType = S(tpe))
      case _ => ()
    // Compare signatures only after every definition has completed erasure.
    overrideChecks.checkSignatures()
    statements.foreach:
      case td: TermDefinition => checkExposedMutableField(td)
      case _ => ()

  /** Other compilation units assign values to a mutable field with the representation of its erased type, which
    * therefore must not depend on the values that this compilation unit happens to assign to the field. Interface
    * exposure assigns a value of unknown shape referring to the field itself to the mutable fields reachable from the
    * unit's interface (see InterfaceExposure); such a field must declare its type. Fields that merely receive unknown
    * values from this unit's own exposed parameters do not need to: their representation is already the unknown one.
    * Record fields cannot declare types; their exposed representation is the unknown one.
    */
  private def checkExposedMutableField(td: TermDefinition): Unit =
    // A constructor parameter declares the type of the field it defines.
    val declared = td.tsym.decl match
      case S(p: Param) => p.sign.isDefined || p.modulefulness.isModuleful
      case _ => td.sign.isDefined || td.modulefulness.isModuleful
    val inputs = summon[State].newResolverState.erasureInputs
    if config.language.useNewResolution && (td.k is syntax.MutVal) && !declared && !Inheritance.isExternal(td)
        && inputs.isPrepared(td.tsym) then
      val exposure = inputs.shapes(td.tsym).iterator.map(_.applicationHead._1).collectFirst:
        case unknown: UnknownValueShape if unknown.fromPublicInterface && (unknown.source match
          case ref: MemberRef => ref.sym is td.bsym
          case _ => false) => unknown
      exposure.foreach: unknown =>
        raise(ErrorReport(unknown.provenance.diagnostic(
          msg"Mutable field '${td.tsym.nme}' is exposed to other compilation units, which can assign to it; annotate its type",
          td.tsym.toLoc), source = Diagnostic.Source.Compilation))
