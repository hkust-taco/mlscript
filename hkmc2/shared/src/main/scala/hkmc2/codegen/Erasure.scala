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

  private val declarations = new SourceDeclarations(root)
  // A spread copies the stored value without conversion. The declaration and its writable copies
  // therefore need one representation, although resolution tracks assignments to each field separately.
  private lazy val copiesByDeclaration = declarations.copiedFields.toList.groupBy(_.root)
  private lazy val sourceDefinitions = declarations.statements.collect { case td: TermDefinition => td }.toList.distinctBy(_.tsym)
  private lazy val overrideChecks = new OverrideChecks(sourceDefinitions)

  /** Whether erasure encountered errors, including ones diagnosed in inherited signatures.
    * Signatures are initialized even on failure for later diagnostics, but the program must not
    * be lowered with those recovery representations.
    */
  def hasErrors: Bool = reporter.hasErrors

  /** Checks that lowering uses the same source root whose signatures this instance initialized. */
  def requireCompleted(statement: Statement): Unit =
    assert(root is statement, "Lowering requires completed erasure of this program")

  /** The representation an observation contributes to its slot, or `N` when it places no constraint.
    * A fixed override contributes the result representation its callers receive.
    */
  private def valueType(input: TermShape | TermDefinition): Opt[ErasedValueType] = input match
    case td: TermDefinition =>
      if td.tsym.isErasureReady then S(td.tsym.sourceDeclaredResultType.getOrElse(ErasedType.Unknown))
      else wrappedResult(td, declaredResultType(td)).callType
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
    case tuple: TupleShape => S(if tuple.collection.isEmpty then ErasedType.Array else ErasedType.Unknown)
    case view: IntersectionView =>
      S(ErasedType.Intersection(view.values.map(value => valueType(value).getOrElse(ErasedType.Nothing))))
    case _: (RecordShape | RecordTypeShape | DynShape | UnknownValueShape | OpaqueTypeShape | RigidTypeShape | ErrShape) =>
      S(ErasedType.Unknown)
    case _: InstanceShape =>
      softAssert(false, "Erasure inputs must interpret contextual instance types before completion")
      S(ErasedType.Unknown)
    case _: NamespaceProbe =>
      lastWords("Erasure inputs must filter namespace probes before completion")

  private def nominalType(definition: ClassLikeDef): ErasedValueType = definition.sym match
    case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
    case _ => ErasedType.Unknown

  /** The observations that constrain a slot. Erasure checks parameters before results, so an
    * override whose parameters have no representation cannot cause a second error at its base.
    */
  private def observations(symbol: ResolvedValues.InputSlot): Iterator[TermShape | TermDefinition] =
    if !config.language.useNewResolution then Iterator.empty
    else
      val inputs = summon[State].newResolverState.resolvedValues
      // A diamond contributes each declaration once; an erroneous cycle must also terminate.
      def family[A](root: A)(children: A => Iterator[A]): Iterator[A] =
        val seen = mutable.Set(root)
        def descendants(parent: A): Iterator[A] = children(parent).filter(seen.add).flatMap: child =>
          Iterator.single(child) ++ descendants(child)
        descendants(root)
      val related: Iterator[TermShape | TermDefinition] = symbol match
        case field: RecordFieldSymbol =>
          copiesByDeclaration.getOrElse(field, Nil).iterator.flatMap(inputs.observations)
        case base: VarSymbol if overrideChecks.overridingParameters.contains(base) =>
          family(base)(p => overrideChecks.overridingParameters.getOrElse(p, Nil).iterator.filter(inputs.isPrepared))
            .flatMap(inputs.observations)
        case base: TermSymbol if overrideChecks.overridingMembers.contains(base) =>
          // A constructor parameter fixes field storage. Async and generator callers receive the
          // wrapper, while observations of their bodies describe the payload.
          def inferred(td: TermDefinition): Bool = td.sign.isEmpty && !td.tsym.decl.exists(_.isInstanceOf[Param])
            && td.resultWrapperAnnotation.isEmpty && inputs.isPrepared(td.tsym)
          base.defn.iterator.flatMap(td => family(td)(parent =>
            if inferred(parent) then overrideChecks.overridingMembers.getOrElse(parent.tsym, Nil).iterator else Iterator.empty
          )).filter(td => !td.isErroneous && parameterError(td.params).isEmpty).flatMap: td =>
            if inferred(td) then inputs.observations(td.tsym) else Iterator.single(td)
        case _ => Iterator.empty
      inputs.observations(symbol) ++ related

  private def inferredType(symbol: ResolvedValues.InputSlot): Opt[ErasedValueType] =
    joined(observations(symbol).flatMap(valueType).toList)

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
        case Intersection(left, right) :: Nil => ErasedType.Intersection(erase(left, next) :: erase(right, next) :: Nil)
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
  private def externalInputOrigin(symbol: ResolvedValues.InputSlot): Opt[UnknownValueShape] =
    val inputs = summon[State].newResolverState.resolvedValues
    if !config.language.useNewResolution || !inputs.isPrepared(symbol) then N
    else observations(symbol).collect { case value: TermShape => value.applicationHead._1 }.collectFirst:
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
      inferredSource: Opt[ResolvedValues.InputSlot]): ErasedValueType =
    if !summon[State].runtimeSymbolsInitialized then tpe
    else tpe.canonicalize match
      case incompatible @ ErasedType.Incompatible(lhs, rhs) if !incompatible.reported =>
        val origin =
          if lhs == ErasedType.Unknown || rhs == ErasedType.Unknown then inferredSource.flatMap(externalInputOrigin)
          else N
        val notes = origin.toList.flatMap(_.diagnostic(
          msg"The exposed interface admits values of unknown representation unless a type annotation restricts them."))
        raise(ErrorReport(
          msg"Types '${lhs.describe}' and '${rhs.describe}' have no common representation" -> loc :: notes,
          source = Diagnostic.Source.Compilation))
        ErasedType.Incompatible(lhs, rhs)(reported = true)
      case incompatible: ErasedType.Incompatible =>
        reporter.markFailed()
        incompatible
      case _ => tpe

  /** The already-diagnosed representation error carried by a slot, if any. */
  private def representationError(tpe: Opt[ErasedValueType]): Opt[ErasedType.Incompatible] = tpe.collect:
    case incompatible: ErasedType.Incompatible if incompatible.reported => incompatible

  /** A diagnosed parameter error that prevents checking this definition's result, if any.
    * Reuse the error in its result signature so overrides cannot mistake a skipped result for `Unknown`.
    */
  private def parameterError(params: IterableOnce[ParamList]): Opt[ErasedType.Incompatible] =
    params.iterator.flatMap(_.allParams).flatMap(p => representationError(p.sym.erasedType)).nextOption()
  
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

  /** Computes the representation to publish on a member symbol: a value type, a getter result,
    * or a function's parameter lists and result. Parameter symbols must already have their erased
    * types. A function's physical parameter lists are its written ones: arrows in the type of a
    * function without parameter lists, as in `declare fun f: (Int) -> Str`, describe the function
    * value it returns. Unannotated overrides can obtain their result from an inherited member
    * that passed source layout validation in `overrides` and has completed erasure. Other unannotated
    * members use the result values resolution has collected from their implementations.
    * Diagnosed parameter errors suppress result checking. The result signature retains the error
    * marker, as it does for an unrepresentable result, so overrides inherit it without another diagnostic.
    */
  private def erasedDefinitionSignature(td: TermDefinition, overrides: OverrideChecks): Opt[ErasedValueType | ErasedCallableSignature] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
    val resultType = parameterError(td.params) match
      case S(error) =>
        reporter.markFailed()
        S(error)
      case N =>
        val declaredResult = declaredResultType(td)
        val specified = declaredResult.orElse:
          // A wrapped definition inherits no payload type from its base's callable result.
          if config.language.useNewResolution && td.resultWrapperAnnotation.nonEmpty then N
          else overrides.validatedBases(td.tsym).filter(_.isErasureReady).flatMap(_.sourceDeclaredResultType).nextOption()
        specified.orElse(inferredType(td.tsym)).map:
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
    def checkConstruction(term: Term, cls: ClassDef): Unit =
      if Inheritance.hasModifier(cls, syntax.Keyword.`abstract`) then
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
    // Use the traversed definitions: handler declarations omit the resumption parameter list here.
    overrideChecks.checkExposedSignatures()
    val inheritedParams = overrideChecks.inheritedParameters
    val parameterSymbols = parameters.iterator.map(_.sym).toSet
    /** Initializes a parameter's representation from its annotation or the joined representations
      * of its inherited counterparts. A rest parameter with neither gets `Array`; an ordinary
      * parameter with neither takes the observed inputs to its shared slot. Recursion initializes local inherited
      * parameters first, while `visiting` breaks inheritance cycles; pending inherited parameters
      * contribute `Unknown`. Making a required inherited parameter optional also admits its null default.
      */
    def eraseParameter(p: Param, visiting: Set[VarSymbol]): Unit =
      if !p.sym.isErasureReady && !visiting(p.sym) then
        val declared = declaredParameterType(p)
        val erased = declared.orElse:
          inheritedParams.get(p.sym) match
            case S(inherited) =>
              // Imported parameters are already erased; erroneous inheritance cycles can leave a
              // local parameter pending. Do not read it or initialize a symbol twice on such a cycle.
              inherited.foreach: param =>
                if parameterSymbols(param.sym) then eraseParameter(param, visiting + p.sym)
              val types = inherited.map: param =>
                if param.sym.isErasureReady then param.sym.erasedType.getOrElse(ErasedType.Unknown) else ErasedType.Unknown
              // Making a required slot optional additionally admits null on direct subclass calls.
              // Its inherited argument channel is unchanged for calls through the base interface.
              val defaults = if p.flags.opt && inherited.exists(!_.flags.opt) then ErasedType.Unknown :: Nil else Nil
              S(ErasedType.Union.mk(types ::: defaults))
            // Rest binding constructs an Array, including when lowering slices off trailing
            // arguments. Use that representation unless a declared or inherited type supplies one.
            case N => Option.when(restParameters(p.sym))(ErasedType.Array).orElse(inferredType(p.sym))
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
        if sym.needsErasure then sym.initializeErasure:
          // Only an unannotated mutable field needs a separate type for the values assigned to it.
          // A declared type, including its reported error, is shared with the constructor parameter.
          if p.flags.mut && p.sign.isEmpty && !p.modulefulness.isModuleful && representationError(p.sym.erasedType).isEmpty
          then inferredType(sym).map(representable(_, p.toLoc, S(sym)))
          else p.sym.erasedType
    // Constructor companions have no source body. Their physical argument lists
    // are the class's lists, and a saturated call always produces its instance.
    statements.foreach:
      // Code generation and the InvalML typer can each erase the same elaborated tree.
      case lam: Lam if !lam.resultSlot.isErasureReady =>
        val slot = lam.resultSlot
        slot.erasedType = parameterError(Iterator.single(lam.params)).orElse:
          inferredType(slot).map(representable(_, lam.body.toLoc, S(slot)))
      case asc: Asc if !asc.isErasureReady =>
        asc.erasedType = eraseSignature(asc.ty).map(representable(_, asc.ty.toLoc, N))
      case cls: ClassLikeDef => cls.ctorSym.foreach: symbol =>
        if symbol.needsErasure then symbol.initializeErasure:
          if config.language.useNewResolution then S(ErasedFuncSignature.Signature(
            (cls.paramsOpt.toList ::: cls.auxParams).map(LoweredParamList.fixedPrefix(_).map(_.sym.erasedType)),
            ErasedResult.Direct(S(nominalType(cls)))))
          else N
      case _ => ()
    // Erase inherited results before their overrides, guarding against erroneous inheritance cycles.
    val definitionsBySymbol = sourceDefinitions.map(td => td.tsym -> td).toMap
    /** Publishes a declaration's erased signature after initializing its local inherited members,
      * so an unannotated override can inherit their result representation. Imported members already
      * have erased signatures. `visiting` breaks erroneous inheritance cycles; signature computation
      * only consults inherited results whose members have completed erasure.
      */
    def eraseDefinition(td: TermDefinition, visiting: Set[TermSymbol]): Unit =
      if td.tsym.needsErasure && !visiting(td.tsym) then
        td.tsym.overriddenMembers.flatMap(definitionsBySymbol.get).foreach(eraseDefinition(_, visiting + td.tsym))
        // Definitions rejected before erasure still need initialized signatures for diagnostic recovery.
        td.tsym.initializeErasure:
          if td.isErroneous then N else erasedDefinitionSignature(td, overrideChecks)
    sourceDefinitions.foreach(eraseDefinition(_, Set.empty))
    def variableType(sym: ResolvedValues.InputSymbol): Opt[ErasedValueType] =
      inferredType(sym).map(representable(_, sym.toLoc, S(sym)))
    declarations.variables.foreach:
      case sym: VarSymbol if !sym.isErasureReady => sym.erasedType = variableType(sym)
      case sym: TermSymbol if sym.needsErasure => sym.initializeErasure(variableType(sym))
      // A temporary's erased type is populated at most once (see TempSymbol); without inferred inputs, it stays
      // unknown, as it was before erasure.
      case sym: TempSymbol if sym.erasedType.isEmpty => variableType(sym).foreach(tpe => sym.erasedType = S(tpe))
      case _ => ()
    // Compare signatures only after every definition has completed erasure.
    overrideChecks.checkSignatures()
