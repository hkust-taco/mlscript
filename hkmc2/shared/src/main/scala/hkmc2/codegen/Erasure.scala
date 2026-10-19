package hkmc2
package codegen

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import semantics.Term.*
import hkmc2.Message.MessageContext

/** The capability to inspect completed resolution. Created only after elaboration/resolution;
  * executable lowering additionally requires this instance's whole-program pass to have finished.
  *
  * The representations this pass infers from resolution's observations are as binding as declared ones:
  * lowering reports a value whose representation is unrelated to its slot's, or a slot whose values have
  * no common representation, as a compilation error (see Runtime Representations in `doc/reference.md`).
  */
final class Erasure private (using Config, Ctx, State)(using Raise):
  private given Erasure = this
  private var completed: Opt[Statement] = N
  private val valueTypes = mutable.Map.empty[TermShape, Opt[ErasedValueType]]
  private val bodyResults = mutable.Map.empty[TermSymbol, Opt[ErasedValueType]]

  def requireCompleted(statement: Statement): Unit =
    assert(completed.exists(_ is statement), "Lowering requires completed erasure of this program")

  /** Async definitions expose a promise and generators an iterator, but their original
    * bodies produce the payload (of the promise, or of the generator's final step).
    * Lowering must coerce explicit and implicit returns before they are wrapped.
    */
  def bodyResultType(td: TermDefinition): Opt[ErasedValueType] =
    bodyResults.getOrElse(td.tsym, td.tsym.declaredResultType)

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
    case _: (RecordShape | RecordTypeShape | DynShape | UnknownValueShape | OpaqueTypeShape | RigidTypeShape | ErrShape) =>
      S(ErasedType.Unknown)
    case _: InstanceShape =>
      softAssert(false, "Erasure inputs must interpret contextual instance types before completion")
      S(ErasedType.Unknown)
  )

  private def nominalType(definition: ClassLikeDef): ErasedValueType = definition.sym match
    case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
    case _ => ErasedType.Unknown

  private def inferredType(symbol: Symbol): Opt[ErasedValueType] =
    if !config.language.useNewResolution then N
    else summon[State].newResolverState.erasureInputs.shapes(symbol).flatMap(valueType) match
      case Nil => N
      // Unknown is a real candidate, not the identity of this join: in particular,
      // combining it with an unboxed primitive must preserve incompatibility.
      case types => S(ErasedType.Union.mk(types))

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
        case _ => ErasedType.Unknown

  private def eraseSignature(sign: Term): Opt[ErasedValueType] =
    if config.language.useNewResolution then
      assert(sign.typeInterpretation.isDefined, "Signature was not registered during elaboration")
      S(erase(sign.typeInterpretation.get, Set.empty))
    else ErasedType.eraseSign(sign)

  private def declaredType(sign: Opt[Term], modulefulness: Modulefulness): Opt[ErasedValueType] =
    modulefulness.msym match
      case S(msym) => S(ErasedType.ValueLike(rsc = S(false), msym))
      case N => sign.flatMap(eraseSignature)

  /** Splits written arrows, retaining an unknown arity when a parameter tuple contains a spread. */
  private def splitSignature(sign: Term): Opt[(Ls[Ls[Opt[ErasedValueType]]], Term)] =
    def paramsOf(lhs: Term): Opt[Ls[Opt[ErasedValueType]]] = lhs match
      case Tup(fields) =>
        val noParams: Opt[Ls[Opt[ErasedValueType]]] = S(Nil)
        fields.foldRight(noParams): (fld, acc) =>
          (fld, acc) match
            case (Fld(_, t, _), S(rest)) => S(eraseSignature(t) :: rest)
            case _ => N
      case single => S(eraseSignature(single) :: Nil)
    sign match
      case Forall(_, _, body) => splitSignature(body)
      case FunTy(lhs, rhs, _) => paramsOf(lhs).map: ps =>
        splitSignature(rhs) match
          case S((rest, ret)) => (ps :: rest, ret)
          case N => (ps :: Nil, rhs)
      case _ => N

  /** An override without a result annotation implements the result of the member it overrides as if it declared it:
    * lowering coerces the values of its body to the inherited representation, with checked casts where resolution
    * observes wider values (as when an override computes its result with dynamically typed operations, or when its
    * body never returns normally). A representation within the inherited one is kept, being more precise. An unrelated
    * one is kept as well, for `checkOverride` to report: such values cannot be coerced to the inherited result.
    */
  private def overrideResultType(td: TermDefinition, observed: Opt[ErasedValueType]): Opt[ErasedValueType] =
    td.tsym.overriddenMembers.headOption.filter(_.isErased) match
      case N => observed
      case S(base) =>
        val inherited = base.declaredResultType
        observed match
          case N => inherited
          case S(tpe) =>
            ErasedType.needsCast(tpe.canonicalize, inherited.getOrElse(ErasedType.Unknown).canonicalize) match
              case S(false) => observed
              case S(true) => inherited
              case N => observed

  private def definitionType(td: TermDefinition): Opt[ErasedType] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
    // A declared function with no written parameters obtains its calling convention from its arrows.
    // An ordinary paramless function instead returns the value denoted by the entire signature.
    val sigShape =
      if (td.k is syntax.Fun) && td.params.isEmpty && declared then td.sign.flatMap(splitSignature)
      else N
    val resultSign = sigShape.map(_._2).orElse(td.resultSignature)
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
    val resultType =
      if config.language.useNewResolution && td.sign.nonEmpty && (td.k is syntax.Fun)
          && !td.flags.hasResultAnnotation && td.params.nonEmpty && !td.modulefulness.isModuleful
      then S(fullResult(td.sign.get.typeInterpretation.get, td.params.length, Set.empty))
      else declaredType(resultSign, td.modulefulness).orElse(overrideResultType(td, inferredType(td.tsym)))
    bodyResults(td.tsym) = resultType
    // The body produces the payload; callers receive the wrapper object instead.
    // Resolution gives calls of such functions the same wrapper shapes.
    val callableResult =
      if !config.language.useNewResolution then resultType
      else td.resultWrapperAnnotation match
        case S(_: Annot.Async) => S(ErasedType.ValueLike(S(false), summon[Ctx].builtins.Promise))
        case S(_: Annot.Generator) => S(ErasedType.ValueLike(S(false), summon[Ctx].builtins.Iterator))
        case N => resultType
    td.k match
      case syntax.Fun =>
        val paramLists = sigShape match
          case S((ps, _)) => ps
          case N => td.params.map(_.params.map(_.sym.erasedType))
        // Block-level nullary functions take an implicit empty list and references auto-invoke them.
        // Member getters and global declarations denote their result directly.
        val physicalParamLists =
          if paramLists.isEmpty && td.owner.isEmpty && !declared then Nil :: Nil else paramLists
        if physicalParamLists.isEmpty then callableResult
        else S(ErasedType.FuncRef(rsc = S(false), physicalParamLists, callableResult))
      case _: syntax.Val => resultType
      case syntax.RecordField => if config.language.useNewResolution then resultType else N
      case _ => N

  private def run(root: Statement): Unit =
    val declarations = new ErasureDeclarations(root)
    val statements = declarations.statements
    val parameters = declarations.parameters.values
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

    def parentClasses(parent: New): Ls[ClassLikeDef] =
      (parent.cls.resolvedSym.flatMap(_.asClsOrMod).flatMap(_.defn).toList :::
        ClassValueShape.targetsOf(parent).map(ClassValueShape.definitionOf)).distinct
    def parentClass(parent: New): Opt[ClassLikeDef] = parentClasses(parent) match
      case cls :: Nil => S(cls)
      case _ => N

    // No erased representation is read until every interpretation has been validated and every
    // nominal parent header has been published, including forward and external declarations.
    statements.foreach:
      case term: Term => term.typeInterpretation.foreach(_.validate(Set.empty))
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

    // Public members replace inherited names; private members retain their declaration identity.
    // A subclass cannot implement a private declaration by introducing the same name.
    type MemberKey = Either[TermSymbol, Str]
    // Definitions are keyed by identity: as case classes, they would otherwise
    // be hashed and compared through their entire bodies on every lookup.
    val effectiveMembers = mutable.Map.empty[Identity[ClassLikeDef], Map[MemberKey, TermSymbol]]
    def checkConstruction(term: Term & PossiblyErroneous, cls: ClassDef): Unit =
      if Inheritance.hasModifier(cls, syntax.Keyword.`abstract`) then
        term.isErroneous = true
        raise(ErrorReport(
          msg"Cannot instantiate abstract class '${cls.sym.nme}'" -> term.toLoc ::
            (msg"Abstract class defined here" -> cls.toLoc) :: Nil, source = Diagnostic.Source.Compilation))
    def members(cls: ClassLikeDef, visiting: Set[Identity[ClassLikeDef]]): Map[MemberKey, TermSymbol] =
      effectiveMembers.getOrElseUpdate(Identity(cls),
        if visiting(Identity(cls)) then
          raise(ErrorReport(msg"Inheritance cycle involving '${cls.sym.nme}'" -> cls.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
          Map.empty
        else
          val inherited = cls.ext.flatMap(parentClass)
            .fold(Map.empty[MemberKey, TermSymbol])(members(_, visiting + Identity(cls)))
          inherited ++ cls.body.members.toList.flatMap: (name, member) =>
            member.asTrm.map: symbol =>
              val key: MemberKey = if symbol.isPrivate then Left(symbol) else Right(name)
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

    // An override shares the calling convention of the member it overrides: calls of that member reach it, and the
    // Wasm backend compiles it with that member's physical signature. Its parameters without declared types therefore
    // take the representations of the inherited parameters (even unknown ones), rather than of their own observed
    // inputs; `checkOverride` checks the declared ones.
    val inheritedParams: Map[VarSymbol, Param] = statements.iterator.flatMap:
      case td: TermDefinition => td.tsym.overriddenMembers.headOption.flatMap(_.defn).iterator.flatMap: base =>
        if td.params.map(_.params.length) != base.params.map(_.params.length) then Iterator.empty
        else td.params.iterator.zip(base.params).flatMap((ps, bps) => ps.params.iterator.zip(bps.params))
          .map((param, inherited) => param.sym -> inherited)
      case _ => Iterator.empty
    .toMap
    def eraseParameter(p: Param, visiting: Set[VarSymbol]): Unit = if !p.sym.isErased then
      p.sym.erasedType = declaredType(p.sign, p.modulefulness).orElse:
        inheritedParams.get(p.sym) match
          // Parameters of members defined in earlier programs are already erased.
          case S(inherited) if declarations.parameters.contains(inherited.sym) && !visiting(p.sym) =>
            eraseParameter(inherited, visiting + p.sym)
            inherited.sym.erasedType
          case S(inherited) => Option.when(inherited.sym.isErased)(inherited.sym.erasedType).flatten
          case N => inferredType(p.sym)
    parameters.foreach: p =>
      eraseParameter(p, Set.empty)
      // Public fields have a BlockMemberSymbol; private/auxiliary constructor fields have a TermSymbol.
      // Their source signatures belong to the parameter, not to the synthesized field definition.
      val field = p.fldSym.flatMap:
        case sym: TermSymbol => S(sym)
        case sym: BlockMemberSymbol => sym.tsym
        case _ => N
      field.foreach: sym =>
        if !sym.isErased then sym.erasedType =
          if p.flags.mut then declaredType(p.sign, p.modulefulness).orElse(inferredType(sym))
          else p.sym.erasedType
    val observed =
      if config.language.useNewResolution then summon[State].newResolverState.erasureInputs.symbols
      else Nil
    // Constructor companions have no source body. Their physical argument lists
    // are the class's lists, and a saturated call always produces its instance.
    statements.foreach:
      case cls: ClassLikeDef => cls.ctorSym.foreach: symbol =>
        if !symbol.isErased then symbol.erasedType =
          if config.language.useNewResolution then S(ErasedType.FuncRef(S(false),
            (cls.paramsOpt.toList ::: cls.auxParams).map(_.params.map(_.sym.erasedType)), S(nominalType(cls))))
          else N
      case _ => ()
    val definitions = statements.collect { case td: TermDefinition => td } ++ observed.collect {
      case sym: TermSymbol => sym.defn }.flatten
    // A handler's compiled declaration omits its resumption parameter list;
    // retain the traversed declaration instead of recovering the original from its symbol.
    // An override's result can be the inherited one (see `overrideResultType`), so the members a definition
    // overrides are erased first. Overriding edges are acyclic, but erroneous inheritance cycles must not diverge.
    val definitionsBySymbol = definitions.distinctBy(_.tsym).map(td => td.tsym -> td).toMap
    def eraseDefinition(td: TermDefinition, visiting: Set[TermSymbol]): Unit =
      if !td.tsym.isErased && !visiting(td.tsym) then
        td.tsym.overriddenMembers.flatMap(definitionsBySymbol.get).foreach(eraseDefinition(_, visiting + td.tsym))
        td.tsym.erasedType = definitionType(td)
    definitions.distinctBy(_.tsym).foreach(eraseDefinition(_, Set.empty))
    declarations.variables.foreach:
      case sym: VarSymbol if !sym.isErased => sym.erasedType = inferredType(sym)
      case sym: TermSymbol if !sym.isErased => sym.erasedType = inferredType(sym)
      // A temporary's erased type is populated at most once (see TempSymbol); without inferred inputs, it stays
      // unknown, as it was before erasure.
      case sym: TempSymbol if sym.erasedType.isEmpty => inferredType(sym).foreach(sym.populateErasedType(_))
      case _ => ()
    // These checks compare erased signatures, so they run once every definition of the program is erased.
    statements.foreach:
      case td: TermDefinition =>
        checkOverride(td)
        checkExposedOpenMember(td, declarations)
        checkExposedMutableField(td)
      case _ => ()
    completed = S(root)

  /** An override is reached through calls of the member it overrides, so it must accept every representation of the
    * inherited parameters and produce only representations of the inherited result. The Wasm backend also compiles all
    * the overrides of a method with the physical signature of the method introducing it, so on that target, an
    * override called directly cannot accept representations that this signature cannot hold either: its parameters
    * must have the representations of the inherited ones. Unchecked, such mismatches would be bridged by casts that
    * fail at run time. Parameters without declared types already take the inherited representations (see
    * `inheritedParams` in `run`), so only declared ones can fail the parameter checks.
    */
  private def checkOverride(td: TermDefinition): Unit =
    def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType]): Bool =
      ErasedType.needsCast(actual.getOrElse(ErasedType.Unknown).canonicalize,
        expected.getOrElse(ErasedType.Unknown).canonicalize).contains(false)
    def describe(tpe: Opt[ErasedValueType]): Str = tpe.getOrElse(ErasedType.Unknown).canonicalize.describe
    def signature(sym: TermSymbol): (Ls[Ls[Opt[ErasedValueType]]], Opt[ErasedValueType]) = sym.erasedType match
      case S(ft: ErasedFuncType) => (ft.paramLists, ft.ret)
      case S(vt: ErasedValueType) => (Nil, S(vt))
      case N => (Nil, N)
    if td.tsym.isErased then
      val (params, result) = signature(td.tsym)
      td.tsym.overriddenMembers.filter(_.isErased).foreach: base =>
        val (baseParams, baseResult) = signature(base)
        def report(message: Message, loc: Opt[Loc]): Unit = raise(ErrorReport(
          (message -> loc) :: (msg"The overridden member '${base.nme}' is defined here" -> base.toLoc) :: Nil,
          source = Diagnostic.Source.Compilation))
        if !within(result, baseResult) then report(
          msg"Overriding member '${td.tsym.nme}' produces values represented as '${describe(result)
            }', which the member it overrides cannot produce: its results are represented as '${describe(baseResult)}'",
          td.tsym.toLoc)
        // Parameter lists of different lengths are reported by the backends that require equal lengths.
        if params.map(_.length) == baseParams.map(_.length) then
          params.flatten.lazyZip(baseParams.flatten).lazyZip(td.params.flatMap(_.params)).foreach: (param, baseParam, p) =>
            if !within(baseParam, param) then report(
              msg"Parameter '${p.sym.nme}' of overriding member '${td.tsym.nme}' is represented as '${describe(param)
                }', which cannot hold the values represented as '${describe(baseParam)}' that the member it overrides accepts",
              p.toLoc)
            else if (config.target is CompilationTarget.Wasm) && !within(param, baseParam) then report(
              msg"Parameter '${p.sym.nme}' of overriding member '${td.tsym.nme}' receives values represented as '${
                describe(param)}', but Wasm calls it through the signature of the member it overrides, whose parameter is represented as '${
                describe(baseParam)}'",
              p.toLoc)

  /** Subclasses in other compilation units implement an open member with the representations of its erased signature,
    * which therefore must not depend on what this compilation unit happens to pass to the member or return from it.
    * Interface exposure feeds values of unknown shape to the unannotated parameters of members reachable from the
    * unit's interface (see InterfaceExposure); an open member receiving them must annotate its parameters and result.
    * Exposure is not observed for a member whose parameters are all annotated, or which has none: overrides in other
    * compilation units are then still checked against its erased signature by `checkOverride`.
    */
  private def checkExposedOpenMember(td: TermDefinition, declarations: ErasureDeclarations): Unit =
    if config.language.useNewResolution && (td.k is syntax.Fun) && Inheritance.isOpen(td) && !Inheritance.isExternal(td) then
      val params = td.params.flatMap(ps => ps.params ::: ps.restParam.toList)
      def exposed(p: Param): Bool = declarations.parameters.contains(p.sym) &&
        summon[State].newResolverState.erasureInputs.shapes(p.sym).exists: shape =>
          shape.applicationHead._1 match
            case unknown: UnknownValueShape => unknown.fromPublicInterface
            case _ => false
      if params.exists(exposed) then
        val missing = params.filter(_.sign.isEmpty).map(p => msg"Parameter '${p.sym.nme}' has no type annotation" -> p.toLoc)
          ::: Option.when(td.resultSignature.isEmpty)(msg"Its result has no type annotation" -> td.tsym.toLoc).toList
        if missing.nonEmpty then raise(ErrorReport(
          (msg"Open member '${td.tsym.nme}' is exposed to other compilation units, which can override it; annotate the types of its parameters and result" -> td.tsym.toLoc)
            :: missing,
          source = Diagnostic.Source.Compilation))

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

object Erasure:
  /** Prelude declarations use the same pass even though they have no executable program. */
  def apply(root: Statement)(using Config, Ctx, State)(using Raise): Erasure =
    val erasure = new Erasure
    erasure.run(root)
    erasure
