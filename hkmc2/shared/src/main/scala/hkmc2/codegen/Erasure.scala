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
  */
final class Erasure private (using Config, Ctx, State)(using Raise):
  private given Erasure = this
  private var completed: Opt[Statement] = N
  private val valueTypes = mutable.Map.empty[TermShape, Opt[ErasedValueType]]
  private val bodyResults = mutable.Map.empty[TermSymbol, Opt[ErasedValueType]]

  def requireCompleted(statement: Statement): Unit =
    assert(completed.exists(_ is statement), "Lowering requires completed erasure of this program")

  /** Async definitions expose a promise, but their original bodies produce its payload.
    * Lowering must coerce explicit and implicit returns before AsyncLowering wraps them.
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
      else declaredType(resultSign, td.modulefulness).orElse(inferredType(td.tsym))
    bodyResults(td.tsym) = resultType
    val callableResult =
      if config.language.useNewResolution && td.asyncAnnotation.nonEmpty
      then S(ErasedType.ValueLike(S(false), summon[Ctx].builtins.Promise))
      else resultType
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
            sym.irClassHeader = cls.ext match
              case N => S(ClassHeader(N))
              case S(parent) => parentClass(parent).flatMap(_.sym.asClsOrMod).map(p => ClassHeader(S(p)))
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

    parameters.foreach: p =>
      if !p.sym.isErased then p.sym.erasedType = declaredType(p.sign, p.modulefulness).orElse(inferredType(p.sym))
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
    definitions.distinctBy(_.tsym).foreach: td =>
      if !td.tsym.isErased then td.tsym.erasedType = definitionType(td)
    declarations.variables.foreach:
      case sym: VarSymbol if !sym.isErased => sym.erasedType = inferredType(sym)
      case sym: TermSymbol if !sym.isErased => sym.erasedType = inferredType(sym)
      case _ => ()
    completed = S(root)

object Erasure:
  /** Prelude declarations use the same pass even though they have no executable program. */
  def apply(root: Statement)(using Config, Ctx, State)(using Raise): Erasure =
    val erasure = new Erasure
    erasure.run(root)
    erasure
