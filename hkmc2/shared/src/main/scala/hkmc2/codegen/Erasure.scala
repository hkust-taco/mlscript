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
  */
final class Erasure(root: Statement)(using Config, Ctx, State)(using Raise):
  private given Erasure = this

  /** Checks that lowering uses the same source root whose signatures this instance initialized. */
  def requireCompleted(statement: Statement): Unit =
    assert(root is statement, "Lowering requires completed erasure of this program")

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

  /** Rejects a declared type without a runtime representation, such as `Int32 | Str`:
    * an unboxed primitive shares no representation with any other type, so no value of such
    * a slot can be stored or passed. Reporting it once at the declaration replaces the errors
    * that each coercion into or out of the slot would report. Class headers are published
    * before declarations are erased, so canonicalizing here sees complete parent chains.
    *
    * The Prelude and Runtime are erased before the runtime's symbols exist, and
    * canonicalizing a type such as `Unit` requires them. Those library declarations are not
    * checked; every other compilation unit is erased after the runtime is loaded.
    */
  private def representable(tpe: ErasedValueType, loc: Opt[Loc]): ErasedValueType =
    if !summon[State].runtimeSymbolsInitialized then tpe
    else tpe.canonicalize match
      case incompatible @ ErasedType.Incompatible(lhs, rhs) if !incompatible.reported =>
        raise(ErrorReport(
          msg"Types '${lhs.describe}' and '${rhs.describe}' have no common representation" -> loc :: Nil,
          source = Diagnostic.Source.Compilation))
        ErasedType.Incompatible(lhs, rhs)(reported = true)
      case _ => tpe
  
  private def declaredType(sign: Opt[Term], modulefulness: Modulefulness): Opt[ErasedValueType] =
    modulefulness.msym match
      case S(msym) => S(ErasedType.ValueLike(rsc = S(false), msym))
      case N => sign.flatMap(eraseSignature)

  /** Computes the representation to publish on a member symbol: a value type, a getter result,
    * or a function's parameter lists and result. Parameter symbols must already have their erased
    * types. A function's physical parameter lists are its written ones: arrows in the type of a
    * function without parameter lists, as in `declare fun f: (Int) -> Str`, describe the function
    * value it returns. Unannotated overrides can obtain their result from an inherited member
    * that passed source layout validation in `overrides` and has completed erasure.
    */
  private def erasedDefinitionSignature(td: TermDefinition,
      overrides: OverrideChecks): Opt[ErasedValueType | ErasedCallableSignature] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
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
    val candidateResultType =
      if config.language.useNewResolution && td.sign.nonEmpty && (td.k is syntax.Fun)
          && !td.flags.hasResultAnnotation && td.params.nonEmpty && !td.modulefulness.isModuleful
      then S(fullResult(td.sign.get.typeInterpretation.get, td.params.length, Set.empty))
      else declaredType(td.resultSignature, td.modulefulness).orElse:
        // An unannotated override implements the inherited result. Async/generator annotations
        // describe a body payload; their inherited callable result describes the wrapper.
        // A structural intersection can give a member several bases: an unannotated one publishes
        // no result, so inherit from the first base that declares one; representation checking
        // then reports any other base whose result the override does not fit.
        if config.language.useNewResolution && td.resultWrapperAnnotation.nonEmpty then N
        else overrides.validatedBases.getOrElse(td.tsym, Nil).iterator.filter(_.isErased)
          .flatMap(_.sourceDeclaredResultType).nextOption()
    val resultType = candidateResultType.map:
      representable(_, td.resultSignature.orElse(td.sign).flatMap(_.toLoc).orElse(td.tsym.toLoc))
    // The body produces the payload; callers receive the wrapper object instead.
    // Resolution gives calls of such functions the same wrapper shapes.
    val result =
      if !config.language.useNewResolution then ErasedResult.Direct(resultType)
      else td.resultWrapperAnnotation match
        case S(_: Annot.Async) => ErasedResult.Async(resultType)
        case S(_: Annot.Generator) => ErasedResult.Generator(resultType)
        case N => ErasedResult.Direct(resultType)
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
      case _ => N

  locally:
    val (statements, parameters, parentConstructions) =
      // One ordered identity set both bounds traversal of shared syntax and preserves diagnostic order.
      // Only this collection step can extend the inputs to the subsequent erasure phases.
      val visited = mutable.LinkedHashSet.empty[Identity[Statement]]
      val parameters = List.newBuilder[Param]
      val parentConstructions = mutable.Set.empty[Identity[Statement]]
      def parentHead(term: Term): Unit = if parentConstructions.add(Identity(term)) then term match
        // Legacy resolution can expand a parent reference to an implicit constructor call.
        // Follow only the class head; constructions in argument expressions are real allocations.
        case ref: Resolvable if ref.expanded isnt ref => parentHead(ref.expanded)
        case New(cls, _, _) => parentHead(cls)
        case App(lhs, _) => parentHead(lhs)
        case TyApp(lhs, _) => parentHead(lhs)
        case _ => ()
      def params(ps: ParamList): Unit = ps.foreach(parameters += _)
      // Handler continuations and rejected class rest parameters can survive as references after their
      // parameter list has been removed. The symbol retains the source declaration needed for erasure.
      def referencedParameter(sym: VarSymbol): Unit = sym.decl match
        case S(p: Param) =>
          parameters += p
          p.subTerms.foreach(visit)
        case _ => ()
      def visit(statement: Statement): Unit = if visited.add(Identity(statement)) then
        statement match
          case td: TermDefinition => td.params.foreach(params); td.tparams.foreach(_.foreach(parameters += _))
          case cls: ClassLikeDef =>
            cls.paramsOpt.foreach(params)
            cls.auxParams.foreach: ps =>
              params(ps)
              ps.subTerms.foreach(visit)
            cls.ext.foreach: parent =>
              parentHead(parent)
              visit(parent)
            cls match
              case pat: PatternDef =>
                parameters ++= pat.parameters
                pat.parameters.flatMap(_.subTerms).foreach(visit)
                pat.pattern.subTerms.foreach(visit)
              case _ => ()
          case Lam(ps, _) => params(ps)
          case Handle(defs = definitions) => definitions.foreach: d =>
            referencedParameter(d.resumeSym)
            visit(d.td)
          case Ref(sym: VarSymbol) => referencedParameter(sym)
          case SimpleRef(sym: VarSymbol) => referencedParameter(sym)
          case New(_, _, refinement) => refinement.foreach: (symbol, body) =>
            symbol.defn.fold(visit(body.blk))(visit)
          case Rcd(_, stats) => stats.foreach(visit)
          case _ => ()
        statement.subStatements.foreach(visit)
        // Legacy resolution may insert executable terms (for example implicit applications).
        // Expanded nodes may share their children with the source tree; visit their identities only once.
        statement match
          case term: Resolvable => visit(term.expanded)
          case _ => ()
      visit(root)
      (visited.iterator.map(_.value).toList, parameters.result(), parentConstructions.toSet)

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
    val definitions = statements.collect { case td: TermDefinition => td }.distinctBy(_.tsym)
    val overrideChecks = new OverrideChecks(definitions)
    overrideChecks.checkExposedSignatures()
    val inheritedParams = overrideChecks.inheritedParameters
    val parameterSymbols = parameters.iterator.map(_.sym).toSet
    /** Initializes a parameter's representation from its annotation or the joined representations
      * of its inherited counterparts. A rest parameter with neither gets `Array`; an ordinary
      * parameter with neither keeps no known representation. Recursion initializes local inherited
      * parameters first, while `visiting` breaks inheritance cycles; pending inherited parameters
      * contribute `Unknown`. Making a required inherited parameter optional also admits its null default.
      */
    def eraseParameter(p: Param, visiting: Set[VarSymbol]): Unit =
      if !p.sym.isErased && !visiting(p.sym) then
        val erased = declaredType(p.sign, p.modulefulness).orElse:
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
            case N => Option.when(restParameters(p.sym))(ErasedType.Array)
        // Inherited parameter types can also join into a type without a representation.
        p.sym.erasedType = erased.map(representable(_, p.sign.flatMap(_.toLoc).orElse(p.toLoc)))
    parameters.foreach: p =>
      eraseParameter(p, Set.empty)
      // Public fields have a BlockMemberSymbol; private/auxiliary constructor fields have a TermSymbol.
      // Their source signatures belong to the parameter, not to the synthesized field definition.
      val field = p.fldSym.flatMap:
        case sym: TermSymbol => S(sym)
        case sym: BlockMemberSymbol => sym.tsym
        case _ => N
      field.foreach: sym =>
        if !sym.isErased then sym.initializeErasure(p.sym.erasedType)
    // Erase inherited results before their overrides, guarding against erroneous inheritance cycles.
    val definitionsBySymbol = definitions.map(td => td.tsym -> td).toMap
    /** Publishes a declaration's erased signature after initializing its local inherited members,
      * so an unannotated override can inherit their result representation. Imported members already
      * have erased signatures. `visiting` breaks erroneous inheritance cycles; signature computation
      * only consults inherited results whose members have completed erasure.
      */
    def eraseDefinition(td: TermDefinition, visiting: Set[TermSymbol]): Unit =
      if !td.tsym.isErased && !visiting(td.tsym) then
        td.tsym.overriddenMembers.flatMap(definitionsBySymbol.get).foreach(eraseDefinition(_, visiting + td.tsym))
        td.tsym.initializeErasure(erasedDefinitionSignature(td, overrideChecks))
    definitions.foreach(eraseDefinition(_, Set.empty))
    statements.foreach:
      case LetDecl(sym: TermSymbol, _) if !sym.isErased => sym.initializeErasure(N)
      case _ => ()
    // Compare signatures only after every definition has completed erasure.
    overrideChecks.checkSignatures()
