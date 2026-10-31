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
        case _ => ErasedType.Unknown

  /** Computes the runtime value representation denoted by a completed type interpretation.
    * Follows aliases and references, discards type arguments, and preserves nominal types, unions,
    * and function representations. Cycles, resolution errors, and unsupported shapes yield `Unknown`.
    * [[OverrideLayout]] uses this to erase the result remaining after it extracts a callable's lists.
    */
  private[codegen] def eraseResolved(resolution: TypeResolution): ErasedValueType = erase(resolution, Set.empty)

  /** Computes the runtime value representation denoted by a source type signature. With the new
    * resolver, elaboration must have registered the term's type interpretation and resolution must
    * have completed; an unknown representation yields `S(Unknown)`. The legacy resolver reads the
    * resolved syntax and can return `N` when it cannot derive a representation.
    */
  private[codegen] def eraseSignature(sign: Term): Opt[ErasedValueType] =
    if config.language.useNewResolution then
      assert(sign.typeInterpretation.isDefined, "Signature was not registered during elaboration")
      S(erase(sign.typeInterpretation.get, Set.empty))
    else ErasedType.eraseSign(sign)

  private def declaredType(sign: Opt[Term], modulefulness: Modulefulness): Opt[ErasedValueType] =
    modulefulness.msym match
      case S(msym) => S(ErasedType.ValueLike(rsc = S(false), msym))
      case N => sign.flatMap(eraseSignature)

  /** Computes the representation to publish on a member symbol: a value type, a getter result,
    * or a function's parameter lists and result. Parameter symbols must already have their erased
    * types. Declared functions can obtain their lists from callable arrows; unannotated overrides
    * can obtain their result from an inherited member in `overrideEdges` that has completed erasure.
    * Those pairs must already have passed source layout validation.
    * For example, `declare fun f: (Int) -> Str` publishes one `Int` parameter and a `Str` result.
    */
  private def erasedDefinitionSignature(td: TermDefinition,
      overrideEdges: Ls[(TermSymbol, TermSymbol)]): Opt[ErasedValueType | ErasedCallableSignature] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
    // A declared function with no written parameters obtains its calling convention from its arrows.
    // An ordinary paramless function instead returns the value denoted by the entire signature.
    val sigShape =
      if (td.k is syntax.Fun) && td.params.isEmpty && declared then
        OverrideLayout.signature(td).toOption.flatMap: signature =>
          // A rest tuple has no fixed physical arity. Preserve any preceding fixed lists,
          // whose result remains a callable, and use the same normalized aliases as overrides.
          val fixed = signature.params.takeWhile(_.variadic.isEmpty)
          if fixed.isEmpty then N
          else S((fixed.map(_.params.map(_.representation)),
            if fixed.length < signature.params.length then S(ErasedType.Function(S(false))) else signature.result))
      else N
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
      else sigShape.fold(declaredType(td.resultSignature, td.modulefulness))(_._2).orElse:
        // An unannotated override implements the inherited result. Async/generator annotations
        // describe a body payload; their inherited callable result describes the wrapper.
        if config.language.useNewResolution && td.resultWrapperAnnotation.nonEmpty then N
        else overrideEdges.collectFirst { case (child, base) if (child is td.tsym) && base.isErased => base }
          .flatMap(_.declaredResultType)
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
        val paramLists = sigShape match
          case S((ps, _)) => ps
          case N => td.params.map(LoweredParamList.fixedPrefix(_).map(_.sym.erasedType))
        // Block-level nullary functions take an implicit empty list and references auto-invoke them.
        // Member getters and global declarations denote their result directly.
        val physicalParamLists =
          if paramLists.isEmpty && td.owner.isEmpty && !declared then Nil :: Nil else paramLists
        if physicalParamLists.isEmpty then S(ErasedGetterSignature.Signature(result))
        else S(ErasedFuncSignature.Signature(physicalParamLists, result))
      case _: syntax.Val => resultType
      case _ => N

  /** The `(overriding, inherited)` declaration pairs whose source layouts preserve argument bindings,
    * including abstract and external declarations. Construction initializes the whole program's
    * representations before publishing these pairs for [[TargetOverrideChecks]] to use after lowering.
    * A pair can remain in the result even if its representation check reported an error.
    */
  val validatedOverrideEdges: Ls[(TermSymbol, TermSymbol)] =
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
    val overrideChecks = new OverrideChecks(statements.collect { case td: TermDefinition => td })
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
        p.sym.erasedType = declaredType(p.sign, p.modulefulness).orElse:
          inheritedParams.get(p.sym) match
            case S(inherited) =>
              // Imported parameters are already erased; erroneous inheritance cycles can leave a
              // local parameter pending. Do not read it or initialize a symbol twice on such a cycle.
              inherited.flatMap(_.parameter).foreach: param =>
                if parameterSymbols(param.sym) then eraseParameter(param, visiting + p.sym)
              val types = inherited.map: input =>
                input.parameter match
                  case S(param) =>
                    if param.sym.isErased then param.sym.erasedType.getOrElse(ErasedType.Unknown) else ErasedType.Unknown
                  case N => input.representation.getOrElse(ErasedType.Unknown)
              // Making a required slot optional additionally admits null on direct subclass calls.
              // Its inherited argument channel is unchanged for calls through the base interface.
              val defaults = if p.flags.opt && inherited.exists(!_.flags.opt) then ErasedType.Unknown :: Nil else Nil
              S(ErasedType.Union.mk(types ::: defaults))
            // Rest binding constructs an Array, including when lowering slices off trailing
            // arguments. Use that representation unless a declared or inherited type supplies one.
            case N => Option.when(restParameters(p.sym))(ErasedType.Array)
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
    // Retain the traversed declarations: handlers remove the resumption parameter list from them.
    // Erase inherited results before their overrides, guarding against erroneous inheritance cycles.
    val definitions = statements.collect { case td: TermDefinition => td }.distinctBy(_.tsym)
    val definitionsBySymbol = definitions.map(td => td.tsym -> td).toMap
    /** Publishes a declaration's erased signature after initializing its local inherited members,
      * so an unannotated override can inherit their result representation. Imported members already
      * have erased signatures. `visiting` breaks erroneous inheritance cycles; signature computation
      * only consults inherited results whose members have completed erasure.
      */
    def eraseDefinition(td: TermDefinition, visiting: Set[TermSymbol]): Unit =
      if !td.tsym.isErased && !visiting(td.tsym) then
        td.tsym.overriddenMembers.flatMap(definitionsBySymbol.get).foreach(eraseDefinition(_, visiting + td.tsym))
        td.tsym.initializeErasure(erasedDefinitionSignature(td, overrideChecks.validatedEdges))
    definitions.foreach(eraseDefinition(_, Set.empty))
    statements.foreach:
      case LetDecl(sym: TermSymbol, _) if !sym.isErased => sym.initializeErasure(N)
      case _ => ()
    // Compare signatures only after every definition has completed erasure.
    overrideChecks.checkRepresentations()
    overrideChecks.validatedEdges
