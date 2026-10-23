package hkmc2
package semantics

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import syntax.*, Elaborator.State, codegen.{Erasure, ErasedType, ErasedValueType, ErasedFuncType, CanonicalErasedValueType}
import Term.*
import ucs.FlatPattern


/** Copy resolved code for another executable occurrence. Each binding scope owns a
  * substitution: copies of a shared subtree get different binders, while free references
  * still denote the enclosing scope. Inference graphs are completed source witnesses;
  * their subscriptions are not copied or restarted during lowering.
  */
private[semantics] final class Cloner(outer: SymbolSubst)(using State, Erasure) extends SymbolSubst:
  private given SymbolSubst = this

  private lazy val variables = mutable.Map.empty[VarSymbol, VarSymbol]
  private lazy val temporaries = mutable.Map.empty[TempSymbol, TempSymbol]
  private lazy val labels = mutable.Map.empty[LabelSymbol, LabelSymbol]
  private lazy val splits = mutable.Map.empty[SplitSymbol, SplitSymbol]
  private lazy val members = mutable.Map.empty[BlockMemberSymbol, BlockMemberSymbol]
  private lazy val terms = mutable.Map.empty[TermSymbol, TermSymbol]
  private lazy val classes = mutable.Map.empty[ClassSymbol, ClassSymbol]
  private lazy val modules = mutable.Map.empty[ModuleOrObjectSymbol, ModuleOrObjectSymbol]
  private lazy val aliases = mutable.Map.empty[TypeAliasSymbol, TypeAliasSymbol]
  private lazy val patterns = mutable.Map.empty[PatternSymbol, PatternSymbol]
  private lazy val constructors = mutable.Map.empty[ClassCtorSymbol, ClassCtorSymbol]
  private lazy val definitions = mutable.Map.empty[Identity[Definition], Definition]

  override def mapVarSym(s: VarSymbol): VarSymbol = variables.getOrElse(s, outer.mapVarSym(s))
  override def mapTempSym(s: TempSymbol): TempSymbol = temporaries.getOrElse(s, outer.mapTempSym(s))
  override def mapLabelSym(s: LabelSymbol): LabelSymbol = labels.getOrElse(s, outer.mapLabelSym(s))
  override def mapSplitSym(s: SplitSymbol): SplitSymbol = splits.getOrElse(s, outer.mapSplitSym(s))
  override def mapBlockMemberSym(s: BlockMemberSymbol): BlockMemberSymbol = members.getOrElse(s, outer.mapBlockMemberSym(s))
  override def mapTermSym(s: TermSymbol): TermSymbol = terms.getOrElse(s, outer.mapTermSym(s))
  override def mapClsSym(s: ClassSymbol): ClassSymbol = classes.getOrElse(s, outer.mapClsSym(s))
  override def mapModuleSym(s: ModuleOrObjectSymbol): ModuleOrObjectSymbol = modules.getOrElse(s, outer.mapModuleSym(s))
  override def mapTypeAliasSym(s: TypeAliasSymbol): TypeAliasSymbol = aliases.getOrElse(s, outer.mapTypeAliasSym(s))
  override def mapPatSym(s: PatternSymbol): PatternSymbol = patterns.getOrElse(s, outer.mapPatSym(s))
  override def mapClassCtorSym(s: ClassCtorSymbol): ClassCtorSymbol = constructors.getOrElse(s, outer.mapClassCtorSym(s))

  private def nested = new Cloner(this)

  private def mapSimple(s: SimpleRefSymbol): SimpleRefSymbol = s match
    case s: LocalVarSymbol => s.subst
    case s: LabelSymbol => s.subst
    case s: BuiltinSymbol => s.subst

  private def mapType(s: TypeSymbol): TypeSymbol = s match
    case s: ClassSymbol => s.subst
    case s: ModuleOrObjectSymbol => s.subst
    case s: TypeAliasSymbol => s.subst

  private def mapClassCompanion(s: ClassCompanionSymbol): ClassCompanionSymbol = s match
    case s: ModuleOrObjectSymbol => s.subst
    case s: TypeAliasSymbol => s.subst

  private def mapModuleCompanion(s: ModuleCompanionSymbol): ModuleCompanionSymbol = s match
    case s: ClassSymbol => s.subst
    case s: TypeAliasSymbol => s.subst

  private def canonicalType(source: CanonicalErasedValueType): CanonicalErasedValueType = source match
    case ErasedType.AnyRef(rsc, symbol) => ErasedType.AnyRef(rsc, mapType(symbol))
    case ErasedType.Incompatible(left, right) => ErasedType.Incompatible(canonicalType(left), canonicalType(right))
    case source @ (_: ErasedType.Primitive | ErasedType.Unknown) => source

  private def valueType(source: ErasedValueType): ErasedValueType = source match
    case source: CanonicalErasedValueType => canonicalType(source)
    case source: ErasedType.ValueLike =>
      val symbol = mapType(summon[Erasure].typeSymbol(source))
      new ErasedType.ValueLike(source.rsc, symbol)
    case ErasedType.Union(members) => ErasedType.Union(members.map(valueType))

  private def erasedType(source: ErasedType): ErasedType = source match
    case source: ErasedValueType => valueType(source)
    case source: ErasedFuncType => ErasedType.FuncRef(source.rsc,
      source.paramLists.map(_.map(_.map(valueType))), source.ret.map(valueType))

  private def located[A <: AutoLocated](source: AutoLocated, copy: A): A =
    if source is copy then copy else copy.withLoc(source.getLoc)

  private def copyMetadata[A <: Term](source: Term, copy: A): A =
    copy.typeInterpretation = source.typeInterpretation
    // These completed shapes describe source declarations and calling conventions.
    // Executable reference targets are substituted separately below.
    copy.shapes.copyFrom(source.shapes)
    located(source, copy)

  extension (source: Term)
    private def cloned: Term = term(source)

  private def bindLocal(symbol: LocalVarSymbol): Unit = symbol match
    case s: VarSymbol => variables.getOrElseUpdate(s, {
      val copy = new VarSymbol(s.id)
      if s.isErased then copy.erasedType = s.erasedType.map(valueType)
      copy.sourceAliases = s.sourceAliases
      copy.decl = s.decl
      copy.shapes.copyFrom(s.shapes)
      copy
    })
    case s: TempSymbol => temporaries.getOrElseUpdate(s, {
      val copy = new TempSymbol(s.trm, s.erasedType.map(erasedType), s.nme)
      copy.shapes.copyFrom(s.shapes)
      copy
    })

  private def bindLabel(s: LabelSymbol): Unit =
    labels(s) = new LabelSymbol(s.trm, s.nme)

  private def bindTerm(s: TermSymbol): Unit = s match
    case s: ClassCtorSymbol => constructors.getOrElseUpdate(s,
      new ClassCtorSymbol(s.k, s.owner.map(_.subst), s.associatedCls.subst))
    case s => terms.getOrElseUpdate(s, {
      val copy = new TermSymbol(s.k, s.owner.map(_.subst), s.id)
      copy.sourceAliases = s.sourceAliases
      copy
    })

  private def bindInner(s: ClassSymbol | ModuleOrObjectSymbol | PatternSymbol): Unit =
    val copy = s match
      case s: ClassSymbol => classes.getOrElseUpdate(s, new ClassSymbol(s.tree, s.id))
      case s: ModuleOrObjectSymbol => modules.getOrElseUpdate(s, new ModuleOrObjectSymbol(s.tree, s.id))
      case s: PatternSymbol => patterns.getOrElseUpdate(s, new PatternSymbol(s.id, s.params, s.body))
    temporaries.getOrElseUpdate(s.thisProxy, copy.thisProxy)

  /** A source type tree owns its definition symbol. Copy its outer node as well as
    * the block member so `symbols`/`asCls` cannot lead back to the old definition.
    * Its syntax children remain source witnesses; executable bodies are copied below.
    */
  private def bindMember(s: BlockMemberSymbol): Unit = members.getOrElseUpdate(s, {
    val trees = s.trees.map:
      case tree: Tree.TypeDef =>
        val copy = located(tree, tree.copy())
        (tree.symbol, copy.symbol) match
          case (old: ClassSymbol, fresh: ClassSymbol) => classes(old) = fresh
          case (old: ModuleOrObjectSymbol, fresh: ModuleOrObjectSymbol) => modules(old) = fresh
          case (old: TypeAliasSymbol, fresh: TypeAliasSymbol) => aliases(old) = fresh
          case (old: PatternSymbol, fresh: PatternSymbol) => patterns(old) = fresh
          case _ => lastWords("A copied type declaration must retain its kind")
        copy
      case tree => tree
    val copy = new BlockMemberSymbol(s.nme, trees, s.nameIsMeaningful)
    copy.sourceAliases = s.sourceAliases
    copy
  })

  private def bindImport(s: BlockMemberSymbol): Unit = members.getOrElseUpdate(s, {
    // Importing creates a local binding for an existing module, not another
    // declaration of that module or of any of its nominal types.
    val copy = new BlockMemberSymbol(s.nme, s.trees, s.nameIsMeaningful)
    copy.sourceAliases = s.sourceAliases
    copy
  })

  private def fieldDefinitions(source: ClassLikeDef): Ls[TermDefinition] =
    (source.paramsOpt.toList ::: source.auxParams).flatMap(_.allParams).flatMap: p =>
      p.fldSym.toList.flatMap:
        case sym: BlockMemberSymbol => sym.tsym.toList.flatMap(_.defn)
        case sym: TermSymbol => sym.defn.toList
        case _ => Nil

  private def prepareDefinitions(stats: Ls[Statement]): Unit =
    // Allocate all block-level names before copying any bodies: functions and
    // classes can refer forward to each other and share overloaded member names.
    stats.foreach:
      case d: Definition => bindMember(d.bsym)
      case imp: Import => imp.sym match
        case s: LocalVarSymbol => bindLocal(s)
        case s: BlockMemberSymbol => bindImport(s)
      case _ => ()
    stats.foreach:
      case d: ClassLikeDef => d.sym match
        case s: (ClassSymbol | ModuleOrObjectSymbol | PatternSymbol) => bindInner(s)
        case _: TopLevelSymbol => lastWords("A top-level compilation unit is not a nested declaration")
      case d: TypeDef => aliases.getOrElseUpdate(d.sym, new TypeAliasSymbol(d.sym.id))
      case _ => ()
    stats.foreach:
      case d: TermDefinition => bindTerm(d.tsym)
      case d: ClassDef => d.ctorSym.foreach(bindTerm)
      case LetDecl(s: TermSymbol, _) => bindTerm(s)
      case _ => ()
    // Selections outside a class still name its members. Publish their renaming
    // in this scope before copying any body, including forward selections and
    // references between companion definitions. Only executable local binders
    // (parameters/lets) belong to the body's child substitution.
    stats.foreach:
      case d: ClassLikeDef => prepareDefinitions(d.body.blk.stats ::: fieldDefinitions(d))
      case _ => ()
    members.foreach: (source, copy) =>
      copy.tsym = source.tsym.map(_.subst)

  private def prepareLocals(stats: Ls[Statement]): Unit = stats.foreach:
    case LetDecl(s: LocalVarSymbol, _) => bindLocal(s)
    case _ => ()

  private def prepare(stats: Ls[Statement]): Unit =
    prepareDefinitions(stats)
    prepareLocals(stats)
    // An annotation can name a class nested in a later declaration. Wait until
    // all nominal symbols are allocated before renaming erased signatures.
    terms.foreach: (source, copy) =>
      if source.isErased then copy.erasedType = source.erasedType.map(erasedType)
    // All member names, including nested classes' methods, now have replacements.
    // Override edges must follow them for common-member selection during lowering.
    (members.iterator ++ terms.iterator).foreach: (source, copy) =>
      copy.overrideLinks.shapes.mapFrom(source.overrideLinks.shapes)(_.subst, identity)

  def block(source: Blk): Blk =
    val scope = nested
    scope.prepare(source.stats)
    val copy = new Blk(source.stats.map(scope.statement), scope.term(source.res))
    copyMetadata(source, copy)

  def statementRoot(source: Statement): Statement =
    prepare(source :: Nil)
    statement(source)

  private def statement(source: Statement): Statement = source match
    case t: Term => term(t)
    case d: Definition => definition(d)
    case imp: Import =>
      val sym: ImportSymbol = imp.sym match
        case s: VarSymbol => s.subst
        case s: TempSymbol => s.subst
        case s: BlockMemberSymbol => s.subst
      Import(sym, imp.str, imp.file)(imp.toLoc)
    case LetDecl(sym, annotations) =>
      val copy: LocalVarSymbol | TermSymbol = sym match
        case s: LocalVarSymbol => s.subst
        case s: TermSymbol => s.subst
      LetDecl(copy, annotations.map(annotation))(source.toLoc)
    // A record property's identity is not a lexical binding. Its value may bind
    // locals, but selecting this property must still use the resolved field key.
    case f @ RcdField(field, rhs, sym) => located(f, RcdField(term(field), term(rhs), sym)(f.key))
    case s @ RcdSpread(rcd) => located(s, RcdSpread(term(rcd)))
    case DefineVar(sym, rhs) =>
      val copy: LocalSymbol | TermSymbol = sym match
        case s: LocalVarSymbol => s.subst
        case s: LabelSymbol => s.subst
        case s: SplitSymbol => s.subst
        case s: InstSymbol => s.subst
        case s: TermSymbol => s.subst
      DefineVar(copy, term(rhs))(source.toLoc)
    case sc: SetConfig => sc

  def annotation(source: Annot): Annot = source match
    case Annot.Trm(t) => Annot.Trm(term(t))(source.toLoc)
    case Annot.JsSymbol(key) => Annot.JsSymbol(key.copy(path = key.path.map(_.subst))(term(key.term)))(source.toLoc)
    case _ => source

  private def modulefulness(source: Modulefulness): Modulefulness =
    Modulefulness(source.msym.map(_.subst))(source.modified)

  private def parameter(source: Param): Param =
    val copy = Param(source.flags, source.sym.subst, source.sign.map(term), modulefulness(source.modulefulness))(source.toLoc)
    copy.fldSym = source.fldSym.map(_.subst)
    copy.sym.decl = S(copy)
    source.fldSym.toList.flatMap:
      case s: TermSymbol => s :: Nil
      case s: BlockMemberSymbol => s.tsym.toList
      case _ => Nil
    .foreach: field =>
      val fresh = field.subst
      if fresh isnt field then fresh.decl = S(copy)
    copy

  private def parameterList(source: ParamList): ParamList =
    ParamList(source.flags, source.params.map(parameter), source.variadic.map(_.map(parameter)))(source.toLoc)

  private def bindParameters(lists: Ls[ParamList]): Unit =
    lists.foreach(_.allParams.foreach(p => bindLocal(p.sym)))

  private def typeParameter(source: TyParam): TyParam =
    val copy = source.copy(sym = source.sym.subst)(source.toLoc)
    copy.sym.decl = S(copy)
    copy

  private def termDefinition(source: TermDefinition): TermDefinition =
    val scope = nested
    scope.bindParameters(source.params)
    source.tparams.foreach(_.foreach(p => scope.bindLocal(p.sym)))
    val copy = source.copy(sym = source.sym.subst, tsym = source.tsym.subst,
      params = source.params.map(scope.parameterList), tparams = source.tparams.map(_.map(scope.parameter)),
      sign = source.sign.map(scope.term), body = source.body.map(scope.term),
      modulefulness = modulefulness(source.modulefulness), annotations = source.annotations.map(scope.annotation),
      companion = source.companion.map(mapType))(source.toLoc, source.headerLoc, source.scope)
    copy.tsym.defn = S(copy)
    copy.isErroneous = source.isErroneous
    copy

  private def knownDefinition(source: Definition): Opt[Definition] =
    definitions.get(Identity(source)).orElse(outer match
      case parent: Cloner => parent.knownDefinition(source)
      case _ => N)
    .filter(_.sym is source.sym.subst)

  private def definition(source: Definition): Definition = knownDefinition(source).getOrElse {
    val copy = source match
      case source: TermDefinition => termDefinition(source)
      case source: TypeDef =>
        val scope = nested
        source.tparams.foreach(p => scope.bindLocal(p.sym))
        val companion = source.companion.map: companion =>
          definition(companion) match
            case copy: CompanionValue => copy
            case _ => lastWords("A cloned companion must remain a value definition")
        val copy = source.copy(sym = source.sym.subst, bsym = source.bsym.subst,
          tparams = source.tparams.map(scope.typeParameter), rhs = source.rhs.map(scope.term),
          companion = companion, annotations = source.annotations.map(scope.annotation))(source.toLoc, source.headerLoc)
        copy.sym.defn = S(copy)
        copy
      case source: ClassLikeDef =>
        val scope = nested
        source.tparams.foreach(p => scope.bindLocal(p.sym))
        scope.bindParameters(source.paramsOpt.toList ::: source.auxParams)
        scope.prepareLocals(source.body.blk.stats)
        val body = ObjBody(copyMetadata(source.body.blk,
          Blk(source.body.blk.stats.map(scope.statement), scope.term(source.body.blk.res))))
        fieldDefinitions(source).foreach(scope.definition)
        val tparams = source.tparams.map(scope.typeParameter)
        val auxParams = source.auxParams.map(scope.parameterList)
        val annotations = source.annotations.map(scope.annotation)
        val ext = source.ext.map(scope.construction)
        val copy = source match
          case s: ClassDef.Parameterized =>
            val c = s.copy(owner = s.owner.map(_.subst), sym = s.sym.subst, bsym = s.bsym.subst,
              ctorSym = S(s.ctorSym.value.subst), tparams = tparams, params = scope.parameterList(s.params),
              auxParams = auxParams, ext = ext, body = body, companion = s.companion.map(mapClassCompanion),
              annotations = annotations, ctorAnnotations = s.ctorAnnotations.map(scope.annotation))(s.toLoc, s.headerLoc, s.ctorLoc)
            c.sym.defn = S(c)
            c
          case s: ClassDef.Plain =>
            val c = s.copy(owner = s.owner.map(_.subst), sym = s.sym.subst, bsym = s.bsym.subst,
              ctorSym = s.ctorSym.map(_.subst), tparams = tparams, auxParams = auxParams, ext = ext,
              body = body, companion = s.companion.map(mapClassCompanion), annotations = annotations,
              ctorAnnotations = s.ctorAnnotations.map(scope.annotation))(s.toLoc, s.headerLoc, s.ctorLoc)
            c.sym.defn = S(c)
            c
          case s: ModuleOrObjectDef =>
            val c = s.copy(owner = s.owner.map(_.subst), sym = s.sym.subst, bsym = s.bsym.subst,
              tparams = tparams, paramsOpt = s.paramsOpt.map(scope.parameterList), auxParams = auxParams,
              ext = ext, body = body, companion = s.companion.map(mapModuleCompanion), annotations = annotations)(s.path, s.toLoc, s.headerLoc)
            c.sym.defn = S(c)
            c
          case s: PatternDef =>
            s.parameters.foreach(p => scope.bindLocal(p.sym))
            scope.bindPattern(s.pattern)
            val c = s.copy(owner = s.owner.map(_.subst), sym = s.sym.subst, bsym = s.bsym.subst,
              tparams = tparams, parameters = s.parameters.map(scope.parameter),
              patternParams = s.patternParams.map(scope.parameter), extractionParams = s.extractionParams.map(scope.parameter),
              pattern = scope.pattern(s.pattern), annotations = annotations)(s.toLoc, s.headerLoc)
            c.sym.defn = S(c)
            c
        (source.sym, copy.sym) match
          case (old: ClassLikeSymbol, fresh: ClassLikeSymbol) =>
            fresh.irClassHeader = old.irClassHeader.map: header =>
              header.copy(parent = header.parent match
                case codegen.ClassHeader.Parent.Known(sym) => codegen.ClassHeader.Parent.Known(mapType(sym))
                case parent => parent,
                companionClass = header.companionClass.map(_.subst), termCompanion = header.termCompanion.map(_.subst))
          case _ => ()
        copy
    copy.isErroneous = source.isErroneous
    copy.bsym.complete()
    definitions(Identity(source)) = copy
    copy
  }

  private def bindPattern(source: Pattern): Unit = source.variables.symbols.foreach(bindLocal)

  private def pattern(source: Pattern): Pattern =
    import Pattern.*
    val copy = source match
      case source @ Constructor(target, arguments) =>
        val copy = Constructor(term(target), arguments.map(_.map(pattern)))
        copy.resolvedTargets = source.resolvedTargets.map:
          case s: DefinitionSymbol[?] => s.subst
          case s: VarSymbol => s.subst
        copy.isErroneous = source.isErroneous
        copy.shapes.copyFrom(source.shapes)
        copy
      case Composition(polarity, left, right) => Composition(polarity, pattern(left), pattern(right))
      case Negation(inner) => Negation(pattern(inner))
      case Wildcard() => Wildcard()
      case Literal(literal) => Literal(literal)
      case Range(lower, upper, inclusive) => Range(lower, upper, inclusive)
      case Concatenation(left, right) => Concatenation(pattern(left), pattern(right))
      case Tuple(leading, spread) => Tuple(leading.map(pattern), spread.map:
        case (kind, middle, trailing) => (kind, pattern(middle), trailing.map(pattern)))
      case Record(fields) => Record(fields.map((id, value) => id -> pattern(value)))
      case Chain(first, second) => Chain(pattern(first), pattern(second))
      case source @ Alias(inner, id) =>
        val copy = Alias(pattern(inner), id)
        source.symbolOption.foreach(sym => copy.symbol = sym.subst)
        copy
      case Transform(inner, parameters, transform) =>
        val scope = nested
        scope.bindPattern(inner)
        parameters.foreach((_, param) => scope.bindLocal(param))
        Transform(scope.pattern(inner), parameters.map((binding, param) =>
          scope.mapVarSym(binding) -> scope.mapVarSym(param)), scope.term(transform))
      case Annotated(inner, annotations) => Pattern.Annotated(pattern(inner), annotations.map:
        case L(loc) => L(loc)
        case R(value) => R(term(value)))
      case Guarded(inner, guard) => Guarded(pattern(inner), term(guard))
    located(source, copy)

  private def simpleRef(source: SimpleRef): SimpleRef =
    copyMetadata(source, new SimpleRef(mapSimple(source.sym))(source.tree))

  private def scrutinee(source: Ref | SimpleRef): Ref | SimpleRef = term(source) match
    case copy: (Ref | SimpleRef) => copy
    case _ => lastWords("Cloning a scrutinee must preserve its reference form")

  def simpleSplit(source: SimpleSplit): SimpleSplit =
    import SimpleSplit.*
    val copy = source match
      case Cons(head @ Head.Let(binding, value), tail) =>
        val scope = nested
        scope.bindLocal(binding)
        Cons(located(head, Head.Let(scope.mapLocal(binding), term(value))), scope.simpleSplit(tail))
      case Cons(head @ Head.Match(value, pat, consequent), tail) =>
        val scope = nested
        scope.bindPattern(pat)
        Cons(located(head, Head.Match(scrutinee(value), scope.pattern(pat), scope.simpleSplit(consequent))), simpleSplit(tail))
      case e @ Else(default) => Else(term(default))(e.kw)
      case End => End
    located(source, copy)

  private def mapLocal(sym: LocalVarSymbol): LocalVarSymbol = sym.subst

  def flatPattern(source: FlatPattern): FlatPattern =
    val copy = source match
      case FlatPattern.Lit(literal) => FlatPattern.Lit(literal)
      case p @ FlatPattern.ClassLike(constructor, symbol, arguments, refined) =>
        arguments.foreach(_.foreach((sym, _) => bindLocal(sym)))
        val cls: ClassSymbol | ModuleOrObjectSymbol = symbol match
          case s: ClassSymbol => s.subst
          case s: ModuleOrObjectSymbol => s.subst
        FlatPattern.ClassLike(term(constructor), cls,
          arguments.map(_.map((sym, loc) => sym.subst -> loc)), refined)(Tree.Dummy)
      case FlatPattern.Tuple(size, inf) => FlatPattern.Tuple(size, inf)
      case FlatPattern.Record(entries) =>
        entries.foreach((_, sym) => bindLocal(sym))
        FlatPattern.Record(entries.map((id, sym) => id -> sym.subst))
    located(source, copy)

  def branch(source: Branch): Branch =
    val scope = nested
    val pat = scope.flatPattern(source.pattern)
    located(source, Branch(simpleRef(source.scrutinee), pat, scope.split(source.continuation)))

  def split(source: Split): Split =
    val copy = source match
      case Split.Cons(head, tail) => Split.Cons(branch(head), split(tail))
      case Split.Let(sym, value, tail) =>
        val scope = nested
        scope.bindLocal(sym)
        Split.Let(scope.mapLocal(sym), term(value), scope.split(tail))
      case Split.Else(default) => Split.Else(term(default))
      case Split.End => Split.End
      case Split.LetSplit(sym, tail) =>
        val scope = nested
        val fresh = new SplitSymbol(split(sym.body), sym.nme)
        scope.splits(sym) = fresh
        Split.LetSplit(fresh, scope.split(tail))
      case Split.UseSplit(sym) => Split.UseSplit(sym.subst)
    located(source, copy)

  private def construction(source: New): New = term(source) match
    case copy: New => copy
    case _ => lastWords("Cloning a construction must preserve its term form")

  private def element(source: Elem): Elem = source match
    case f: Fld => located(f, f.copy(term = f.term.cloned, asc = f.asc.map(_.cloned)))
    case s: Spd => located(s, s.copy(term = s.term.cloned))

  def term(source: Term): Term =
    def copyResolution(source: Resolvable, copy: Resolvable): copy.type =
      copy.isErroneous = source.isErroneous
      source.expansion.foreach(expansion => copy.expand(expansion.map(_.cloned)))
      copy
    def copySelection(source: Term & AnySel, copy: Term & AnySel): copy.type =
      copy.resolvedTargets = source.resolvedTargets.map:
        case flow.SelectionTarget.ObjectMember(sym) => flow.SelectionTarget.ObjectMember(sym.subst)
        case flow.SelectionTarget.CompanionMember(comp, sym) => flow.SelectionTarget.CompanionMember(comp.cloned, sym.subst)
      copyResolution(source, copy)
    def copyNewResolution(source: NewResolvable, copy: NewResolvable): copy.type =
      copy.resolvedTargets = source.resolvedTargets.map(_.subst)
      copy.keyAccess = source.keyAccess.map(_.cloned)
      copy.isErroneous = source.isErroneous
      copy
    // Keep class qualifiers typed as selections while sharing all clone metadata copying.
    def cloneSel(term: NewSel): NewSel =
      val copy = new NewSel(term.prefix.cloned, term.id, term.cls.map(cloneSel))(term.resSym)
      copy.resolvedMembers = term.resolvedMembers.map(_.subst)
      copy.hasDynamicTarget = term.hasDynamicTarget
      copy.tupleIndex = term.tupleIndex
      copyMetadata(term, copyNewResolution(term, copy))
    val that = source match
      case Error() => Error()
      case UnitVal() => UnitVal()
      case DynTy() => DynTy()
      case Missing => return Missing
      case Lit(lit) => Lit(lit)
      case term @ SimpleRef(sym) => SimpleRef(mapSimple(sym))(term.tree)
      case term @ SelfRef(sym) => SelfRef(sym.subst)(term.tree)
      case term @ MemberRef(sym) => copyNewResolution(term, MemberRef(sym.subst)(term.tree, term.resSym))
      case term @ Super(receiver, owner, id) =>
        return copyMetadata(term, copyNewResolution(term,
          Super(receiver.cloned, owner.subst, id)(term.resSym)))
      case term: NewSel => return cloneSel(term)
      case term @ UnresolvedRef(prefixes, id) =>
        val clonedPrefixes = prefixes.map(_.cloned)
        val copy = UnresolvedRef(clonedPrefixes, id)(term.resSym)
        def cloneReceiver(receiver: Term): Term =
          val index = prefixes.indexWhere(_ is receiver)
          assert(index >= 0, "A wildcard candidate must belong to an opened prefix")
          clonedPrefixes(index)
        copy.resolvedMembers = term.resolvedMembers.map((receiver, member) => cloneReceiver(receiver) -> member.subst)
        copy.dynamicPrefixes = term.dynamicPrefixes.map(cloneReceiver)
        copyNewResolution(term, copy)
      case Capture(base, thru) => Capture(base.cloned, thru.subst)
      case term @ Resolved(t, sym) => copyResolution(term, Resolved(t.cloned, sym.subst)(term.typ))
      case term @ Ref(sym) => copyResolution(term, Ref(sym.subst)(term.tree, term.typ))
      case term @ App(lhs, rhs) =>
        val copy = App(lhs.cloned, rhs.cloned)(term.tree, term.typ, term.resSym)
        copy.callableTargets.shapes.copyFrom(term.callableTargets.shapes)
        copyResolution(term, copy)
      case term @ TyApp(lhs, targs) => copyResolution(term, TyApp(lhs.cloned, targs.map(_.cloned))(term.typ))
      case term @ Sel(prefix, nme) => copySelection(term, Sel(prefix.cloned, nme)(term.sym.map(_.subst), term.resSym, term.typ, term.originalCtx))
      case term @ SynthSel(prefix, nme) => copySelection(term, SynthSel(prefix.cloned, nme)(term.sym.map(_.subst), term.resSym, term.typ, term.originalCtx))
      case term @ LeadingDotSel(nme) =>
        val copy = LeadingDotSel(nme)(term.originalCtx)
        copy.resolvedTargets = term.resolvedTargets.map:
          case flow.SelectionTarget.CompanionMember(comp, sym) => flow.SelectionTarget.CompanionMember(comp.cloned, sym.subst)
        copyResolution(term, copy)
      case DynSel(prefix, fld, arrayIdx, checked) => DynSel(prefix.cloned, fld.cloned, arrayIdx, checked)
      case term @ Tup(fields) =>
        Tup(fields.map(element))(term.tree)
      case Mut(underlying) => underlying.cloned match
        case copy: (Tup | Rcd | New | DynNew) => Mut(copy)
        case _ => lastWords("Cloning must preserve a mutable term's form")
      case term @ CtxTup(fields) =>
        CtxTup(fields.map(element))(term.tree)
      case IfLike(kw, form, split) => IfLike(kw, form, simpleSplit(split))
      case SynthIf(value) => SynthIf(split(value))
      case SynthWhile(value) => SynthWhile(split(value))
      case Lam(params, body) =>
        val scope = nested
        scope.bindParameters(params :: Nil)
        Lam(scope.parameterList(params), scope.term(body))
      case FunTy(lhs, rhs, eff) => FunTy(lhs.cloned, rhs.cloned, eff.map(_.cloned))
      case Forall(tvs, outer, body) =>
        val scope = nested
        (tvs.map(_.sym) ::: outer.toList).foreach(scope.bindLocal)
        Forall(tvs.map(tv => QuantVar(scope.mapVarSym(tv.sym), tv.ub.map(scope.term), tv.lb.map(scope.term))),
          outer.map(scope.mapVarSym), scope.term(body))
      case Constrained(constraints, body) => Constrained(constraints.map(c =>
        located(c, c.copy(lhs = c.lhs.cloned, rhs = c.rhs.cloned))), body.cloned)
      case WildcardTy(in, out) => WildcardTy(in.map(_.cloned), out.map(_.cloned))
      case blk: Blk => return block(blk)
      case term @ Rcd(mut, stats) =>
        val scope = nested
        scope.prepare(stats)
        Rcd(mut, stats.map(scope.statement))
      case Quoted(body) => Quoted(body.cloned)
      case Unquoted(body) => Unquoted(body.cloned)
      case term @ New(cls, args, rft) =>
        val refinement = rft.map: (cs, ob) =>
          val scope = nested
          val declaration = cs.defn.getOrElse(lastWords("An anonymous refinement must have a class declaration"))
          assert(declaration.body.blk is ob.blk, "An anonymous refinement must use its class declaration's body")
          scope.prepare(declaration :: Nil)
          scope.definition(declaration) match
            case copy: ClassDef => copy.sym -> copy.body
            case _ => lastWords("A cloned refinement must remain a class")
        copyResolution(term, New(cls.cloned, args.map(_.cloned), refinement)(term.resSym, term.typ))
      case DynNew(cls, args) => DynNew(cls.cloned, args.map(_.cloned))
      case term @ SelProj(prefix, cls, proj) =>
        copySelection(term, SelProj(prefix.cloned, cls.cloned, proj)(term.sym.map(_.subst), term.resSym, term.typ, term.originalCtx))
      case Asc(term, ty) => Asc(term.cloned, ty.cloned)
      case CompType(lhs, rhs, pol) => CompType(lhs.cloned, rhs.cloned, pol)
      case Neg(rhs) => Neg(rhs.cloned)
      case Region(name, body) =>
        val scope = nested
        scope.bindLocal(name)
        Region(scope.mapVarSym(name), scope.term(body))
      case RegRef(reg, value) => RegRef(reg.cloned, value.cloned)
      case Assgn(lhs, rhs) => Assgn(lhs.cloned, rhs.cloned)
      case Drop(trm) => Drop(trm.cloned)
      case Deref(ref) => Deref(ref.cloned)
      case SetRef(ref, value) => SetRef(ref.cloned, value.cloned)
      case Ret(result) => Ret(result.cloned)
      case Throw(result) => Throw(result.cloned)
      case Label(label, result, body, hasNonLocalContinueDispatch) =>
        val scope = nested
        scope.bindLabel(label)
        scope.bindLocal(result)
        Label(scope.mapLabelSym(label), scope.mapTempSym(result), scope.term(body), hasNonLocalContinueDispatch)
      case Break(label, result, value) => Break(label.subst, result.subst, value.map(_.cloned))
      case Continue(label) => Continue(label.subst)
      case Try(body, finallyDo) => Try(body.cloned, finallyDo.cloned)
      case Annotated(annot, target) => Annotated(annotation(annot), target.cloned)
      case handle @ Handle(lhs, rhs, args, derivedClsSym, defs, body) =>
        val scope = nested
        scope.bindLocal(lhs)
        scope.bindInner(derivedClsSym)
        scope.prepare(derivedClsSym.defn.toList ::: defs.map(_.td))
        val handlers = defs.map: handler =>
          val handlerScope = scope.nested
          handlerScope.bindLocal(handler.resumeSym)
          val definition = handlerScope.termDefinition(handler.td)
          // Abortive handlers also expose these same definitions in their synthetic
          // class body. They are one binding, with the resumption symbol in scope.
          scope.definitions(Identity(handler.td)) = definition
          HandlerTermDefinition(handlerScope.mapVarSym(handler.resumeSym), definition)
        derivedClsSym.defn.foreach(scope.definition)
        Handle(scope.mapLocal(lhs), rhs.cloned, args.map(_.cloned), scope.mapClsSym(derivedClsSym), handlers, scope.term(body))(handle.isAbortive)
    copyMetadata(source, that)
  
end Cloner
