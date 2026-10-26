package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import Term.*


/** Implementation dependencies of the exposed interface. Exposure alone is
  * insufficient: an unexposed private helper can still carry a public call's
  * arguments and results. Follow complete reachable bodies, including dormant
  * branches, rather than just the candidates observed while checking the unit.
  * Unknown synthetic owners are kept conservatively.
  */
private[semantics] final class ResolutionReachability(block: Blk, owner: Elaborator.State,
    sourceOwners: collection.Map[Symbol, Opt[AnyDefinitionSymbol]]):
  private val definitions = mutable.Set.empty[AnyDefinitionSymbol]
  private val codeOf = mutable.Map.empty[Identity[Statement | Pattern | Symbol], Opt[AnyDefinitionSymbol]]
  private val indexed = mutable.Set.empty[Identity[Statement]]
  private val reached = mutable.Set.empty[Identity[Statement]]
  private val live = mutable.Set.empty[AnyDefinitionSymbol]

  private def symbolOf(definition: Definition): AnyDefinitionSymbol = definition match
    case term: TermDefinition => term.tsym
    case definition: ClassLikeDef => definition.sym
    case definition: TypeDef => definition.sym

  private def index(statement: Statement, enclosing: Opt[AnyDefinitionSymbol]): Unit =
    if indexed.add(new Identity(statement)) then
      val code = statement match
        case definition: Definition =>
          val symbol = symbolOf(definition)
          definitions += symbol
          S(symbol)
        case _ => enclosing
      def symbol(symbol: Symbol): Unit = codeOf.getOrElseUpdate(new Identity(symbol), code)
      def parameters(parameters: ParamList): Unit = parameters.allParams.foreach(param => symbol(param.sym))
      statement match
        case definition: TermDefinition =>
          symbol(definition.tsym)
          definition.params.foreach(parameters)
          definition.tparams.foreach(_.foreach(param => symbol(param.sym)))
        case definition: ClassLikeDef =>
          symbol(definition.sym)
          definition.paramsOpt.foreach(parameters)
          definition.auxParams.foreach(parameters)
          definition.tparams.foreach(param => symbol(param.sym))
        case definition: TypeDef =>
          symbol(definition.sym)
          definition.tparams.foreach(param => symbol(param.sym))
        case LetDecl(binding, _) => symbol(binding)
        case DefineVar(binding, _) => symbol(binding)
        case Lam(params, _) => parameters(params)
        case application: App => symbol(application.resSym)
        case creation: New => symbol(creation.resSym)
        case ref: MemberRef => symbol(ref.resSym)
        case sel: NewSel => symbol(sel.resSym)
        case ref: UnresolvedRef => symbol(ref.resSym)
        case sup: Super => symbol(sup.resSym)
        case _ => ()
      codeOf(new Identity(statement)) = code
      def pattern(pat: Pattern): Unit =
        codeOf(new Identity(pat)) = code
        ResolutionSources.patternChildren(pat)(index(_, code), pattern)
      ResolutionSources.children(statement)(index(_, code), pattern)
  index(block, N)

  private def enclosing(source: Statement | Pattern | Symbol): Opt[AnyDefinitionSymbol] =
    codeOf.get(new Identity(source)).orElse(source match
      case symbol: Symbol => sourceOwners.get(symbol)
      case _ => N).flatten

  private def reference(symbol: Symbol): Unit = if symbol.getState is owner then
    symbol match
      case member: BlockMemberSymbol => member.symbols.foreach(reference)
      case symbol: AnyDefinitionSymbol =>
        if live.add(symbol) then
          enclosing(symbol).filterNot(_ == symbol).foreach(reference)
          symbol.defn.foreach(body)
      case _ => enclosing(symbol).foreach(reference)

  private def body(definition: Definition): Unit =
    live += symbolOf(definition)
    definition match
      case cls: ClassLikeDef =>
        cls.body.blk.stats.collect:
          case definition: Definition if InterfaceExposure.isPublic(definition) => definition.bsym
        .foreach(reference)
        cls match
          case cls: ClassDef => cls.ctorSym.foreach(reference)
          case _ => ()
      case _ => ()
    visit(definition, enterDefinition = true)

  private def visit(statement: Statement, enterDefinition: Bool): Unit = statement match
    case definition: Definition if !enterDefinition => definition match
      // Initializers may feed a captured variable or an instance field. Functions
      // and nested classes enter the graph only through a reference or exposure.
      case term: TermDefinition if term.k != syntax.Fun => reference(term.tsym)
      case _ => ()
    case _ if reached.add(new Identity(statement)) =>
      statement match
        case term: AnyRef_ => reference(term.sym)
        case _ => ()
      statement match
        case ref: NewResolvable => ref.resolvedTargets.foreach(reference)
        case Capture(_, through) => reference(through)
        case definition: ClassLikeDef => definition.owner.foreach(reference)
        case definition: TypeDef => definition.owner.foreach(reference)
        case definition: TermDefinition => definition.owner.foreach(reference)
        case Handle(_, _, _, symbol, _, _) => reference(symbol)
        case _ => ()
      def pattern(pat: Pattern): Unit = ResolutionSources.patternChildren(pat)(visit(_, false), pattern)
      ResolutionSources.children(statement)(visit(_, false), pattern)
    case _ => ()

  def follow(exports: Ls[BlockMemberSymbol], exposed: ResolutionRetention): Unit =
    exports.foreach(reference)
    exposed.exposedDefinitions.foreach(reference)
    exposed.exposedValues.foreach: value =>
      codeOf.get(new Identity(value.value)).flatten.foreach(reference)
      visit(value.value, false)
    visit(block, false)

  def include(symbol: AnyDefinitionSymbol): Unit = reference(symbol)
  def keeps(symbol: AnyDefinitionSymbol): Bool = live(symbol) ||
    !definitions(symbol) && enclosing(symbol).filterNot(_ == symbol).forall(keeps)
  def keepsSource(source: Statement | Pattern | Symbol): Bool =
    enclosing(source).forall(keeps)
