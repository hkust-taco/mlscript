package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import Elaborator.State
import Term.*
import syntax.Tree

/** Recover an expression for an implicit reference from its use site's lexical
  * scope. As with companion-module references in the legacy flow resolver, a
  * module can supply a path to its members, but a function or local block cannot.
  * Imported file bindings use the existing compilation-unit linkage.
  */
object AccessPath:
  enum Failure:
    case OutOfScope
    case PrivateMember(member: DefinitionSymbol[?])

  /** The binding at the start of a path, available where the path is used. */
  private enum Base:
    /** A reference to `target`, bound in `binding`, or at file or global level if `binding` is absent. */
    case Reference(target: DefinitionSymbol[?], binding: Opt[SrcScope])
    /** The receiver of `owner`'s body, which is the scope `binding`. */
    case Receiver(owner: InnerSymbol, binding: SrcScope)

  /** A path is planned before any of its terms is built, so that an inaccessible step
    * leaves no partially built path behind (building a value path registers resolution).
    */
  private final case class Plan(base: Base, selections: Ls[DefinitionSymbol[?]])

  private def checked(target: DefinitionSymbol[?])(using state: State): Either[Failure, Unit] =
    if (target.getState isnt state) && codegen.MemberStorage.sourcePrivateDefinition(target).nonEmpty
    then L(Failure.PrivateMember(target))
    else R(())

  private def select(plan: Plan, target: DefinitionSymbol[?])(using State): Either[Failure, Plan] =
    checked(target).map(_ => plan.copy(selections = plan.selections :+ target))

  private def member(target: DefinitionSymbol[?]): BlockMemberSymbol =
    target.bms.getOrElse(lastWords("An access path requires a block member"))

  /** Plan a path to `target` from `src` by walking its enclosing module/object owners
    * until reaching a binding available in `src`. For a member declared in [scp2] here,
    * [scp1] is the outermost accessible base:
    * {{{
    *     [scp0]
    *     fun foo =
    *       [scp1]
    *       module Foo with
    *         module Bar with
    *           [scp2]
    * }}}
    * From [scp1], the path to that member is `Foo.Bar.member`. [scp0] cannot access
    * [scp2] because there is a function scope on the way: the owner walk cannot
    * obtain the local binding of `Foo` from outside an invocation of `foo`.
    * The same would happen for:
    * {{{
    *     [scp0]
    *     if ... then // LocalScope also blocks access to [scp1] and [scp2]
    *       [scp1]
    *       module Foo with
    *         module Bar with
    *           [scp2]
    * }}}
    * This restriction prevents entering an inaccessible scope; it does not prevent
    * nested functions from capturing bindings in their enclosing scopes. `encloses`
    * recognizes those bindings before the owner walk is needed. Imported file bindings
    * and global declarations can also provide the base of a path directly.
    */
  private def plan(src: SrcScope, target: DefinitionSymbol[?])(using state: State): Either[Failure, Plan] =
    def encloses(dst: SrcScope): Bool =
      def loop(scope: SrcScope): Bool = (scope is dst) || scope.parent.exists(loop)
      loop(src)
    val scope = target.defn.flatMap:
      case td: TermDefinition => td.scope
      case md: ModuleOrObjectDef => S(md.path)
      case _ => N
    val imported = target.bms.exists: sym =>
      sym.getState.externalModuleImport(sym, state) match
        case S(_: Elaborator.ExternalModuleImport.Default) => true
        case S(_: Elaborator.ExternalModuleImport.Private) => sym.getState.compilationUnitPrivateName(sym).nonEmpty
        case N => false
    val global = scope.exists(_.outer.inner.isEmpty) && target.defn.exists(_.hasDeclareModifier.nonEmpty)
    if global || imported then checked(target).map(_ => Plan(Base.Reference(target, N), Nil))
    else scope.toRight(Failure.OutOfScope).flatMap: dst =>
      // Different files may share a prelude scope, but only their exported
      // bindings are available to one another, not their lexical receivers.
      if (target.getState is state) && encloses(dst) then dst.outer.inner match
        case S(owner) => checked(target).map(_ => Plan(Base.Receiver(owner, dst), target :: Nil))
        case N => checked(target).map(_ => Plan(Base.Reference(target, S(dst)), Nil))
      else dst.outer.inner match
        case S(owner: ModuleOrObjectSymbol) => plan(src, owner).flatMap(select(_, target))
        case _ => L(Failure.OutOfScope)

  /** A path whose targets are already known, for operands recovered after member
    * resolution has finished. It adds no flow edges and needs no lexical captures.
    */
  private def resolvedPath(plan: Plan)(using State): Term =
    val base: Term = plan.base match
      case Base.Reference(target, _) =>
        val bms = member(target)
        val ref = MemberRef(bms)(N, FlowSymbol.memSym(bms))
        ref.resolvedTargets = target :: Nil
        ref
      case Base.Receiver(owner, _) => SelfRef(owner)(Tree.Ident(owner.nme))
    plan.selections.foldLeft(base): (prefix, target) =>
      val bms = member(target)
      val sel = new NewSel(prefix, Tree.Ident(bms.nme), N)(FlowSymbol.synthSel(bms.nme))
      sel.resolvedTargets = target :: Nil
      sel.resolvedMembers = bms :: Nil
      sel

  def findAccessPath(src: SrcScope, target: DefinitionSymbol[?])(using State): Either[Failure, Term] =
    plan(src, target).map(resolvedPath)

  /** Like `findAccessPath`, but the recovered expression is resolved as if it had been
    * written in `src`, so that it can supply values to the inference graph. Elaboration
    * wraps a reference in one `Capture` per resolution boundary between its binding and
    * its use (see doc/new-resolution-scopes.md); the base of the path receives the same
    * captures, and its selections are resolved like written ones. `binders` are the
    * type binders in scope at `src`, which by-name definitions on the path can read.
    * Unlike written references, the path is not an access site (see
    * ResolutionContext.checkAccess): its user did not name these definitions, and
    * planning has already excluded the private members of other files.
    */
  def valuePath(src: SrcScope, target: DefinitionSymbol[?], binders: Set[VarSymbol])
      (using State, NewResolver, ResolutionContext): Either[Failure, Term] =
    def captured(base: Term, scope: SrcScope, binding: Opt[SrcScope]): Term =
      if binding.exists(_ is scope) then base
      else
        val outer = scope.parent.fold(base)(captured(base, _, binding))
        scope.outer.resolutionBoundary.fold(outer)(Capture(outer, _))
    def withBinders(term: NewResolvable): term.type =
      rctx.recordLexicalBinders(term, binders)
      term
    plan(src, target).map: plan =>
      val base: Term = plan.base match
        case Base.Reference(target, binding) =>
          val bms = member(target)
          captured(withBinders(MemberRef(bms)(N, FlowSymbol.memSym(bms))), src, binding)
        case Base.Receiver(owner, binding) => captured(SelfRef(owner)(Tree.Ident(owner.nme)), src, S(binding))
      plan.selections.foldLeft(base): (prefix, target) =>
        val bms = member(target)
        val sel = withBinders(new NewSel(prefix, Tree.Ident(bms.nme), N)(FlowSymbol.synthSel(bms.nme)))
        summon[NewResolver].newSel(sel, src)
        sel

  /** The key's symbol identity remains unchanged. Only the runtime expression is
    * recovered here, after member resolution has finished; it adds no flow edges.
    */
  def symbolKey(src: SrcScope, key: SymbolKey)(using State): Either[Failure, Term] =
    def target(sym: Symbol, receiver: Bool): DefinitionSymbol[?] = sym match
      case bms: BlockMemberSymbol =>
        (if receiver then bms.asMod.orElse(bms.asTrm) else bms.asTrm).getOrElse(
          lastWords("A validated symbol path must denote a module or immutable val"))
      case sym: TermSymbol => sym
      case sym: ModuleOrObjectSymbol => sym
      case _ => lastWords("Invalid symbol path root")
    key.path.tail.zipWithIndex.foldLeft(plan(src, target(key.path.head, key.path.tail.nonEmpty))): (prefix, entry) =>
      val (sym, index) = entry
      prefix.flatMap(select(_, target(sym, index < key.path.length - 2)))
    .map(resolvedPath)
