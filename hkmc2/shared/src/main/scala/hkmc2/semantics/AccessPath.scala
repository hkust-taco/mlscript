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

  private def checked(target: DefinitionSymbol[?])(make: => Term)(using state: State): Either[Failure, Term] =
    if (target.getState isnt state) && codegen.MemberStorage.sourcePrivateDefinition(target).nonEmpty
    then L(Failure.PrivateMember(target))
    else R(make)

  private def reference(target: DefinitionSymbol[?])(using State): Either[Failure, Term] = checked(target):
    val member = target.bms.getOrElse(lastWords("An access path requires a block member"))
    val ref = MemberRef(member)(N, FlowSymbol.memSym(member))
    ref.resolvedTargets = target :: Nil
    ref

  private def select(prefix: Term, target: DefinitionSymbol[?])(using State): Either[Failure, Term] = checked(target):
    val member = target.bms.getOrElse(lastWords("An access path requires a block member"))
    val sel = new NewSel(prefix, Tree.Ident(member.nme), N)(FlowSymbol.synthSel(member.nme))
    sel.resolvedTargets = target :: Nil
    sel.resolvedMembers = member :: Nil
    sel

  /** Recover a path to `target` from `src` by walking its enclosing module/object owners
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
  def findAccessPath(src: SrcScope, target: DefinitionSymbol[?])(using state: State): Either[Failure, Term] =
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
    if global || imported then reference(target)
    else scope.toRight(Failure.OutOfScope).flatMap: dst =>
      // Different files may share a prelude scope, but only their exported
      // bindings are available to one another, not their lexical receivers.
      if (target.getState is state) && encloses(dst) then dst.outer.inner match
        case S(owner) => select(SelfRef(owner)(Tree.Ident(owner.nme)), target)
        case N => reference(target)
      else dst.outer.inner match
        case S(owner: ModuleOrObjectSymbol) => findAccessPath(src, owner).flatMap(select(_, target))
        case _ => L(Failure.OutOfScope)

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
    key.path.tail.zipWithIndex.foldLeft(findAccessPath(src, target(key.path.head, key.path.tail.nonEmpty))): (prefix, entry) =>
      val (sym, index) = entry
      prefix.flatMap(select(_, target(sym, index < key.path.length - 2)))
