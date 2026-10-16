package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*


/** The runtime binding shared by the interpretations of a member name in JavaScript-like backends.
  * Explicit function companions carry the class value as a field of the function.
  * Otherwise, the IR class owns its binding, including its generated constructor and companion module.
  * Private bindings need distinct storage so they cannot replace inherited public properties with the same name.
  */
object MemberStorage:
  
  def symbol(sym: AnyDefinitionSymbol): AnyDefinitionSymbol = sym match
    case ctor: ClassCtorSymbol => symbol(ctor.associatedCls)
    case cls: BaseTypeSymbol => cls.irTermCompanion match
      case S(_: ClassCtorSymbol) | N => cls.irClassContainer.asDefnSym
      case S(term) => term
    case _ => sym
  
  /** An absent owner denotes ordinary public/local storage. Read current IR definitions so
    * copied classes and synthetic modules do not depend on stale semantic definitions.
    * For the symbols that still have source definitions, this must agree with `sourcePrivateDefinition`. */
  def privateOwner(sym: AnyDefinitionSymbol)(using Raise, Config): Opt[InnerSymbol] =
    val stored = symbol(sym)
    val owner = stored match
      case term: TermSymbol => term.owner.filter(_ => term.isPrivate)
      case cls: InnerSymbol => cls.asDefnSym.irClsLikeDefn.flatMap: definition =>
        if (definition.visibility is Visibility.Private)
        && definition.companion.forall(_.visibility is Visibility.Private)
        then definition.owner.filterNot(_.isInstanceOf[TopLevelSymbol])
        else N
      case _ => N
    if config.checkInvariants && sym.defn.isDefined then
      // A class-like binding without an IR definition, such as a foreign declaration's, has no storage to compare.
      val decided = stored match
        case cls: InnerSymbol => cls.asDefnSym.irClsLikeDefn.isDefined
        case _ => true
      if decided then softAssert(owner.isDefined === sourcePrivateDefinition(sym).isDefined,
        s"The runtime storage of '${sym.nme}' is ${if owner.isDefined then "private" else "public"
          }, unlike what its source definitions imply")
    owner
  
  /** The counterpart of `privateOwner` for code that runs before lowering, when IR definitions do not exist yet:
    * the source definition of `sym` if `sym` is stored privately. ResolutionContext.checkAccess uses it to reject
    * the references that lowering would compile to property accesses, which cannot reach private storage.
    * All the definitions of a member name share its runtime binding (see `symbol`), except type aliases,
    * which have no runtime storage, so this binding is private when all these definitions are private.
    * `privateOwner` instead reads the visibility of the IR definition that owns the binding. The two agree only
    * thanks to the following invariants, which `privateOwner` checks for the symbols that have source definitions
    * when `Config.checkInvariants` is set:
    * - a public class or module cannot have a private companion, so a private function companion implies that the
    *   class-like definitions of its name are private; Elaborator marks the definitions of the names it rejects
    *   for this reason as erroneous, and these are not compiled (see `Lowering.erroneousRef`);
    * - the definition of a class's constructor function carries the visibility modifiers of the class (see Elaborator);
    * - lowering copies visibility modifiers onto IR definitions,
    *   including onto the class that it creates for a standalone module (see Lowering).
    */
  def sourcePrivateDefinition(sym: AnyDefinitionSymbol): Opt[Definition] =
    def privatelyStored(definition: Definition, owner: Opt[InnerSymbol]): Opt[Definition] = owner match
      case S(_: TopLevelSymbol) | N => N
      case S(_) =>
        val stored = definition.bsym.symbols.filter:
          case _: TypeAliasSymbol => false
          case _ => true
        Option.when(stored.nonEmpty && stored.forall(_.defn.exists(_.visibility is Visibility.Private)))(definition)
    sym match
      case ctor: ClassCtorSymbol => sourcePrivateDefinition(ctor.associatedCls)
      case member: TermSymbol => member.defn.flatMap(privatelyStored(_, member.owner))
      case member: InnerSymbol => member.asDefnSym.defn.flatMap(definition => privatelyStored(definition, definition.owner))
      case _ => N
  
end MemberStorage
