package hkmc2
package semantics

import scala.collection.mutable
import hkmc2.utils.*, shorthands.*
import syntax.Keyword
import hkmc2.Message.MessageContext
import codegen.Erasure

/** Declaration edges are separate from callable shapes: selecting a base declaration must
  * not replace the implementation flow inferred for an ordinary virtual selection.
  */
private[semantics] final class OverrideLinks extends Host[TermSymbol]:
  def showDbg(using DebugPrinter): Str = "overridden members"
  def members(using Erasure): Ls[TermSymbol] = shapes.toList

object Inheritance:
  def hasModifier(d: Definition, keyword: Keyword.Modifier): Bool = d.annotations.exists:
    case Annot.Modifier(kw) => kw == keyword
    case _ => false

  def isAbstract(d: TermDefinition): Bool =
    d.body.isEmpty && !isExternal(d) && !d.tsym.isInstanceOf[ClassCtorSymbol]

  /** A foreign declaration also supplies the implementation of its nested declarations. */
  def isExternal(d: Definition): Bool = d.hasDeclareModifier.nonEmpty || d.match
    case td: TermDefinition => td.owner.exists(_.asDefnSym.defn.exists(isExternal))
    case cd: ClassLikeDef => cd.owner.exists(_.asDefnSym.defn.exists(isExternal))
    case _ => false

  def isOpen(d: TermDefinition): Bool = d.body.isEmpty || hasModifier(d, Keyword.`open`)

  /** Whether other compilation units may extend `cls`: only `open` and `abstract` classes allow it.
    * Objects cannot be extended yet, but an `open` object marks the same intent for its members.
    */
  def isExtensible(cls: ClassLikeDef): Bool =
    hasModifier(cls, Keyword.`open`) || hasModifier(cls, Keyword.`abstract`)
  
  /** Symbol states identify compilation units, including all blocks of a worksheet. Source
    * locations cannot establish this boundary: generated classes may have no source location,
    * and imported aliases must retain the defining class's unit rather than the alias's unit.
    */
  def validateParent(child: ClassLikeDef, parent: ClassLikeDef, site: Term.New)(using Erasure, Raise): Unit =
    if parent.isInstanceOf[ClassDef] && (parent.sym.getState isnt child.sym.getState) && !isExtensible(parent) then
      raise(ErrorReport(
        msg"Cannot extend sealed class '${parent.sym.nme}' outside its compilation unit" -> site.toLoc ::
          (msg"Class '${parent.sym.nme}' is defined here; declare it 'open' or 'abstract' to allow external subclasses" -> parent.toLoc) :: Nil,
        source = Diagnostic.Source.Compilation))

  /** An ancestor may itself be a target (one receiver overrides a member, another inherits it).
    * Discard less-specific common ancestors, so a chain of overrides is not an ambiguity.
    */
  def commonMember(targets: Ls[DefinitionSymbol[?]])(using Erasure): Opt[DefinitionSymbol[?]] =
    def ancestors(sym: DefinitionSymbol[?]): Set[DefinitionSymbol[?]] =
      val seen = mutable.Set.empty[DefinitionSymbol[?]]
      def visit(current: DefinitionSymbol[?]): Unit = if seen.add(current) then
        current.overriddenMembers.foreach(visit)
      visit(sym)
      seen.toSet
    targets.distinct match
      case Nil => N
      case target :: Nil => S(target)
      case first :: rest =>
        val common = rest.foldLeft(ancestors(first))((acc, sym) => acc intersect ancestors(sym))
        common.filterNot(base => common.exists(other => (other isnt base) && ancestors(other)(base))).toList match
          case target :: Nil => S(target)
          case _ => N

  /** Whether an override of `inherited` uses a different kind of definition, such as a `fun` overriding
    * a `val`, or a `mut val` overriding a `val`. A value is computed once when its object is constructed,
    * a mutable value can also be reassigned, and a function is evaluated on each access, so a selection
    * typed through the inherited member would assume the wrong evaluation. Functions with different
    * parameter lists, including a function without any overriding one with a parameter list, are
    * rejected by [[codegen.OverrideLayout]]'s parameter list comparison.
    */
  def changesMemberKind(td: TermDefinition, inherited: TermDefinition): Bool = td.k != inherited.k
  
  /** Check only completed edges; an empty list during resolution can still acquire a parent. */
  def validateMember(td: TermDefinition)(using Erasure, Raise): Unit =
    val bases = td.tsym.overriddenMembers
    def fail(message: Message, base: Opt[TermSymbol]): Unit = raise(ErrorReport(
      (message -> td.toLoc) :: base.toList.map(sym => msg"Inherited member '${sym.nme}' is defined here" -> sym.toLoc),
      source = Diagnostic.Source.Compilation))
    if hasModifier(td, Keyword.`override`) && bases.isEmpty then
      fail(msg"Member '${td.tsym.nme}' is marked 'override' but overrides no inherited member", N)
    // Private members are never overridden: a subclass member with the same name is a distinct member.
    if hasModifier(td, Keyword.`open`) && td.owner.isDefined && td.tsym.isExplicitlyPrivate then
      raise(WarningReport(msg"Private member '${td.tsym.nme}' cannot be overridden, so 'open' has no effect" -> td.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
    bases.foreach: base =>
      base.defn.foreach: inherited =>
        if !isOpen(inherited) then
          fail(msg"Cannot override non-open member '${base.nme}'", S(base))
        else if inherited.body.nonEmpty && !hasModifier(td, Keyword.`override`) then
          fail(msg"Overriding member '${base.nme}' requires the 'override' modifier", S(base))
        if td.tsym.isPrivate then
          fail(msg"Overriding member '${base.nme}' cannot be private", S(base))
        if changesMemberKind(td, inherited) then
          fail(msg"Overriding member '${base.nme}' is a ${td.k.desc}, but the member it overrides is a ${inherited.k.desc}", S(base))
        // Mixing a data property with an inherited accessor changes initialization and freezing behavior.
        if (td.k is syntax.MutVal) && (inherited.k is syntax.MutVal) &&
            td.annotations.exists(_.isInstanceOf[Annot.PlainField]) !=
              inherited.annotations.exists(_.isInstanceOf[Annot.PlainField]) then
          fail(msg"Overriding mutable field '${base.nme}' must preserve the @js.plainField annotation", S(base))
