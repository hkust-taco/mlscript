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
  def isExternal(d: Definition): Bool = d.hasDeclareModifier.nonEmpty || (d match
    case td: TermDefinition => td.owner.exists(_.asDefnSym.defn.exists(isExternal))
    case cd: ClassLikeDef => cd.owner.exists(_.asDefnSym.defn.exists(isExternal))
    case _ => false)

  def isOpen(d: TermDefinition): Bool = d.body.isEmpty || hasModifier(d, Keyword.`open`)

  /** Symbol states identify compilation units, including all blocks of a worksheet. Source
    * locations cannot establish this boundary: generated classes may have no source location,
    * and imported aliases must retain the defining class's unit rather than the alias's unit.
    */
  def validateParent(child: ClassLikeDef, parent: ClassLikeDef, site: Term.New)(using Erasure, Raise): Unit =
    if parent.isInstanceOf[ClassDef] && (parent.sym.getState isnt child.sym.getState) &&
        !hasModifier(parent, Keyword.`open`) && !hasModifier(parent, Keyword.`abstract`) then
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

  /** Check only completed edges; an empty list during resolution can still acquire a parent. */
  def validateMember(td: TermDefinition)(using Erasure, Raise): Unit =
    val bases = td.tsym.overriddenMembers
    def fail(message: Message, base: Opt[TermSymbol]): Unit = raise(ErrorReport(
      (message -> td.toLoc) :: base.toList.map(sym => msg"Inherited member '${sym.nme}' is defined here" -> sym.toLoc),
      source = Diagnostic.Source.Compilation))
    if hasModifier(td, Keyword.`override`) && bases.isEmpty then
      fail(msg"Member '${td.tsym.nme}' is marked 'override' but overrides no inherited member", N)
    bases.foreach: base =>
      base.defn.foreach: inherited =>
        if !isOpen(inherited) then
          fail(msg"Cannot override non-open member '${base.nme}'", S(base))
        else if inherited.body.nonEmpty && !hasModifier(td, Keyword.`override`) then
          fail(msg"Overriding member '${base.nme}' requires the 'override' modifier", S(base))
        if td.tsym.isPrivate then
          fail(msg"Overriding member '${base.nme}' cannot be private", S(base))
        // Getter evaluation and method selection have different effects and calling conventions.
        // A shared target symbol must never cause a getter read to be treated as a pure method value.
        if !isExternal(td) && (td.k != inherited.k ||
            td.params.nonEmpty != inherited.params.nonEmpty) then
          fail(msg"Overriding member '${base.nme}' must preserve whether the member is a field, getter, or method", S(base))
