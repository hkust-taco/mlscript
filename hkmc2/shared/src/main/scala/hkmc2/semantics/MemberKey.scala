package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** Named source members and fresh values occupy distinct key spaces.
  * A jsSymbol annotation gives a method a source name for its computed property.
  */
type MemberKey = Str | SymbolKey

/** The identity includes the receiver: two instances' fresh fields need not hold
  * the same value. The source expression is retained for diagnostics, but locations
  * and capture wrappers do not participate in member-key equality.
  */
final case class SymbolKey(path: Ls[Symbol])(val term: Term):
  def name: Str = path.map(_.nme).mkString(".")
  override def toString: Str = name

object MemberKey:
  def index(key: MemberKey): Opt[Int] = key match
    case name: Str => name.toIntOption
    case _: SymbolKey => N

  def symbol(annotations: Ls[Annot]): Opt[SymbolKey] = annotations.collectFirst:
    case Annot.JsSymbol(key) => key

  // Unsupported annotation targets are diagnosed as unused by lowering. They
  // must keep their string property in both lookup and code generation.
  def symbol(definition: TermDefinition): Opt[SymbolKey] =
    if !definition.tsym.isPrivate && (definition.k == syntax.RecordField ||
        definition.k == syntax.Fun && definition.flags.isMethod)
    then symbol(definition.annotations) else N

  def symbol(member: BlockMemberSymbol): Opt[SymbolKey] =
    member.asTrm.flatMap(_.defn).flatMap(td => symbol(td))

  def own(defn: ClassLikeDef, key: MemberKey): Opt[BlockMemberSymbol] = key match
    case name: Str => defn.body.members.get(name)
    case key: SymbolKey =>
      defn.body.methods.find(method => symbol(method).contains(key)).map(_.bsym)
