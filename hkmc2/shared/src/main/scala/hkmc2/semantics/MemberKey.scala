package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** Named source members and well-known JavaScript symbols occupy distinct key spaces.
  * A jsSymbol annotation gives a method a source alias for its symbol-keyed property.
  */
type MemberKey = Str | WellKnownSymbol

enum WellKnownSymbol(val name: Str):
  case Iterator extends WellKnownSymbol("iterator")
  override def toString: Str = s"Symbol.$name"

object MemberKey:
  def index(key: MemberKey): Opt[Int] = key match
    case name: Str => name.toIntOption
    case _: WellKnownSymbol => N

  def symbol(annotations: Ls[Annot]): Opt[WellKnownSymbol] = annotations.collectFirst:
    case Annot.JsSymbol(key) => key

  // Unsupported annotation targets are diagnosed as unused by lowering. They
  // must keep their string property in both lookup and code generation.
  def symbol(definition: TermDefinition): Opt[WellKnownSymbol] =
    if !definition.tsym.isPrivate && (definition.k == syntax.RecordField ||
        definition.k == syntax.Fun && definition.flags.isMethod)
    then symbol(definition.annotations) else N

  def symbol(member: BlockMemberSymbol): Opt[WellKnownSymbol] =
    member.asTrm.flatMap(_.defn).flatMap(td => symbol(td))

  def own(defn: ClassLikeDef, key: MemberKey): Opt[BlockMemberSymbol] = key match
    case name: Str => defn.body.members.get(name)
    case key: WellKnownSymbol =>
      defn.body.methods.find(method => symbol(method).contains(key)).map(_.bsym)
