package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** The aliases expanded at this type's head, in lookup priority order. Ordinary
  * types have no annotation; their constructors and children already describe
  * their namespaces. Each alias occurs once: for a fixed name and lexical scope,
  * trying it again cannot discover a different provider. Repeated Identity[A]
  * forwarding therefore retains one priority step, rather than expansion history.
  * The witness explains this use and does not participate in type identity.
  */
private[semantics] final class TypeNamespaces private (
    val aliases: Ls[TypeAliasSymbol], val witness: NamespaceWitness):
  def through(alias: TypeAliasSymbol, written: NamespaceWitness): TypeNamespaces =
    new TypeNamespaces(alias :: aliases.filterNot(_ is alias), written)

  /** Outer aliases take priority; their occurrences in the inner path add no
    * further fallback. Boolean components retain their own independent paths.
    */
  def precededBy(outer: TypeNamespaces): TypeNamespaces =
    new TypeNamespaces(outer.aliases ::: aliases.filterNot(outer.aliases.contains), outer.witness)

private[semantics] object TypeNamespaces:
  def single(alias: TypeAliasSymbol, witness: NamespaceWitness): TypeNamespaces =
    new TypeNamespaces(alias :: Nil, witness)
