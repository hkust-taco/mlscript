package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** The namespace behavior of a type use, independently of its interface. Each path tries
  * aliases in order before reaching a class, an inference input, or a still-deferred type.
  * Paths contribute independently, as the components of a union or intersection do.
  *
  * A reference has one name and lexical scope: trying the same alias again cannot change
  * whether its companion or declaring module provides that name. Keeping only its first
  * occurrence bounds a path by the number of declarations, even for Identity[Identity[A]].
  * Witnesses explain a use; they do not distinguish its namespace behavior.
  */
private[semantics] final class TypeNamespaces private (
    val paths: Ls[(TypeNamespaces.Path, NamespaceWitness)]):
  import TypeNamespaces.*
  val key: Set[Path] = paths.iterator.map(_._1).toSet
  def types: Iterator[DeclaredType] = paths.iterator.flatMap:
    case (Path(_, S(Target.Type(tpe))), _) => Iterator.single(tpe.tpe)
    case _ => Iterator.empty

  def union(that: TypeNamespaces): TypeNamespaces =
    new TypeNamespaces(paths ::: that.paths.filterNot((path, _) => key(path)))

  def through(alias: Opt[TypeAliasSymbol], witness: NamespaceWitness): TypeNamespaces =
    val bodies = if paths.isEmpty then (Path(Nil, N) -> witness) :: Nil else paths
    val prefixed = bodies.map: (path, _) =>
      Path(alias.fold(path.aliases)(a => a :: path.aliases.filterNot(_ is a)), path.target) -> witness
    TypeNamespaces.distinct(prefixed)

  def mapTypes(f: DeclaredType => DeclaredType): TypeNamespaces = TypeNamespaces.distinct(paths.map:
    case (Path(aliases, S(Target.Type(tpe))), witness) =>
      Path(aliases, S(Target.Type(f(tpe.tpe).observation))) -> witness
    case entry => entry)

private[semantics] object TypeNamespaces:
  enum Target:
    case Class(definition: ClassLikeDef)
    case Type(tpe: DeclaredType.Observation)
  final case class Path(aliases: Ls[TypeAliasSymbol], target: Opt[Target])

  val empty: TypeNamespaces = new TypeNamespaces(Nil)
  def target(target: Target, witness: NamespaceWitness): TypeNamespaces =
    new TypeNamespaces((Path(Nil, S(target)) -> witness) :: Nil)
  private def distinct(paths: Ls[(Path, NamespaceWitness)]): TypeNamespaces =
    val seen = scala.collection.mutable.HashSet.empty[Path]
    new TypeNamespaces(paths.filter((path, _) =>
      (path.aliases.nonEmpty || path.target.nonEmpty) && seen.add(path)))
