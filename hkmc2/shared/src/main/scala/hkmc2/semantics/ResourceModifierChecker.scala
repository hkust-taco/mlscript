package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import Elaborator.{Ctx, State}
import Message.MessageContext

/** Representation checks shared by both resolvers. The supplied symbol lookup reads
  * legacy resolved references, or completed new-resolution targets during erasure.
  */
final class ResourceModifierChecker(symbolOf: Term => Opt[Symbol])(using Ctx, State, Raise):
  /** The types that a resource modifier wrapping `t` applies to, as `ErasedType.eraseSign` reads them. */
  private def rscReach(t: Term): Ls[Term] = t match
    case Term.CompType(lhs, rhs, true) => rscReach(lhs) ::: rscReach(rhs)
    case Term.Forall(_, _, body) => rscReach(body)
    case Term.Capture(base, _) => rscReach(base)
    case _ => t :: Nil
  
  /**
   * The members that the type `t` denotes: those of the alias it refers to, the type itself, or none if the type does
   * not have a symbol (such as a function type or an intersection).
   */
  private def aliasMembers(t: Term): Ls[codegen.CanonicalErasedValueType.AliasMember] =
    symbolOf(t).flatMap(_.asTpe).toList.flatMap(codegen.CanonicalErasedValueType.resolveTpeSymAlias(_, symbolOf))
  
  /**
   * Checks a type that a resource modifier denoting `rsc` applies to is valid: it must not denote a primitive type
   * (directly or through an alias). This is an error under `rsc`, and a warning under `rsc?`, which then has no effect.
   *
   * A member of a union, written or through an alias, combines its own modifier with `rsc`.
   */
  private def checkRscTarget(t: Term, rsc: Opt[Bool]): Unit = t match
    // A union member with a modifier of its own is already checked under that modifier. It is checked again only when
    // this modifier is `rsc` and the member's is not, as this one then overrides it.
    case Term.Annotated(Annot.Resource(own), target) =>
      if rsc === S(true) && own =/= S(true) then
        rscReach(target).filter(codegen.ErasedType.keepsRsc(_, own, symbolOf)).foreach(checkRscTarget(_, rsc))
    // An erroneous type, or a reference to a non-type, is already reported. A type parameter has nothing to check.
    case Term.Error() => ()
    case _ if symbolOf(t).exists(_.asTpe.isEmpty) => ()
    // A modifier that erasure would silently drop is rejected.
    case _ if !codegen.ErasedType.keepsRsc(t, rsc, symbolOf) =>
      raise(ErrorReport(msg"Resource modifiers on this type are not supported yet." -> t.toLoc :: Nil))
    case _ =>
      val members = aliasMembers(t)
      // A member is checked here when this modifier decides its resource-ness: always under `rsc`, which overrides the
      // member's own modifier, unless that is `rsc` too. Otherwise, the member's own modifier decides it, and is
      // checked where its alias is defined.
      val decided = members.filter(m => m.ownRsc.isEmpty || rsc === S(true) && m.ownRsc =/= S(S(true)))
      val prims = decided.flatMap(_.sym).flatMap(codegen.PrimitiveType.of).distinct
      prims.foreach: prim =>
        val nme = prim.sym.nme
        rsc match
        case S(true) =>
          raise(ErrorReport(msg"Primitive type '${nme}' cannot be a resource." -> t.toLoc :: Nil))
        case N =>
          raise(WarningReport(
            msg"Primitive type '${nme}' is never a resource, so 'rsc?' has no effect." -> t.toLoc :: Nil))
        // No syntax writes a non-resource modifier.
        case S(false) => lastWords(s"a resource modifier denoting a non-resource on '$t'")
  
  /**
   * Checks a resource modifier denoting `rsc` on `target`:
   *
   * - a type takes at most one modifier written directly on it (e.g. `rsc rsc? C`), while one on a union's member or
   *   inside an alias combines with it instead;
   * - `rsc?` has no effect on a type whose members are all resources of their own, so it is reported as a warning.
   *
   * Also see `checkRscTarget` for the checks on each type that the modifier applies to.
   */
  def checkRscModifier(rsc: Opt[Bool], target: Term): Unit =
    def directlyModified(t: Term): Opt[Term] = t match
      case Term.Forall(_, _, body) => directlyModified(body)
      case Term.Capture(base, _) => directlyModified(base)
      case mod @ Term.Annotated(Annot.Resource(_), _) => S(mod)
      case _ => N
    directlyModified(target) match
    // Only the nested modifier is reported here - its target is checked under its own modifier.
    case S(mod) => raise(ErrorReport(msg"A type takes at most one resource modifier." -> mod.toLoc :: Nil))
    case N =>
      val reached = rscReach(target)
      reached.foreach(checkRscTarget(_, rsc))
      def isOwnResource(t: Term): Bool = t match
        case Term.Annotated(Annot.Resource(own), _) => own === S(true)
        case _ =>
          val members = aliasMembers(t)
          members.nonEmpty && members.forall(_.ownRsc === S(S(true)))
      if rsc.isEmpty && reached.forall(isOwnResource) then
        raise(WarningReport(
          msg"Every member of this type is a resource, so 'rsc?' has no effect." -> target.toLoc :: Nil))
  
  /**
   * Checks the operands of an intersection type: a resource modifier inside one is not supported yet, as
   * `ErasedType.eraseSign` never decomposes an intersection, so the modifier would be silently lost.
   */
  def checkRscInIntersection(lhs: Term, rhs: Term): Unit =
    rejectRscModifiersIn(lhs :: rhs :: Nil, "an intersection type")
  
  /**
   * Checks the parameters of a function type: a resource modifier on one is not supported yet, as a function type
   * erases to `Function` without its parameter types, so the modifier would be silently lost.
   */
  def checkRscInFunParams(params: Term): Unit = params match
    case params: Term.Tup => rejectRscModifiersIn(params.subTerms.toList, "the parameters of a function type")
    case param => rejectRscModifiersIn(param :: Nil, "the parameters of a function type")
  
  /**
   * Reports each resource modifier on a term in `ts` or reached through it by `rscReach` (a union's members, a
   * `forall`'s body), as not supported inside the type that `ts` belongs to (e.g. "an intersection type").
   */
  private def rejectRscModifiersIn(ts: Ls[Term], what: Str): Unit =
    ts.flatMap(rscReach).foreach:
      case mod @ Term.Annotated(Annot.Resource(_), _) =>
        raise(ErrorReport(msg"Resource modifiers inside ${what} are not supported yet." -> mod.toLoc :: Nil))
      case _ => ()
  
  /** Checks one type node; the caller controls traversal and avoids revisiting shared signatures. */
  def checkNode(t: Term): Unit = t match
    case Term.Annotated(Annot.Resource(rsc), target) => checkRscModifier(rsc, target)
    case Term.CompType(lhs, rhs, false) => checkRscInIntersection(lhs, rhs)
    case Term.FunTy(lhs, _, _) => checkRscInFunParams(lhs)
    case _ => ()
  
  /**
   * Checks every resource modifier within the type `t`, at any depth.
   *
   * This is intended for the right-hand side of a type alias: it is not traversed as a signature, so this runs the
   * resource modifier checks that `traverseSign` would.
   *
   * The arguments of a type application are skipped: `resolve` already traverses them as signatures, which checks
   * them, so checking them here too would report every error twice.
   */
  def checkAllRscModifiers(t: Term): Unit =
    checkNode(t)
    t match
    case Term.TyApp(con: Resolvable, _) => checkAllRscModifiers(con)
    case _ => t.subTerms.foreach(checkAllRscModifiers)
