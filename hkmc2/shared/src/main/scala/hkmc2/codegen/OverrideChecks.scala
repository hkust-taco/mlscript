package hkmc2
package codegen

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import hkmc2.Message.MessageContext


/** Checks that member overrides preserve the argument bindings and runtime representations
  * promised by their inherited declarations. The checks cover every supplied declaration,
  * including abstract and unused members, before lowering changes their parameter lists.
  *
  * [[Erasure]] constructs one instance after resolution completes. Construction uses [[OverrideLayout]]
  * to match each override's parameters with its inherited parameters, reports incompatible layouts,
  * and retains the compatible pairs in [[validatedEdges]]. [[inheritedParameters]] supplies the
  * correspondence that erasure needs to assign representations to unannotated overriding parameters.
  * After erasure initializes the parameter and member signatures, [[checkRepresentations]] checks
  * that the override accepts every inherited input and produces only permitted results.
  * `definitions` contains at most one declaration per member symbol.
  */
final class OverrideChecks(definitions: Ls[TermDefinition])(using Config, Ctx, State, Erasure, Raise):
  import OverrideChecks.{report, within, describe}
  
  /** A declaration pair with compatible argument bindings, ready for representation checking.
    * `parameters` pairs each overriding input with its inherited counterpart. The result fields
    * hold representations obtained from declared callable arrows; an absent result means that
    * [[checkRepresentations]] must read the member's completed erased signature.
    */
  private case class Edge(overriding: TermDefinition, inherited: TermSymbol,
      parameters: Ls[(OverrideLayout.Input, OverrideLayout.Input)],
      result: Opt[ErasedValueType], inheritedResult: Opt[ErasedValueType])
  
  // Definitions are keyed by identity: as case classes, they would otherwise be hashed and
  // compared through their entire bodies on every lookup.
  private val layouts =
    mutable.Map.empty[Identity[TermDefinition], Either[OverrideLayout.Failure, OverrideLayout.Signature]]
  
  /** The source layout of `td`, computed once per declaration. A base member with several overrides
    * and a declared member whose erased signature uses its layout then share one traversal of its type.
    */
  def layout(td: TermDefinition): Either[OverrideLayout.Failure, OverrideLayout.Signature] =
    layouts.getOrElseUpdate(Identity(td), OverrideLayout.signature(td))
  
  private val edges = definitions.flatMap: td =>
    td.tsym.overriddenMembers.flatMap: base =>
      softAssert(base.defn.nonEmpty, "An inherited declaration must retain its source signature for override validation")
      base.defn.toList.flatMap: inherited =>
        val checked = for
          actual <- layout(td)
          expected <- layout(inherited)
          parameters <- OverrideLayout.correspondingParameters(actual.params, expected.params)
        yield Edge(td, base, parameters, actual.result, expected.result)
        checked match
          case Left(failure) =>
            report(base, msg"Overriding member '${td.tsym.nme}' ${failure.message}", failure.toLoc.orElse(td.tsym.toLoc))
            Nil
          case Right(edge) => edge :: Nil
  
  /** The `(overriding, inherited)` member pairs whose source layouts preserve argument bindings.
    * Erasure uses these pairs to inherit result representations; [[TargetOverrideChecks]] uses
    * them to check the target's calling convention. Layout validation does not establish representation
    * compatibility: [[checkRepresentations]] reports those errors without removing pairs from this list.
    */
  val validatedEdges: Ls[(TermSymbol, TermSymbol)] = edges.map(edge => edge.overriding.tsym -> edge.inherited)
  
  /** The inherited members of each overriding member in [[validatedEdges]], in the same order.
    * Erasure looks up an unannotated override's inherited result here for every definition,
    * so the lookup must not scan all edges of the program.
    */
  val validatedBases: Map[TermSymbol, Ls[TermSymbol]] = validatedEdges.groupMap(_._1)(_._2)
  
  /** Maps each written overriding parameter to the inherited inputs that deliver the same argument,
    * omitted-argument default, or rest slice. Each input refers either to a written parameter or to
    * a representation obtained from a declared callable arrow. Erasure joins all these inherited
    * representations when the overriding parameter has no annotation of its own. Parameters with
    * no inherited counterpart have no entry.
    */
  val inheritedParameters: Map[VarSymbol, Ls[OverrideLayout.Input]] = edges.flatMap(_.parameters).flatMap:
    (param, inherited) => param.parameter.map(_.sym -> inherited)
  .groupMap(_._1)(_._2)
  
  /** Reports representation incompatibilities for the declaration pairs that passed layout checking.
    * An overriding parameter must hold every value its inherited counterpart accepts; an overriding
    * result must fit the inherited result representation. Both comparisons canonicalize the types
    * and require the value to fit without a cast, treating an absent representation as `Unknown`.
    *
    * For example, overriding `(Int) -> Any` with `(Any) -> Int` accepts every inherited input and
    * returns a permitted result. [[TargetOverrideChecks]] imposes additional restrictions for Wasm.
    * Run this after erasure initializes parameter and member signatures; pairs whose members have
    * not both completed erasure are skipped.
    */
  def checkRepresentations(): Unit =
    def input(param: OverrideLayout.Input): Opt[ErasedValueType] = param.parameter match
      case S(param) => param.sym.erasedType
      case N => param.representation
    def result(sym: TermSymbol, representation: Opt[ErasedValueType]): Opt[ErasedValueType] =
      representation.orElse(sym.declaredResultType)
    edges.foreach: edge =>
      val td = edge.overriding
      val base = edge.inherited
      if td.tsym.isErased && base.isErased then
        val actualResult = result(td.tsym, edge.result)
        val baseResult = result(base, edge.inheritedResult)
        if !within(actualResult, baseResult) then report(base,
          msg"Overriding member '${td.tsym.nme}' produces values represented as '${describe(actualResult)
            }', which the member it overrides cannot produce: its results are represented as '${describe(baseResult)}'",
          td.tsym.toLoc)
        edge.parameters.foreach: (param, inherited) =>
          val actualType = input(param)
          val baseType = input(inherited)
          if !within(baseType, actualType) then report(base,
            msg"${param.label.capitalize} of overriding member '${td.tsym.nme}' is represented as '${describe(actualType)
              }', which cannot hold the values represented as '${describe(baseType)}' that the member it overrides accepts",
            param.toLoc)

object OverrideChecks:
  /** Whether a value represented as `actual` fits `expected` without a cast, after canonicalizing both.
    * An absent representation stands for `Unknown`.
    */
  def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType])(using Ctx, State): Bool =
    ErasedType.needsCast(canonical(actual), canonical(expected)).contains(false)
  
  /** The user-facing description of a canonicalized representation; an absent one is `Unknown`. */
  def describe(tpe: Opt[ErasedValueType])(using Ctx, State): Str = canonical(tpe).describe
  
  private def canonical(tpe: Opt[ErasedValueType])(using Ctx, State): CanonicalErasedValueType =
    tpe.getOrElse(ErasedType.Unknown).canonicalize
  
  /** Reports an override incompatibility at `loc` and points at the overridden member's declaration. */
  def report(base: TermSymbol, message: Message, loc: Opt[Loc])(using Raise): Unit =
    raise(ErrorReport(
      (message -> loc) :: (msg"The overridden member '${base.nme}' is defined here" -> base.toLoc) :: Nil,
      source = Diagnostic.Source.Compilation))
