package hkmc2
package codegen

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
  */
final class OverrideChecks(definitions: Ls[TermDefinition])(using Config, Ctx, State, Erasure, Raise):
  /** A declaration pair with compatible argument bindings, ready for representation checking.
    * `parameters` pairs each overriding input with its inherited counterpart. The result fields
    * hold representations obtained from declared callable arrows; an absent result means that
    * [[checkRepresentations]] must read the member's completed erased signature.
    */
  private case class Edge(overriding: TermDefinition, inherited: TermSymbol,
      parameters: Ls[(OverrideLayout.Input, OverrideLayout.Input)],
      result: Opt[ErasedValueType], inheritedResult: Opt[ErasedValueType])
  
  private def report(base: TermSymbol, message: Message, loc: Opt[Loc]): Unit =
    raise(ErrorReport(
      (message -> loc) :: (msg"The overridden member '${base.nme}' is defined here" -> base.toLoc) :: Nil,
      source = Diagnostic.Source.Compilation))
  
  private val edges = definitions.distinctBy(_.tsym).flatMap: td =>
    td.tsym.overriddenMembers.flatMap: base =>
      softAssert(base.defn.nonEmpty, "An inherited declaration must retain its source signature for override validation")
      base.defn.toList.flatMap: inherited =>
        val checked = for
          actual <- OverrideLayout.signature(td)
          expected <- OverrideLayout.signature(inherited)
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
    def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType]): Bool =
      ErasedType.needsCast(actual.getOrElse(ErasedType.Unknown).canonicalize,
        expected.getOrElse(ErasedType.Unknown).canonicalize).contains(false)
    def describe(tpe: Opt[ErasedValueType]): Str = tpe.getOrElse(ErasedType.Unknown).canonicalize.describe
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
