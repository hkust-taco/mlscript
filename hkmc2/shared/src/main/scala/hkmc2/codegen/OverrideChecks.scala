package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import hkmc2.Message.MessageContext


/** Validate source declarations, including abstract and unused members that need not survive
  * lowering. Parameter correspondence is established before erasure assigns inherited types;
  * representation checks read those completed types afterwards. No metadata is added to symbols.
  */
final class OverrideChecks(definitions: Ls[TermDefinition])(using Config, Ctx, State, Erasure, Raise):
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
  
  val validatedEdges: Ls[(TermSymbol, TermSymbol)] = edges.map(edge => edge.overriding.tsym -> edge.inherited)
  
  /** Multiple possible ancestors all constrain an overriding input. Their representations are
    * joined by Erasure, rather than choosing an ancestor according to resolution delivery order.
    */
  val inheritedParameters: Map[VarSymbol, Ls[OverrideLayout.Input]] = edges.flatMap(_.parameters).flatMap:
    (param, inherited) => param.parameter.map(_.sym -> inherited)
  .groupMap(_._1)(_._2)
  
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
