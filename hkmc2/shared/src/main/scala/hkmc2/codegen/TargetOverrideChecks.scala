package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import hkmc2.Message.MessageContext


/** Check the additional calling-convention restrictions imposed by a compilation target.
  * Source override checks establish argument binding and result compatibility before lowering.
  * Wasm also calls an override directly through the introducing method's fixed physical slots,
  * so an override's wider accepted inputs must fit those slots as well.
  */
object TargetOverrideChecks:
  private case class Parameter(name: Opt[Str], representation: Opt[ErasedValueType], loc: Opt[Loc])
  private case class Signature(params: Ls[Ls[Parameter]], hasRest: Bool)

  private def signature(symbol: TermSymbol): Signature = symbol.irFunDefn match
    case S(definition) => Signature(
      definition.params.map(_.params.map(p => Parameter(S(p.sym.nme), p.sym.erasedType, p.toLoc))),
      definition.params.exists(_.restParam.isDefined),
    )
    case N =>
      // Abstract and external declarations have no executable IR body. Erasure has already
      // published their fixed-arity callable contract, including imports from another unit.
      val params = symbol.erasedSignature.toList.flatMap(_.paramLists)
      Signature(params.map(_.map(Parameter(N, _, symbol.toLoc))), false)

  def apply(edges: Ls[(TermSymbol, TermSymbol)])(using Config, Ctx, State, Raise): Unit =
    if summon[Config].target is CompilationTarget.Wasm then
      def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType]): Bool =
        ErasedType.needsCast(actual.getOrElse(ErasedType.Unknown).canonicalize,
          expected.getOrElse(ErasedType.Unknown).canonicalize).contains(false)
      def describe(tpe: Opt[ErasedValueType]): Str = tpe.getOrElse(ErasedType.Unknown).canonicalize.describe
      def fixedLists(signature: Signature): Ls[Ls[Parameter]] = signature.params match
        case Nil => Nil :: Nil
        case params => params
      edges.foreach: (overriding, base) =>
        val actual = signature(overriding)
        val inherited = signature(base)
        // The Wasm backend rejects rest parameters independently; their lowered array does not
        // describe a supported fixed-slot ABI and must not be compared as an ordinary parameter.
        if !actual.hasRest && !inherited.hasRest then
          def report(message: Message, loc: Opt[Loc]): Unit = raise(ErrorReport(
            (message -> loc) :: (msg"The overridden member '${base.nme}' is defined here" -> base.toLoc) :: Nil,
            source = Diagnostic.Source.Compilation))
          val params = fixedLists(actual)
          val baseParams = fixedLists(inherited)
          // Physical arity is checked when Wasm constructs the actual virtual slot, including
          // structural override paths that do not have a validated source declaration edge.
          if params.map(_.length) == baseParams.map(_.length) then
            params.flatten.zip(baseParams.flatten).zipWithIndex.foreach:
              case ((param, inheritedParam), index) =>
                // Source checking owns failures in the other direction. Report only the additional
                // restriction that a direct call of the override must fit the inherited slot.
                if within(inheritedParam.representation, param.representation)
                    && !within(param.representation, inheritedParam.representation) then
                  val parameter = param.name.fold(msg"Parameter ${index + 1}")(name => msg"Parameter '$name'")
                  report(
                    msg"$parameter of overriding member '${overriding.nme}' receives values represented as '${
                      describe(param.representation)}', but Wasm calls it through the signature of the member it overrides, whose parameter is represented as '${
                      describe(inheritedParam.representation)}'",
                    param.loc)
  end apply
