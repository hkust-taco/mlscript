package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import hkmc2.Message.MessageContext


/** Checks whether overrides can use their compilation target's runtime calling convention.
  * Wasm gives every implementation of a virtual method the function signature of the method that
  * introduced its slot. Direct calls to an override use that signature too, so every value the
  * overriding parameter accepts must fit the inherited physical parameter slot.
  *
  * For example, overriding a parameter of type `Int` with one of type `Any` satisfies the source
  * checks in [[OverrideChecks]], but a direct call could then supply a string to the inherited
  * `Int` slot. This checker rejects that widening for Wasm. Other targets have no extra checks here.
  */
object TargetOverrideChecks:
  /** A parameter's erased representation and the source information used to explain a mismatch.
    * Imported erased signatures retain parameter positions and types but no parameter names.
    */
  private case class Parameter(name: Opt[Str], representation: Opt[ErasedValueType], loc: Opt[Loc])
  /** The fixed parameter lists to compare at the calling boundary. `hasRest` records whether an
    * executable definition also has a rest parameter, which requires a separate backend diagnostic.
    */
  private case class Signature(params: Ls[Ls[Parameter]], hasRest: Bool)

  /** Obtains a member's parameter representations after lowering. An executable definition supplies
    * its lowered parameter lists and their source locations; a member without an IR body supplies
    * the fixed lists published by erasure. The latter covers abstract, external, and prelude members.
    */
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

  /** Reports Wasm parameter widening errors for `(overriding, inherited)` pairs supplied by
    * [[Erasure.validatedOverrideEdges]]. Run this after lowering ordinary compilation units;
    * prelude declarations have no bodies to lower, so their completed erasure supplies the signatures.
    *
    * Checks corresponding fixed slots only when both signatures have the same parameter-list
    * arities and neither has a lowered rest parameter. The Wasm backend diagnoses unsupported rest
    * parameters and incompatible physical arities when it constructs functions and virtual slots.
    * Parameters that already fail the source representation check produce no additional error here.
    * This method has no effect for other targets.
    */
  def apply(edges: Ls[(TermSymbol, TermSymbol)])(using Config, Ctx, State, Raise): Unit =
    if summon[Config].target is CompilationTarget.Wasm then
      def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType]): Bool =
        ErasedType.needsCast(actual.getOrElse(ErasedType.Unknown).canonicalize,
          expected.getOrElse(ErasedType.Unknown).canonicalize).contains(false)
      def describe(tpe: Opt[ErasedValueType]): Str = tpe.getOrElse(ErasedType.Unknown).canonicalize.describe
      /** Treats a member with no parameter lists as one empty physical list for arity comparison. */
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
