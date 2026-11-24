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
  * and retains the compatible pairs. [[inheritedParameters]] supplies the correspondence that erasure
  * needs to assign representations to unannotated overriding parameters.
  * After erasure initializes the parameter and member signatures, [[checkSignatures]] checks
  * that the override accepts every inherited input and produces only permitted results, and applies
  * the compilation target's additional calling-convention restrictions to the same signatures.
  * `definitions` contains at most one declaration per member symbol.
  */
final class OverrideChecks(definitions: Ls[TermDefinition])(using Config, Ctx, State, Erasure, Raise):
  import OverrideChecks.{report, within, describe}
  
  /** A declaration pair with compatible argument bindings, ready for representation checking.
    * `parameters` pairs each overriding parameter with its inherited counterpart. `inherited` retains
    * the complete inherited parameter lists, including unmatched optional or dropped parameters, for
    * target arity checks.
    */
  private case class Edge(overriding: TermDefinition, inherited: TermDefinition, parameters: Ls[(Param, Param)])
  
  private val edges = definitions.flatMap: td =>
    td.tsym.overriddenMembers.flatMap: base =>
      softAssert(base.defn.nonEmpty, "An inherited declaration must retain its source signature for override validation")
      // `Inheritance.validateMember` reports an override that changes the kind of definition; comparing
      // the pair's layouts would only restate that error, so the pair yields neither a layout error nor an edge.
      base.defn.toList.filterNot(Inheritance.changesMemberKind(td, _)).flatMap: inherited =>
        // A handler member traversed by erasure has no resumption parameter list, unlike its symbol's
        // declaration, so the overriding side's lists come from `td`.
        OverrideLayout.correspondingParameters(td.params, inherited.params) match
          case Left(failure) =>
            report(base, msg"Overriding member '${td.tsym.nme}' ${failure.message}", failure.toLoc.orElse(td.tsym.toLoc))
            Nil
          case Right(parameters) => Edge(td, inherited, parameters) :: Nil
  
  /** The inherited members whose source layouts preserve each overriding member's argument bindings.
    * Erasure looks up an unannotated override's inherited result here for every definition,
    * so the lookup must not scan all edges of the program.
    */
  val validatedBases: Map[TermSymbol, Ls[TermSymbol]] = edges.groupMap(_.overriding.tsym)(_.inherited.tsym)
  
  /** Maps each overriding parameter to the inherited parameters that deliver the same argument,
    * omitted-argument default, or rest slice. Erasure joins all their representations when the
    * overriding parameter has no annotation of its own. Parameters with no inherited counterpart
    * have no entry.
    */
  val inheritedParameters: Map[VarSymbol, Ls[Param]] = edges.flatMap(_.parameters).groupMap(_._1.sym)(_._2)
  
  /** Reports overridable members that [[InterfaceExposure]] found reachable from this compilation unit's
    * exports, in classes and objects that other units may extend, when their signatures leave a parameter
    * or the result unspecified. Overrides in other units inherit these members' representations, which
    * erasure cannot recover from an unannotated base: an exposed `open fun f(x) = x + 1` would give
    * every such override an unknown parameter and result.
    *
    * A parameter or result is specified when the member annotates it, gives a separate full signature,
    * or inherits it from the corresponding parameter or result of an overridden member that specifies it.
    * Overrides inherit signatures unchanged, so they need not restate them. Overridden members of other
    * compilation units count as specified: their own unit applies this check to the members it lets
    * other units override.
    */
  def checkExposedSignatures(): Unit =
    /** The inherited declarations whose parameter lists correspond to `td`'s, with the parameter pairs. */
    def correspondingBases(td: TermDefinition): Ls[(TermDefinition, Ls[(Param, Param)])] =
      td.tsym.overriddenMembers.flatMap(_.defn).filterNot(Inheritance.changesMemberKind(td, _)).flatMap: inherited =>
        OverrideLayout.correspondingParameters(td.params, inherited.params).toOption.map(inherited -> _)
    // A separate signature, as in `fun f: (Int) -> Int` followed by `fun f(x) = x`, types every written
    // parameter; a result annotation describes only the result.
    def hasFullSignature(td: TermDefinition): Bool =
      td.sign.isDefined && !td.flags.hasResultAnnotation && td.params.nonEmpty
    /** Whether `base`, overridden from `td`, specifies a part; `visiting` stops at inheritance cycles. */
    def inheritedSpecifies(td: TermDefinition, base: TermDefinition, visiting: Set[TermSymbol])(
        specifies: Set[TermSymbol] => Bool): Bool =
      (base.tsym.getState isnt td.tsym.getState) || (!visiting(base.tsym) && specifies(visiting + base.tsym))
    def parameterSpecified(td: TermDefinition, param: Param, visiting: Set[TermSymbol]): Bool =
      param.sign.isDefined || hasFullSignature(td) || locally:
        val inherited = correspondingBases(td).flatMap: (base, parameters) =>
          parameters.collect { case (actual, inherited) if actual.sym is param.sym => base -> inherited }
        // Erasure joins every corresponding inherited representation, so each must be specified.
        inherited.nonEmpty && inherited.forall: (base, inheritedParam) =>
          inheritedSpecifies(td, base, visiting)(parameterSpecified(base, inheritedParam, _))
    def resultSpecified(td: TermDefinition, visiting: Set[TermSymbol]): Bool =
      // Erasure does not inherit a result for async and generator bodies, whose results are wrappers.
      td.sign.isDefined || (td.resultWrapperAnnotation.isEmpty && correspondingBases(td).exists: (base, _) =>
        inheritedSpecifies(td, base, visiting)(resultSpecified(base, _)))
    definitions.foreach: td =>
      td.tsym.getState.newResolverState.exposedOpenMember(td.tsym).foreach: path =>
        val parameters = td.params.flatMap: ps =>
          ps.params ::: ps.variadic.toList.flatMap(variadic => variadic.param :: variadic.trailing)
        val missing = parameters.filterNot(parameterSpecified(td, _, Set(td.tsym)))
        val missingResult = !resultSpecified(td, Set(td.tsym))
        val required = (missingResult, missing.nonEmpty) match
          case (true, true) => S("its result type and the types of its parameters")
          case (true, false) => S(if td.k is syntax.Fun then "its result type" else "its type")
          case (false, true) => S("the types of its parameters")
          case (false, false) => N
        required.foreach: required =>
          raise(ErrorReport(
            path.diagnostic(msg"Open member '${td.tsym.nme}' is exposed by this compilation unit, so ${required
              } must be annotated or inherited from an overridden member", td.headerLoc)
              ::: missing.map(param => msg"Parameter '${param.sym.nme}' has no type annotation" -> param.toLoc),
            source = Diagnostic.Source.Compilation))
  
  /** Computes why a source-compatible override cannot use Wasm's fixed parameter slots.
    * A variadic list needs argument packing that the Wasm backend does not implement. An override
    * without a variadic list of its own can still drop an inherited one, as with `(Int)` overriding
    * `(Int, drop ...Array[Any])`; the message then names the inherited signature. With fixed
    * lists, each source parameter occupies one slot, including optional and `drop` parameters, so the override
    * must preserve every list's length even when its source bindings permit adding or dropping inputs.
    */
  private def wasmLayoutFailure(edge: Edge): Opt[OverrideLayout.Failure] =
    val actual = edge.overriding.params
    val inherited = edge.inherited.params
    actual.iterator.flatMap(_.variadic).nextOption() match
      case S(rest) => S(OverrideLayout.Failure(
        msg"cannot use a variadic signature on the Wasm target", rest.param.toLoc.orElse(edge.overriding.headerLoc)))
      case N if inherited.exists(_.variadic.nonEmpty) => S(OverrideLayout.Failure(
        msg"overrides a variadic signature, which the Wasm target does not support", edge.overriding.headerLoc))
      case N if actual.map(_.params.length) != inherited.map(_.params.length) => S(OverrideLayout.Failure(
        msg"must preserve the number of parameters in each parameter list on the Wasm target", edge.overriding.headerLoc))
      case N => N
  
  /** Reports source and target incompatibilities for declaration pairs that passed binding checks.
    * An overriding parameter must hold every value its inherited counterpart accepts; an overriding
    * result must fit the inherited result representation. Both comparisons canonicalize the types
    * and require the value to fit without a cast, treating an absent representation as `Unknown`.
    *
    * For example, overriding `fun f(x: Int): Any` with `fun f(x: Any): Int` accepts every inherited
    * input and returns a permitted result on JavaScript. Wasm uses the inherited method's fixed parameter slots
    * for direct calls to the override too: its layout must pass [[wasmLayoutFailure]], and its inputs
    * must also fit the inherited representations. A parameter comparison reports the source failure
    * first, or the additional Wasm restriction when the source comparison succeeds.
    * Run this after erasure initializes parameter and member signatures; pairs whose members have
    * not both completed erasure are skipped.
    */
  def checkSignatures(): Unit =
    edges.foreach: edge =>
      val td = edge.overriding
      val base = edge.inherited.tsym
      if td.tsym.isErased && base.isErased then
        val actualResult = td.tsym.sourceDeclaredResultType
        val baseResult = base.sourceDeclaredResultType
        if !within(actualResult, baseResult) then report(base,
          msg"Overriding member '${td.tsym.nme}' produces values represented as '${describe(actualResult)
            }', which the member it overrides cannot produce: its results are represented as '${describe(baseResult)}'",
          td.tsym.toLoc)
        val isWasm = config.target is CompilationTarget.Wasm
        val targetFailure = if isWasm then wasmLayoutFailure(edge) else N
        targetFailure.foreach: failure =>
          report(base, msg"Overriding member '${td.tsym.nme}' ${failure.message}", failure.toLoc)
        edge.parameters.foreach: (param, inherited) =>
          val actualType = param.sym.erasedType
          val baseType = inherited.sym.erasedType
          if !within(baseType, actualType) then report(base,
            msg"${OverrideLayout.label(param).capitalize} of overriding member '${td.tsym.nme}' is represented as '${describe(actualType)
              }', which cannot hold the values represented as '${describe(baseType)}' that the member it overrides accepts",
            param.toLoc)
          else if isWasm && targetFailure.isEmpty && !within(actualType, baseType) then report(base,
            msg"${OverrideLayout.label(param).capitalize} of overriding member '${td.tsym.nme}' receives values represented as '${
              describe(actualType)}', but Wasm calls it through the signature of the member it overrides, whose parameter is represented as '${
              describe(baseType)}'",
            param.toLoc)

object OverrideChecks:
  /** Whether a value represented as `actual` fits `expected` without a cast, after canonicalizing both.
    * An absent representation stands for `Unknown`.
    */
  private def within(actual: Opt[ErasedValueType], expected: Opt[ErasedValueType])(using Ctx, State): Bool =
    ErasedType.needsCast(canonical(actual), canonical(expected)).contains(false)
  
  /** The user-facing description of a canonicalized representation; an absent one is `Unknown`. */
  private def describe(tpe: Opt[ErasedValueType])(using Ctx, State): Str = canonical(tpe).describe
  
  private def canonical(tpe: Opt[ErasedValueType])(using Ctx, State): CanonicalErasedValueType =
    tpe.getOrElse(ErasedType.Unknown).canonicalize
  
  /** Reports an override incompatibility at `loc` and points at the overridden member's declaration. */
  private def report(base: TermSymbol, message: Message, loc: Opt[Loc])(using Raise): Unit =
    raise(ErrorReport(
      (message -> loc) :: (msg"The overridden member '${base.nme}' is defined here" -> base.toLoc) :: Nil,
      source = Diagnostic.Source.Compilation))
