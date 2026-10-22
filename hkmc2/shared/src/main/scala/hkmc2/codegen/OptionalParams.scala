package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.State
import syntax.{Tree, SpreadKind}


/** Optional parameters bind `null` when an argument is missing. JS receives missing arguments as
  * `undefined`, so rewrites that remove a JS function entry (inlining, tail-call jumps, and constructor
  * elimination) must preserve its normalization. Wasm call sites supply `null` directly; IR `undefined`
  * is an uninitialized value, not a distinct Wasm value that can be tested for missing arguments. */
object OptionalParams:
  case class Forwarding(params: LoweredParamList, args: Ls[Arg], prologue: Block => Block)
  
  /** Generated forwarding functions leave normalization to the callee. Binding their optional
    * slots as ordinary optional parameters would replace undefined before a foreign callee
    * could apply its native defaults. A raw rest parameter preserves those slots instead. */
  def forwarding(params: LoweredParamList)(using State): Forwarding =
    if !params.hasOptParams then
      Forwarding(params, params.params.map(_.sym.asSimpleRef.asArg) :::
        params.restParam.toList.map(p => Arg(S(SpreadKind.Eager), p.sym.asSimpleRef)), body => body)
    else
      val (required, optional) = params.params.splitAt(params.paramCountLB)
      val raw = VarSymbol(Tree.Ident("args"), erasedType = S(ErasedType.Array))
      def int(n: Int): Path = Value.Lit(Tree.IntLit(n))(N)
      val slots = optional.indices.map(index =>
        DynSelect(raw.asSimpleRef, int(index), DynSelectKind.ArrayIdx)(params.toLoc).asArg).toList
      val args = required.map(_.sym.asSimpleRef.asArg) ::: slots
      val physical = LoweredParamList(params.flags, required, S(Param.simple(raw)))(params.toLoc)
      params.restParam match
        case N => Forwarding(physical, args, body => body)
        case S(rest) =>
          val slice = State.runtimeSymbol.asSimpleRef.sel(Tree.Ident("Tuple"), State.tupleSymbol)
            .sel(Tree.Ident("slice"), State.tupleSliceSymbol)
          val restValue = Call(slice, (raw.asSimpleRef :: int(optional.length) :: int(0) :: Nil)
            .map(_.asArg) ne_:: Nil)(CallMetadata.defaultMlsFun, params.toLoc)
          Forwarding(physical, args :+ Arg(S(SpreadKind.Eager), rest.sym.asSimpleRef),
            body => Scoped(Set(rest.sym), Assign(rest.sym, restValue, body)))
  
  def normalize(sym: LocalVarSymbol, rest: Block)(using Config): Block = config.target match
    case CompilationTarget.JS =>
      Match(sym.asSimpleRef,
        Case.Lit(Tree.UnitLit(false)) -> Assign(sym, Value.Lit(Tree.UnitLit(true))(sym.toLoc), End()) :: Nil,
        N, rest)
    case CompilationTarget.Wasm => rest
  
  def normalizeAll(params: Ls[Param], body: Block)(using Config): Block =
    params.filter(_.flags.opt).foldRight(body)((param, rest) => normalize(param.sym, rest))
  
  /** Evaluate a constructor slot once before optimizers can replace field reads with arguments. */
  def argument(value: Path)(k: Path => Block)(using State, Config): Block = value match
    case Value.Lit(Tree.UnitLit(false)) if config.target is CompilationTarget.JS =>
      k(Value.Lit(Tree.UnitLit(true))(value.toLoc))
    case _: Value.Lit => k(value)
    case _ =>
      val slot = TempSymbol(N, erasedType = N, "optionalArg")
      Scoped(Set(slot), Assign(slot, value, normalize(slot, k(slot.asSimpleRef))))
