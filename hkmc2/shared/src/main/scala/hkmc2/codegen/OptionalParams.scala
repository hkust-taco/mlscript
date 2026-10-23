package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.State
import syntax.{Tree, SpreadKind}


/** Optional parameters bind `null` for missing arguments. Rewrites that replace calls with
  * assignments must supply that default themselves instead of relying on function entry code. */
object OptionalParams:
  case class Forwarding(params: LoweredParamList, args: Ls[Arg])
  
  /** Forward optional arguments to the callee without applying MLscript defaults to foreign calls.
    * Foreign constructors need fixed slots to retain their flattened argument layout; ordinary
    * forwarding calls can pass the optional suffix as a spread and let the callee bind its slots.
    * Note: while it doesn't make much sense to declare JS-foreign classes as curried,
    *   we might well want to declare Scala classes as curried,
    *   which on the JVM does flatten the parameter list,
    *   so this might be useful once we have the Java backend. */
  def forwarding(params: LoweredParamList, fixedArity: Bool)(using State): Forwarding =
    assert(!fixedArity || params.restParam.isEmpty, "Constructor parameters must have a fixed layout")
    if !params.hasOptParams then
      Forwarding(params, params.params.map(_.sym.asSimpleRef.asArg) :::
        params.restParam.toList.map(p => Arg(S(SpreadKind.Eager), p.sym.asSimpleRef)))
    else
      val required = params.params.take(params.paramCountLB)
      val raw = VarSymbol(Tree.Ident("args"), erasedType = S(ErasedType.Array))
      val suffix = if fixedArity then
        (0 until params.params.length - required.length).map(index =>
          DynSelect(raw.asSimpleRef, Value.Lit(Tree.IntLit(index))(N), DynSelectKind.ArrayIdx)(params.toLoc).asArg).toList
      else Arg(S(SpreadKind.Eager), raw.asSimpleRef) :: Nil
      val args = required.map(_.sym.asSimpleRef.asArg) ::: suffix
      val physical = LoweredParamList(params.flags, required, S(Param.simple(raw)))(params.toLoc)
      Forwarding(physical, args)
  
  /** Complete a known argument list, declining calls that omit required parameters so callers can
    * retain their arity diagnostics instead of silently supplying values for invalid calls. */
  def pad(params: Ls[Param], args: Ls[Arg]): Opt[Ls[Arg]] =
    assert(args.forall(_.spread.isEmpty), "Argument count must be known before padding optional slots")
    val missing = params.drop(args.length)
    Option.when(missing.forall(_.flags.opt)):
      args ::: missing.map(p => Value.Lit(Tree.UnitLit(true))(p.toLoc).asArg)
  
  /** Bind a slot from an already evaluated argument tuple. The tuple-length guard prevents an
    * out-of-bounds read from manufacturing an uninitialized value for an absent optional argument. */
  def bindFromTuple(args: Path, index: Int, sym: LocalVarSymbol, optional: Bool, rest: Block): Block =
    val value = DynSelect(args, Value.Lit(Tree.IntLit(index))(N), DynSelectKind.ArrayIdx)(sym.toLoc)
    if !optional then Assign(sym, value, rest)
    else
      assert(index >= 0, "Optional slots are indexed from the start of the argument tuple")
      Match(args, Case.Tup(index + 1, true) -> Assign(sym, value, End()) :: Nil,
        S(Assign(sym, Value.Lit(Tree.UnitLit(true))(sym.toLoc), End())), rest)
  
  /** Evaluate a constructor slot once before optimizers can replace field reads with arguments. */
  def argument(value: Path)(k: Path => Block)(using State): Block = value match
    case _: Value.Lit => k(value)
    case _ =>
      val slot = TempSymbol(N, erasedType = N, "optionalArg")
      Scoped(Set(slot), Assign(slot, value, k(slot.asSimpleRef)))
