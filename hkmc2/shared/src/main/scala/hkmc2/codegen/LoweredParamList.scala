package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import hkmc2.document.*
import semantics.*
import semantics.Elaborator.State
import syntax.Tree


/** The parameter lists accepted by the IR: fixed parameters followed by at most one rest parameter.
  * Source variadic parameters with trailing parameters must be desugared before constructing IR.
  * Individual parameters retain their source metadata and erased symbols. In particular, an optional
  * parameter binds `null` for a missing argument. Call rewrites must supply this default whenever
  * they replace parameter binding with assignments or substitutions. */
final case class LoweredParamList(flags: ParamListFlags, params: Ls[Param], restParam: Opt[Param])
(val toLoc: Opt[Loc]) extends Located:
  def foreach(f: Param => Unit): Unit = allParams.foreach(f)
  lazy val allParams: Ls[Param] = params ::: restParam.toList
  lazy val paramSyms: Ls[VarSymbol] = allParams.map(_.sym)
  lazy val paramCountLB: Int = FldFlags.requiredPrefixLength(params.map(_.flags))
  def hasOptParams: Bool = paramCountLB < params.length
  def paramCountUB: Bool = restParam.isEmpty
  def show(using Scope, ShowCfg, Raise): Document =
    flags.show
    :: doc"(" :: (params.map(_.show) ::: restParam.toList.map(p => doc"...${p.show}")).mkDocument(", ")
    :: doc")"
  def showDbg(using DebugPrinter): Str = flags.showDbg
    + (params.map(_.showDbg) ::: restParam.toList.map(p => "..." + p.showDbg)).mkString("(", ", ", ")")

object LoweredParamList:
  def plain(params: Ls[Param])(toLoc: Opt[Loc]): LoweredParamList =
    LoweredParamList(ParamListFlags.empty, params, N)(toLoc)
  
  /** Classes and generated pattern methods have only fixed parameters. Keep the check at their
    * source-to-IR boundary so a future source change cannot silently discard a variadic parameter. */
  def fixed(ps: ParamList): LoweredParamList =
    assert(ps.variadic.isEmpty, "Expected fixed parameters at the source-to-IR boundary")
    LoweredParamList(ps.flags, ps.params, N)(ps.toLoc)
  
  /** The physical argument layout shared by definitions and forwarding wrappers.
    * With trailing parameters, a fresh rest parameter receives everything after the required prefix.
    * This does not bind the remaining source parameters: executable definitions must also emit
    * the extraction prologue in `Lowering.lowerTrailingParams`; wrappers simply forward the arguments. */
  def callingConvention(ps: ParamList)(using State): LoweredParamList = ps.variadic match
    case S(Variadic(_, _ :: _)) =>
      val args = VarSymbol(Tree.Ident("args"), erasedType = S(ErasedType.Array))
      LoweredParamList(ps.flags, ps.params.take(ps.leadingRequiredCount), S(Param.simple(args)))(ps.toLoc)
    case variadic =>
      LoweredParamList(ps.flags, ps.params, variadic.map(_.param))(ps.toLoc)
