package hkmc2.utils

import hkmc2.semantics.*

class SymbolSubst:
  def mapBlockMemberSym(s: BlockMemberSymbol): BlockMemberSymbol = s
  def mapFlowSym(s: FlowSymbol): FlowSymbol = s
  def mapTempSym(s: TempSymbol): TempSymbol = s
  def mapVarSym(s: VarSymbol): VarSymbol = s
  def mapInstSym(s: InstSymbol): InstSymbol = s
  def mapBuiltInSym(s: BuiltinSymbol): BuiltinSymbol = s
  def mapTermSym(s: TermSymbol): TermSymbol = s
  def mapCtorSym(s: CtorSymbol): CtorSymbol = s
  def mapClsSym(s: ClassSymbol): ClassSymbol = s
  def mapModuleSym(s: ModuleSymbol): ModuleSymbol = s
  def mapTypeAliasSym(s: TypeAliasSymbol): TypeAliasSymbol = s
  def mapPatSym(s: PatternSymbol): PatternSymbol = s
  def mapTopLevelSym(s: TopLevelSymbol): TopLevelSymbol = s
