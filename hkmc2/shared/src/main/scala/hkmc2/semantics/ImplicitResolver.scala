package hkmc2.semantics

import mlscript.utils.*, shorthands.*

class CtxArgImpl(val param: Param) extends CtxArg:
  override def term: Opt[Term] = N

