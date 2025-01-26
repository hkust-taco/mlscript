package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*

// Lifts classes and functions to the top-level.
// Assumes the input block does not have any `HandleBlock`s.
class Lifter(using State):
  private def lift(f: FunDefn, clsMap: Map[ClassLikeSymbol, ClassLikeSymbol]) = ???
    // val (blk, defns) = f.body.floatOutDefns

  def transform(b: Block) = b