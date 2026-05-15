package hkmc2
package codegen

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


/** - For function bodies, fuse all shallowly-nested scopes into one top-level one,
  *   because certain passes, such as the handler lowering, rely on knowing all the local
  *   variables of each function.
  * - Loop labels are also safe to flatten right before handler lowering as long as their bodies
  *   do not contain lambdas; otherwise locals could be moved out of scope incorrectly.
  *   This pass must therefore still run after the lifter, which is the pass that needs updating
  *   before more general loop-label flattening becomes valid.
  */
class ScopeFlattener extends BlockTransformer(new SymbolSubst):
  /** Returns whether a loop-label body contains any lambda, stopping at the first one found. */
  private def loopLabelContainsLambda(b: Block): Bool =
    object lambdaDetector extends BlockTraverser:
      var found = false
      override def applySubBlock(b: Block): Unit =
        if !found then super.applySubBlock(b)
      override def applyLam(l: Lambda): Unit =
        found = true
    lambdaDetector.applyBlock(b)
    lambdaDetector.found
  
  override def applyBlock(b: Block): Block = b match
    case Label(_, loop, body, _) =>
      assert(!loop || !loopLabelContainsLambda(body),
        "ScopeFlattener cannot flatten loop labels whose bodies contain lambdas; lift them before flattening")
      super.applyBlock(b)
    case _ => super.applyBlock(b)
  
  private var scopedSymForCurrentFun: Opt[mutable.Set[Symbol]] = N
  override def applyFunBodyLikeBlock(b: Block): Block =
    val prevScopedSymForCurrentFun = scopedSymForCurrentFun
    val resBlk = b match
      case Scoped(syms, body) =>
        val tmp = mutable.Set.from(syms)
        scopedSymForCurrentFun = S(tmp)
        val newBody = applySubBlock(body)
        if (newBody is body) && tmp.sizeCompare(syms) === 0
        then b
        else Scoped(tmp, newBody)
      case _ =>
        val tmp = mutable.Set.empty[Symbol]
        scopedSymForCurrentFun = S(tmp)
        val newBlk = applySubBlock(b)
        Scoped(tmp, newBlk)
    scopedSymForCurrentFun = prevScopedSymForCurrentFun
    resBlk
  
  override def applyScopedBlock(b: Block): Block = b match
    case Scoped(syms, body) =>
      scopedSymForCurrentFun match
        case N => super.applyScopedBlock(b)
        case S(scopedForCurrentFun) =>
          scopedForCurrentFun.addAll(syms)
          super.applySubBlock(body)
    case _ => super.applySubBlock(b)

