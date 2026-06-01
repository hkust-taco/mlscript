package hkmc2
package codegen

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


/** - For function bodies, fuse all shallowly-nested scopes into one top-level one,
  *   because certain passes, such as the handler lowering, rely on knowing all the local
  *   variables of each function.
  * - Assert the absence of Label(loop = true) blocks,
  *   because loops should be rewritten to functions first,
  *   otherwise we cannot fuse scopes correctly.
  */
class ScopeFlattener extends BlockTransformer(new SymbolSubst):
  override def applyBlock(b: Block): Block = b match
    case Label(_, loop, _, _) =>
      assert(!loop, "loops should be rewritten to functions before scope flattening")
      super.applyBlock(b)
    case _ => super.applyBlock(b)
  
  private var scopedSymForCurrentFun: Opt[mutable.Set[ScopedSymbol]] = N
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
        val tmp = mutable.Set.empty[ScopedSymbol]
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


