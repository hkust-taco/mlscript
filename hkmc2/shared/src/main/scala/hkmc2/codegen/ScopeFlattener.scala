package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*

/** - For function bodies, fuse all shallowly-nested scopes into one top-level one,
  *   because certain passes, such as the handler lowering, rely on knowing all the local
  *   variables of each function.
  * - Asserts the absence of Label(loop = true) blocks,
  *   because loops should be rewritten to functions first,
  *   otherwise we cannot fuse scopes correctly.
  */
class ScopeFlattener extends BlockTransformer(new SymbolSubst):
  override def applyBlock(b: Block): Block = b match
    case Label(_, loop, _, _) =>
      assert(!loop, "loops should be rewritten to functions before scope flattening")
      super.applyBlock(b)
    case _ => super.applyBlock(b)
  
  private var scopedSymForCurrentFun: Option[collection.mutable.Set[Symbol]] = None
  override def applyFunBodyLikeBlock(b: Block): Block =
    val prevScopedSymForCurrentFun = scopedSymForCurrentFun
    val resBlk = b match
      case Scoped(syms, body) =>
        scopedSymForCurrentFun = Some(collection.mutable.Set.from(syms))
        val newBody = applySubBlock(body)
        new Scoped(scopedSymForCurrentFun.get, newBody)
      case _ =>
        scopedSymForCurrentFun = Some(collection.mutable.Set.empty[Symbol])
        val newBlk = applySubBlock(b)
        Scoped(scopedSymForCurrentFun.get, newBlk)
    scopedSymForCurrentFun = prevScopedSymForCurrentFun
    resBlk
  
  override def applyScopedBlock(b: Block): Block = b match
    case Scoped(syms, body) =>
      scopedSymForCurrentFun match
        case None => super.applyScopedBlock(b)
        case Some(scopedForCurrentFun) =>
          scopedForCurrentFun.addAll(syms)
          super.applySubBlock(body)
    case _ => super.applySubBlock(b)
