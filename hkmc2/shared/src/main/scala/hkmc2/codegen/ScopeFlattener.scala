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
  *   do not contain nested lambdas, functions, handlers, or classes; otherwise locals could be
  *   moved out of scope incorrectly. This pass must therefore still run after the lifter, which
  *   is the pass that needs updating before more general loop-label flattening becomes valid.
  */
class ScopeFlattener extends BlockTransformer(new SymbolSubst):
  private var nestedScopedDefsAllowed = true
  
  private def withNestedScopedDefsAllowed[A](allowed: Bool)(body: => A): A =
    val prevNestedScopedDefsAllowed = nestedScopedDefsAllowed
    nestedScopedDefsAllowed = allowed
    try body
    finally nestedScopedDefsAllowed = prevNestedScopedDefsAllowed
  
  private def assertNestedScopedDefsAllowed(kind: Str): Unit =
    assert(nestedScopedDefsAllowed,
      s"ScopeFlattener cannot flatten loop labels whose bodies contain nested $kind; lift them before flattening")
  
  override def applyBlock(b: Block): Block = b match
    case Label(_, loop, body, _) =>
      if loop then withNestedScopedDefsAllowed(false)(super.applyBlock(b))
      else super.applyBlock(b)
    case _ => super.applyBlock(b)
  
  override def applyLam(lam: Lambda): Lambda =
    assertNestedScopedDefsAllowed("lambdas")
    super.applyLam(lam)
  
  override def applyHandler(hdr: Handler): Handler =
    assertNestedScopedDefsAllowed("handlers")
    super.applyHandler(hdr)
  
  override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
    case _: FunDefn =>
      assertNestedScopedDefsAllowed("functions")
      super.applyDefn(defn)(k)
    case _: ClsLikeDefn =>
      assertNestedScopedDefsAllowed("classes")
      super.applyDefn(defn)(k)
    case _ =>
      super.applyDefn(defn)(k)
  
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
