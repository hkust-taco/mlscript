package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import sourcecode.Line

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State


/** `symbolsToPreserve` is the set of local symbols we want to leave alone;
  * typically, these will be top-level symbols that are being exported from a diff-test block;
  * we don't want to eliminate these. */
class BlockSimplifier(symbolsToPreserve: Set[Local])(using DebugPrinter, State):
  
  
  private var changed = true
  
  def registerChange = changed = true
  // * For debugging:
  // def registerChange(using line: Line) = { println(s"Change at line ${line.value}"); changed = true }
  
  def apply(prog: Program): Program =
    var res = prog
    while changed do
      changed = false
      res = new DeadCodeElim().apply(res)
      // TODO: other simplifications, such as inlining
    res
  end apply
  
  
  class DeadCodeElim() extends BlockTransformer(SymbolSubst.Id):
    
    
    val usedLabels = MutSet.empty[LabelSymbol]
    val definedVars = MutSet.empty[Local]
    val localVars = MutSet.empty[Local]
    val usedVars = MutSet.empty[Local]
    
    def apply(prog: Program): Program =
      
      new BlockTraverser:
        
        applyProgram(prog)
        
        override def applyDefn(defn: Defn): Unit =
          defn match
          case cls: ClsLikeDefn =>
            localVars ++= cls.privateFields
            cls.companion.foreach(localVars ++= _.privateFields)
          case _ =>
          super.applyDefn(defn)
        
        override def applyPath(p: Path): Unit =
          p match
            case Value.Ref(loc, _) =>
              usedVars += loc
            case _ =>
          super.applyPath(p)
        
        override def applyBlock(b: Block): Unit =
          b match
            case Define(defn, rst) =>
              definedVars += defn.sym
            case Scoped(syms, _) =>
              localVars ++= syms
            case Break(lbl) => usedLabels += lbl
            case Continue(lbl) => usedLabels += lbl
            case Assign(lhs, rhs, rst) =>
              definedVars += lhs
            case _ =>
          super.applyBlock(b)
      
      applyProgram(prog)
    
    
    // * Cached analysis to find which labels are the targets of `break`s in a given block
    object BrokenLabels extends CachedAnalysis[Block, Set[LabelSymbol]]:
      
      def analyzeUncached(block: Block): Set[LabelSymbol] = block match
        case Break(lbl) => Set.single(lbl)
        case _ => block.subBlocks.iterator.flatMap(analyze).toSet
      
    end BrokenLabels
    
    
    // * Cached analysis to find whether a block is abortive
    // * (i.e. always throws, returns, breaks, continues, or is unreachable)
    object AbortiveAnalysis extends CachedAnalysis[Block, Bool]:
      
      def analyzeUncached(block: Block): Bool = block match
        case Scoped(syms, body) =>
          body.analyze
        case Match(scrut, arms, dflt, rest) =>
          rest.analyze || arms.forall(_._2.analyze) && dflt.exists(_.analyze)
        case Begin(sub, rest) =>
          sub.analyze || rest.analyze
        case Define(defn, rest) =>
          // TODO: we could also analyse the effects of the extends clauses and companion module ctor
          rest.analyze
        case x: (Assign | AssignField | AssignDynField) =>
          x.rest.analyze
        case TryBlock(sub, finallyDo, rest) =>
          sub.analyze || rest.analyze
        case Label(lbl, loop, bod, rst) =>
          bod.analyze
            && !BrokenLabels.analyze(bod).contains(lbl) // if `bod` breaks to `lbl`, then we must consider `rst`
            || rst.analyze
        case _: Throw | Return(_, false) | _: Unreachable | _: Continue | _: Break => true
        case Return(_, true) => false
        case _: End => false
        case HandleBlock(lhs, res, par, args, cls, handlers, body, rest) =>
          body.analyze || rest.analyze
        
    end AbortiveAnalysis
    
    
    val removedLocals: MutSet[Local] = MutSet.empty
    
    override def applyValue(v: Value)(k: Value => Block) = v match
      // * Replace with `undefined` those references to local variables that are never assigned
      case Value.Ref(loc, N) if localVars.contains(loc) && !definedVars.contains(loc) =>
        registerChange
        if !symbolsToPreserve(loc) then removedLocals += loc
        k(Value.Lit(syntax.Tree.UnitLit(false)))
      case _ => super.applyValue(v)(k)
    
    override def applyBlock(b: Block): Block = b match
      
      // * Discard assignments to local variables that are never read (and are not preserved)
      case Assign(lhs, rhs, rst) if localVars(lhs) && !usedVars(lhs) && !symbolsToPreserve(lhs) =>
        registerChange
        removedLocals += lhs
        applyResult(rhs)(r => Assign.discard(r, applyBlock(rst)))
      
      // * Remove local pure definitions that are never read (and are not preserved)
      case Define(defn, rest) =>
        if !defn.isPure
        || !localVars(defn.sym)
        || usedVars(defn.sym)
        || symbolsToPreserve(defn.sym)
        then super.applyBlock(b)
        else
          registerChange
          removedLocals += defn.sym
          applyBlock(rest)
        
      // * Simplify labelled blocks
      case Label(lbl, loop, bod, rst) =>
        if !BrokenLabels.analyze(bod).contains(lbl) && AbortiveAnalysis.analyze(bod) && !rst.isInstanceOf[Unreachable] then
          registerChange
          val unr = Unreachable("Rest of abortive labelled block")
          if usedLabels.contains(lbl)
          then Label(lbl, loop, applyBlock(bod), unr)
          else Begin(applyBlock(bod), unr)
        else
          if usedLabels.contains(lbl) then super.applyBlock(b)
          else
            registerChange
            Begin(applyBlock(bod), applyBlock(rst))
      
      case x => super.applyBlock(x)
    
    
    // FIXME: refactor transformers so this is not so error-prine (adding this case to `applyBlock` doesn't work)
    override def applyScopedBlock(b: Block): Block = b match
      // * Delete removed local variables from Scoped blocks
      case Scoped(syms, body) =>
        val body2 = applyBlock(body)
        // println(s">> $body2 ${body is body2}")
        // println(s">> $body2 ${changed}")
        if changed then
        // if changed || (body isnt body2) then
          val syms2 = syms.filterNot(removedLocals)
          // println(s">> $syms $syms2 ${removedLocals}")
          if syms2.size === syms.size && (body2 is body) then b
          else Scoped(syms2, body2)
        else b
      case _ => super.applyScopedBlock(b)
      
    
  end DeadCodeElim
  
  
end BlockSimplifier


