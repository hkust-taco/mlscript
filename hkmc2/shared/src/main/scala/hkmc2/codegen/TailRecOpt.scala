package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import hkmc2.Message.*
import hkmc2.semantics.Elaborator.State
import hkmc2.syntax.Tree

// This optimization assumes the lifter has been run.
// It technically still works without lifting, but it will only consider calls to functions defined in the same scope.
class TailRecOpt(using State, TL, Raise):
  
  object CallToFun:
    def unapply(c: Call): Opt[TermSymbol] = c match
      case Call(fun = Value.Ref(b, S(r: TermSymbol))) => S(r)
      case _ => N
  
  sealed abstract class CallEdge:
    val f1: TermSymbol
    val f2: TermSymbol
    val call: Call
  
  case class TailCall(f1: TermSymbol, f2: TermSymbol)(val call: Call) extends CallEdge
  case class NormalCall(f1: TermSymbol, f2: TermSymbol)(val call: Call) extends CallEdge
  
  class CallFinder(f: FunDefn) extends BlockTraverserShallow:
    
    var edges: List[CallEdge] = Nil
    
    def find =
      println(f.sym)
      edges = Nil
      applyBlock(f.body)
      edges
    
    override def applyBlock(b: Block): Unit = b match
      case Return(c @ CallToFun(r), _) => edges ::= TailCall(f.dSym, r)(c)
      case Assign(a, c @ CallToFun(r), Return(b, _)) if a == b => edges ::= TailCall(f.dSym, r)(c)
      case Return(c: Call, _) =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"Only direct calls in tail position may be marked @tailcall." -> c.toLoc :: Nil))
      case _ => super.applyBlock(b)
      
    override def applyResult(r: Result): Unit = r match
      case c: Call =>
        if c.explicitTailCall then
          raise(ErrorReport(msg"This call is not in tail position." -> c.toLoc :: Nil))
        c match
          case CallToFun(r) => edges ::= NormalCall(f.dSym, r)(c)
          case _ =>
      case _ => super.applyResult(r)
  
  def buildCallGraph(fs: List[FunDefn]): List[CallEdge] =
    fs.flatMap(f => CallFinder(f).find)
  
  case class SccOfCalls(funs: List[FunDefn], calls: List[CallEdge])
  
  def partFns(fs: List[FunDefn]): List[SccOfCalls] =
    val defnSyms = fs.map(_.dSym)
    val tsToDefn = fs.map(f => f.dSym -> f).toMap
    
    // Only care about calls to functions in the same scope
    // Note that the results may differ if the lifter has been run.
    val cg = buildCallGraph(fs).filter: c =>
      val cond = defnSyms.contains(c.f1) && defnSyms.contains(c.f2)
      c.match
        case c: TailCall if c.call.explicitTailCall && !cond =>
          raise(ErrorReport(
            msg"This tail call exits the current scope and cannot be optimized. Enabling the lifter may fix this." -> c.call.toLoc :: Nil))
        case _ =>
      cond
    
    val cgTup = cg.map(c => (c.f1, c.f2))
    val sccs = algorithms.sccsWithInfo(cgTup, Nil)
    
    // partition the call graph
    val sccMap = sccs.sccs.flatMap:
      case (id, scc) => scc.map(f => f -> id)
    
    val cgLabelled = cg
      .groupBy: c =>
        val s1 = sccMap(c.f1)
        val s2 = sccMap(c.f2)
        if s1 != s2 && c.call.explicitTailCall then
          raise(ErrorReport(
            msg"This call is not optimized as it does not directly recurse through its parent function." -> c.call.toLoc :: Nil))
          -1
        else s1
      .filter:
        (id, _) => id != -1
    
    sccs.sccs.toList.map: v =>
      val (id, tss) = v
      val cgs = cgLabelled.get(id) match
        case Some(value) => value
        case None => Nil
      SccOfCalls(tss.map(tsToDefn), cgs)
  
  def optFunctions(fs: List[FunDefn], owner: Opt[InnerSymbol]) =
    val parts = partFns(fs)
  
  def transform(b: Block) =
    val (blk, defns) = b.floatOutDefns()
    val (funs, clses) = 
      defns.foldLeft[(List[FunDefn], List[ClsLikeDefn])](Nil, Nil):
        case ((fs, cs), d) => d match
          case f: FunDefn => (f :: fs, cs)
          case c: ClsLikeDefn => (fs, c :: cs)
          case _ => (fs, cs) // unreachable as floatOutDefns only floats out FunDefns and ClsLikeDefns
    print(optFunctions(funs, N))
    b
