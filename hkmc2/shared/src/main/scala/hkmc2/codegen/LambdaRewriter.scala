package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import semantics.Elaborator.State
import hkmc2.syntax.Tree

object LambdaRewriter:
  
  def desugar(b: Block)(using State) =
    
    def rewriteOneBlk(b: Block) = b match
      case Assign(lhs, Lambda(params, body), rest) if !lhs.isInstanceOf[TempSymbol] =>
        val newSym = BlockMemberSymbol(lhs.nme, Nil,
          nameIsMeaningful = true // TODO: lhs.nme is not always meaningful
        )
        val defn = FunDefn.withFreshSymbol(N, newSym, params :: Nil, body)(false)
        val blk = blockBuilder
          .define(defn)
          .assign(lhs, defn.asPath)
          .rest(rest)
        (blk, Nil, List(newSym))
      case _ =>
        var lambdasList: List[((BlockMemberSymbol, TermSymbol), Lambda)] = Nil
        var newLambdaSyms: List[BlockMemberSymbol] = Nil
        val lambdaRewriter = new BlockDataTransformer(SymbolSubst()):
          override def applyResult(r: Result)(k: Result => Block): Block = r match
            case lam: Lambda => 
              val sym = BlockMemberSymbol("lambda", Nil, nameIsMeaningful = false)
              val tSym = TermSymbol.fromFunBms(sym, N)
              lambdasList ::= ((sym, tSym) -> super.applyLam(lam))
              newLambdaSyms ::= sym
              k(Value.Ref(sym, S(tSym)))
            case _ => super.applyResult(r)(k)
        val blk = lambdaRewriter.applyBlock(b)
        (blk, lambdasList, newLambdaSyms)
    
    val transformer = new BlockTransformer(SymbolSubst()):
      private var surroundingScopedSyms = Option.empty[collection.mutable.Set[Symbol]]
      override def applyScopedBlock(b: Block): Block =
        val prevsurroundingScopedSyms = surroundingScopedSyms
        val res = b match
          case Scoped(syms, body) => 
            surroundingScopedSyms = Some(collection.mutable.Set.from(syms))
            val newBody = applySubBlock(body)
            if newBody is body then b
            else new Scoped(surroundingScopedSyms.get, newBody)
          case _ =>
            surroundingScopedSyms = Some(collection.mutable.Set.empty[Symbol])
            val newBlk = applySubBlock(b)
            if newBlk is b then b
            else new Scoped(surroundingScopedSyms.get, newBlk)
        surroundingScopedSyms = prevsurroundingScopedSyms
        res
      
      override def applyBlock(b: Block): Block =
        val (newBlk, lambdasList, newLambdaSyms) = rewriteOneBlk(b)
        val lambdaDefns = lambdasList.map:
          case (sym, Lambda(params, body)) =>
            FunDefn(N, sym._1, sym._2, params :: Nil, body)(false)
        val ret = lambdaDefns.foldLeft(newBlk):
          case (acc, defn) => Define(defn, acc)
        surroundingScopedSyms.foreach(_.addAll(newLambdaSyms))
        super.applyBlock(ret)
    
    transformer.applyBlock(b)
  

