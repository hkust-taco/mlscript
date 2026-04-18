package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import semantics.Elaborator.State
import hkmc2.syntax.Tree

object LambdaRewriter:
  
  def desugar(b: Block)(using State) =
    val transformer = new BlockTransformer(SymbolSubst.Id):
      override def applyResult(r: Result)(k: Result => Block): Block = r match
        case lam: Lambda =>
          val sym = BlockMemberSymbol("lambda", Nil, nameIsMeaningful = false)
          val Lambda(params, body) = super.applyLam(lam)
          val lamDefn = FunDefn.withFreshSymbol(N, sym, params :: Nil, body)(false, N, Visibility.Public)
          Scoped(Set.single(sym), Define(lamDefn, k(lamDefn.asPath)))
        case _ => super.applyResult(r)(k)
      
      override def applyBlock(b: Block): Block = b match
        case Assign(lhs, Lambda(params, body), rest) if !lhs.isInstanceOf[TempSymbol] =>
          val newSym = BlockMemberSymbol(lhs.nme, Nil,
            nameIsMeaningful = true // TODO: lhs.nme is not always meaningful
          )
          val defn = FunDefn.withFreshSymbol(N, newSym, params :: Nil, applyBlock(body))(false, N, Visibility.Public)
          val blk = blockBuilder
            .define(defn)
            .assign(lhs, defn.asPath)
            .rest(applyBlock(rest))
          Scoped(Set.single(newSym), blk)
        case _ => super.applyBlock(b)
    
    transformer.applyBlock(b)
  

