package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import semantics.Elaborator.State
import hkmc2.syntax.Tree

object LambdaRewriter:
  
  def desugar(b: Program)(using State) =
    
    val transformer = new BlockTransformer(SymbolSubst.Id):
      
      override def applyResult(r: Result)(k: Result => Block): Block = r match
        case lam: Lambda =>
          val sym = BlockMemberSymbol("lambda", Nil, nameIsMeaningful = false)
          val lam2 = super.applyLam(lam)
          val Lambda(params, body) = lam2
          val lamDefn = FunDefn.withFreshSymbol(N, sym, params :: Nil, body)(N, annotations = Annot.Private :: lam2.annot)
          Scoped(Set.single(sym), Define(lamDefn, k(lamDefn.asPath)))
        case _ => super.applyResult(r)(k)
      
      // Special-case Assign to avoid creating a temporary symbol for the lambda
      override def applyBlock(b: Block): Block = b match
        case Assign(lhs, lam @ Lambda(params, body), rest) if !lhs.isInstanceOf[TempSymbol] =>
          val newSym = BlockMemberSymbol(lhs.nme, Nil,
            nameIsMeaningful = true // TODO: lhs.nme is not always meaningful
          )
          val defn = FunDefn.withFreshSymbol(N, newSym, params :: Nil, applyBlock(body))
            (N, annotations = Annot.Private :: lam.annot)
          val blk = blockBuilder
            .define(defn)
            .assign(lhs, defn.asPath)
            .rest(applyBlock(rest))
          Scoped(Set.single(newSym), blk)
        case _ => super.applyBlock(b)
    
    transformer.applyProgram(b)
  
  
