package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.*
import semantics.Elaborator.State

object LambdaRewriter:
  def desugar(b: Block)(using State) =
    def rewriteOneBlk(b: Block) = b match
      case Assign(lhs, Value.Lam(params, body), rest) if !lhs.isInstanceOf[TempSymbol] =>
        val newSym = BlockMemberSymbol(lhs.nme, Nil,
          nameIsMeaningful = true // TODO: lhs.nme is not always meaningful
        )
        val blk = blockBuilder
          .define(FunDefn(N, newSym, params :: Nil, body))
          .assign(lhs, newSym.asPath)
          .rest(rest)
        (blk, Nil)
      case _ =>
        var lambdasList: List[(BlockMemberSymbol, Value.Lam)] = Nil
        val lambdaRewriter = new BlockDataTransformer(SymbolSubst()):
          override def applyValue(v: Value): Value = v match
            case lam: Value.Lam => 
              val sym = BlockMemberSymbol("lambda", Nil, nameIsMeaningful = false)
              lambdasList ::= (sym -> super.applyLam(lam))
              Value.Ref(sym)
            case _ => super.applyValue(v)
        val blk = lambdaRewriter.applyBlock(b)
        (blk, lambdasList)

    val transformer = new BlockTransformer(SymbolSubst()):
      override def applyBlock(b: Block): Block =
        val (newBlk, lambdasList) = rewriteOneBlk(b)
        val lambdaDefns = lambdasList.map:
          case (sym, Value.Lam(params, body)) =>
            FunDefn(N, sym, params :: Nil, body)
        val ret = lambdaDefns.foldLeft(newBlk):
          case (acc, defn) => Define(defn, acc)
        super.applyBlock(ret)
    transformer.applyBlock(b)
