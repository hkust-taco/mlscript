package hkmc2
package codegen

import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst

import syntax.{Literal, Tree, ParamBind}
import semantics.*
import semantics.Elaborator.ctx
import semantics.Elaborator.State
import hkmc2.Message.MessageContext
import hkmc2.syntax.Tree.DummyTypeDef

class BufferableTransform()(using State, Raise):
  def transform(blk: Block): Block =
    val transformer = new BlockTransformer(SymbolSubst()):
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case cls: ClsLikeDefn =>
          cls.bufferable.fold(super.applyDefn(defn)(k)): bufferable =>
            require(cls.k is syntax.Cls)
            require(cls.companion is N)
            val companionSym = ModuleOrObjectSymbol(DummyTypeDef(syntax.Mod), new Tree.Ident(cls.sym.nme))
            val clsSizeSym = BlockMemberSymbol("size", Nil, false)
            val clsSizeTermSym = TermSymbol(syntax.ImmutVal, S(companionSym), new Tree.Ident("size"))
            val fields = cls.privateFields ++ cls.publicFields.map(_._2)
            val fieldReplacer = new BlockTransformer(SymbolSubst()):
              override def applyPath(p: Path)(k: Path => Block): Block = ???
            val fakeCompanion = ClsLikeBody(
              companionSym,
              Nil, // TODO: methods
              Nil,
              clsSizeSym -> clsSizeTermSym :: Nil,
              Define(ValDefn(clsSizeTermSym, clsSizeSym, Value.Lit(Tree.IntLit(fields.size))), End()),
            )
            k:
              ClsLikeDefn(
                cls.owner,
                cls.isym,
                cls.sym,
                cls.k,
                cls.paramsOpt,
                cls.auxParams,
                cls.parentPath,
                cls.methods,
                cls.privateFields,
                cls.publicFields,
                cls.preCtor,
                cls.ctor,
                S(fakeCompanion),
                cls.bufferable,
              )
        case _ => super.applyDefn(defn)(k)
    transformer.applyBlock(blk)
