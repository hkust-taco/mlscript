package hkmc2
package codegen

import scala.annotation.tailrec

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst

import syntax.{Literal, Tree}
import semantics.*
import semantics.Elaborator.{Ctx, ctx}
import semantics.Elaborator.State
import hkmc2.Message.MessageContext
import hkmc2.syntax.Tree.DummyTypeDef

class BufferableTransform()(using Ctx, State, Raise):
  def transform(blk: Block): Block =
    val transformer = new BlockTransformer(SymbolSubst.Id):
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case cls: ClsLikeDefn if cls.k is syntax.Cls =>
          cls.bufferable.fold(super.applyDefn(defn)(k)): bufferable =>
            val companionSym = ModuleOrObjectSymbol(DummyTypeDef(syntax.Mod), new Tree.Ident(cls.sym.nme))
            val clsSizeSym = BlockMemberSymbol("size", Nil, false)
            val clsSizeTermSym = TermSymbol(syntax.ImmutVal, S(companionSym), new Tree.Ident("size"))
            val pubFieldMap: Map[Symbol, Symbol] = cls.publicFields.toMap
            val fields = cls.privateFields ++ cls.publicFields.map(_._2)
            val fieldMap: Map[Symbol, Int] = fields.zipWithIndex.toMap
            def mkSymbolReplacer(params: List[ParamList]): (List[ParamList], Map[SimpleSymbol, SimpleSymbol]) =
              val allVars = params.flatMap(_.allParams).map(_.sym)
              val varMap = allVars
                .map: sym =>
                  (sym, VarSymbol(sym.id))
                .toMap
              def mapParam(p: Param) =
                Param(p.flags, varMap(p.sym), p.sign, p.modulefulness)
              (params.map(pl => ParamList(pl.flags, pl.params.map(mapParam), pl.restParam.map(mapParam))), varMap.toMap)
            def mkFieldReplacer(buf: VarSymbol, baseIdx: VarSymbol, symMap: Map[SimpleSymbol, SimpleSymbol]) =
              def getOffset(off: Int)(k: Path => Block): Block =
                val idxSymbol = new TempSymbol(N, "idx")
                Scoped(Set.single(idxSymbol), Assign(idxSymbol, Call(State.builtinOpsMap("+").asSimpleRef, (baseIdx.asSimpleRef.asArg :: Value.Lit(Tree.IntLit(off)).asArg :: Nil) ne_:: Nil)(true, false, false),
                  k(DynSelect(buf.asSimpleRef.selSN("buf"), idxSymbol.asSimpleRef, true))))
              def assignToOffset(off: Int, r: Result, rst: Block) =
                val idxSymbol = new TempSymbol(N, "idx")
                Scoped(Set.single(idxSymbol), Assign(idxSymbol, Call(State.builtinOpsMap("+").asSimpleRef, (baseIdx.asSimpleRef.asArg :: Value.Lit(Tree.IntLit(off)).asArg :: Nil) ne_:: Nil)(true, false, false),
                  AssignDynField(buf.asSimpleRef.selSN("buf"), idxSymbol.asSimpleRef, true, r, applyBlock(rst))))
              new BlockTransformer(SymbolSubst.Id):
                override def applySimpleSymbol(sym: SimpleSymbol): SimpleSymbol = symMap.getOrElse(sym, sym)
                override def applyBlock(b: Block): Block = b match
                  case Assign(l: (LocalVarSymbol | TermSymbol), r, rst) =>
                    fieldMap.get(l).fold(super.applyBlock(b)): off =>
                      applyResult(r): r2 =>
                        assignToOffset(off, r2, applyBlock(rst))
                  case af @ AssignField(l, n, r, rst) =>
                    af.symbol.flatMap(sym => fieldMap.get(sym).orElse(pubFieldMap.get(sym).flatMap(fieldMap.get)))
                      .fold(super.applyBlock(b)): off =>
                        applyResult(r): r2 =>
                          assignToOffset(off, r2, applyBlock(rst))
                  case Define(defn: ValDefn, rst) =>
                    fieldMap.get(defn.tsym).fold(super.applyBlock(b)): off =>
                      applyResult(defn.rhs): r2 =>
                        assignToOffset(off, r2, applyBlock(rst))
                  case _ => super.applyBlock(b)
                override def applyPath(p: Path)(k: Path => Block): Block = p match
                  case sel: Select =>
                    sel.symbol.fold(super.applyPath(p)(k)): sym =>
                      fieldMap.get(sym).orElse(pubFieldMap.get(sym).flatMap(fieldMap.get(_))).fold(super.applyPath(p)(k)): off =>
                        getOffset(off): res =>
                          k(res)
                  case r: Value.Ref =>
                    fieldMap.get(r.symbol).fold(super.applyPath(p)(k)): off =>
                      getOffset(off): res =>
                        k(res)
                  case _ => super.applyPath(p)(k)
            def transformFunDefn(f: FunDefn, isCtor: Bool): FunDefn =
              val buf = VarSymbol(new Tree.Ident("buf"))
              val idx = VarSymbol(new Tree.Ident("idx"))
              val (newParams, symMap) = mkSymbolReplacer(f.params)
              val blk = mkFieldReplacer(buf, idx, symMap).applyBlock(f.body)
              FunDefn(f.owner, f.sym, TermSymbol(f.dSym.k, f.dSym.owner, f.dSym.id), PlainParamList(
                Param(FldFlags.empty, buf, N, Modulefulness.none) :: Param(FldFlags.empty, idx, N, Modulefulness.none) :: Nil) :: newParams,
                if isCtor then Begin(blk, Return(idx.asSimpleRef)) else blk)(configOverride = f.configOverride, annotations = f.annotations)
            val fakeCtor = transformFunDefn(FunDefn.withFreshSymbol(
                S(companionSym), 
                BlockMemberSymbol("ctor", Nil, false), 
                cls.paramsOpt.toList ::: cls.auxParams,
                Begin(cls.preCtor, cls.ctor),
              )(N, annotations = Nil), true)
            val fakeCompanion = ClsLikeBody(
              companionSym,
              fakeCtor :: cls.methods.map(transformFunDefn(_, false)),
              Nil,
              clsSizeSym -> clsSizeTermSym :: Nil,
              Define(ValDefn(clsSizeTermSym, clsSizeSym, Value.Lit(Tree.IntLit(fields.size)))(N, Nil), End()),
              annotations = Nil,
            )
            k:
              ClsLikeDefn(
                cls.owner,
                cls.isym,
                cls.sym,
                cls.ctorSym,
                cls.k,
                if bufferable then cls.paramsOpt else N,
                if bufferable then cls.auxParams else Nil,
                cls.parentPath,
                if bufferable then cls.methods else Nil,
                cls.privateFields,
                cls.publicFields,
                if bufferable then cls.preCtor else End(),
                if bufferable then cls.ctor else End(),
                S(fakeCompanion),
                cls.bufferable,
              )(cls.configOverride, cls.annotations)
        case _ => super.applyDefn(defn)(k)
    transformer.applyBlock(blk)
