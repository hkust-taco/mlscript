package hkmc2
package codegen

import scala.collection.mutable.{Map => MutMap, Set => MutSet, Buffer}

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*
import semantics.Elaborator.State

class SymbolRefresher(existingMapping: Map[Symbol, Symbol])(using State) extends BlockTransformer(SymbolSubst.Id):
  val mapping = MutMap.from(existingMapping)
  
  override def applyScopedBlock(b: Block): Block =
    b match
    case Scoped(syms, body) =>
      val newSyms = MutSet.empty[Symbol]
      val oldSyms = MutSet.empty[Symbol]
      for s <- syms.toList.sortBy(_.uid) do
        assert(!mapping.isDefinedAt(s), s"already defined: $s")
        val newS = s match
          case tmpSym: TempSymbol => new TempSymbol(N, tmpSym.nme)
          case bms: BlockMemberSymbol =>
            val newBms = new BlockMemberSymbol(bms.nme, Nil, bms.nameIsMeaningful)
            newBms.tsym = bms.tsym.map: t =>
              val newOwner: Opt[InnerSymbol] = t.owner.map: o =>
                existingMapping.get(o) match
                  case Some(inner: InnerSymbol) => inner
                  case _ => o
              val nt = new TermSymbol(t.k, newOwner, t.id)
              mapping(t) = nt
              oldSyms.add(t)
              nt
            newBms
          case varSym: VarSymbol => new VarSymbol(varSym.id)
          case _ => lastWords(s"unexpected symbol kind: $s")
        mapping(s) = newS
        oldSyms.add(s)
        newSyms.add(newS)
      val res = Scoped(newSyms, applyBlock(body))
      for s <- oldSyms do mapping.remove(s)
      res
    case _ => super.applyScopedBlock(b)
  override def applyBlock(b: Block): Block =
    b match
    case Assign(lhs, rhs, rest) =>
      applyResult(rhs): newRhs =>
        val newLhs = mapping.getOrElse(lhs, lhs)
        val newRest = applyBlock(rest)
        if (newLhs is lhs) && (newRhs is rhs) && (newRest is rest) then b else Assign(newLhs, newRhs, newRest)
    case Label(label, loop, body, rest) =>
      assert(!mapping.isDefinedAt(label))
      val newLabel = new LabelSymbol(label.trm, label.nme)
      mapping(label) = newLabel
      val newBody = applyBlock(body)
      mapping.remove(label)
      val newRest = applyBlock(rest)
      Label(newLabel, loop, newBody, newRest)
    case Break(label) => Break(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
    case Continue(label) => Continue(mapping.getOrElse(label, label).asInstanceOf[LabelSymbol])
    case _ => super.applyBlock(b)
  
  override def applyDefn(defn: Defn)(k: Defn => Block): Block =
    defn match
    case fun: FunDefn =>
      assert(fun.owner.isEmpty)
      // because fun sym is not treated as a free var, we refresh here
      var newlyCreated = false
      val (sym2, dSym2) = mapping.get(fun.sym) match
        case Some(s: BlockMemberSymbol) => (s, s.tsym.get)
        case None =>
          newlyCreated = true
          val newBms = new BlockMemberSymbol(fun.sym.nme, fun.sym.trees, fun.sym.nameIsMeaningful)
          val newDsym = fun.sym.tsym.map: tsym =>
            assert(tsym.owner.isEmpty)
            new TermSymbol(tsym.k, N, tsym.id)
          newBms.tsym = S(newDsym.get)
          mapping(fun.sym) = newBms
          (newBms, newDsym.get)
        case _ => die
      val oldParamSyms = Buffer.empty[VarSymbol]
      val params2 = fun.params.map:
        case ParamList(flags, params, N) =>
          ParamList(
            flags,
            params.map: 
              case Param(flags, sym, sign, modulefulness) =>
                oldParamSyms.append(sym)
                val newSym = new VarSymbol(sym.id)
                assert(!mapping.isDefinedAt(sym))
                mapping(sym) = newSym
                Param(flags, newSym, sign, modulefulness),
            N)
        case _ => TODO("rest params are not supported")
      val body2 = applyFunBodyLikeBlock(fun.body)
      for s <- oldParamSyms do mapping.remove(s)
      if newlyCreated then
        Scoped(Set.single(sym2), k(FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec, fun.configOverride)))
      else
        k(FunDefn(N, sym2, dSym2, params2, body2)(fun.forceTailRec, fun.configOverride))
    case defn @ ValDefn(tsym, sym, rhs) =>
      val (tsym2, sym2) = mapping.get(sym) match
        case None =>
          val newBms = new BlockMemberSymbol(sym.nme, sym.trees, sym.nameIsMeaningful)
          val newTsym = new TermSymbol(tsym.k, tsym.owner, tsym.id)
          newBms.tsym = S(newTsym)
          (newTsym, newBms)
        case S(bms: BlockMemberSymbol) =>
          (bms.tsym.get, bms)
        case _ => die
      applyPath(rhs): rhs2 =>
        k(ValDefn(tsym2, sym2, rhs2)(defn.configOverride))
    case _ => super.applyDefn(defn)(k)
  
  override def applyValue(v: Value)(k: Value => Block): Block = v match
    case Value.Ref(l, x) =>
      mapping.get(l) match
        case None => super.applyValue(v)(k)
        case Some(newBms: BlockMemberSymbol) => k(Value.Ref(newBms, newBms.tsym))
        case Some(newSym) => k(Value.Ref(newSym, N))
    case _ => super.applyValue(v)(k)
