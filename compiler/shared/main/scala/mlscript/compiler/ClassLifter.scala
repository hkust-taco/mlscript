package mlscript.compiler

import mlscript.*
import mlscript.utils.StringOps
import scala.collection.mutable.StringBuilder as StringBuilder
import scala.collection.mutable.Map as MMap
import scala.collection.mutable.Set as MSet
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.codegen.CodeGenError

class ClassLifter(logDebugMsg: Boolean = false) { 
  type ClassName = String
  type FieldName = String
  case class LocalContext(vSet: Set[Var], tSet: Set[TypeName]){
    def ++(rst: LocalContext) = LocalContext(vSet ++ rst.vSet, tSet ++ rst.tSet)
    def -+(rst: LocalContext) = LocalContext(vSet -- rst.vSet, tSet ++ rst.tSet)
    def addV(rst: IterableOnce[Var]) = LocalContext(vSet ++ rst, tSet)
    def addV(nV: Var) = LocalContext(vSet + nV, tSet)
    def extV(rst: IterableOnce[Var]) = LocalContext(vSet -- rst, tSet)
    def extV(nV: Var) = LocalContext(vSet - nV, tSet)
    def addT(rst: IterableOnce[TypeName]) = LocalContext(vSet, tSet ++ rst)
    def addT(nT: TypeName) = LocalContext(vSet, tSet + nT)
    def extT(rst: IterableOnce[TypeName]) = LocalContext(vSet, tSet -- rst)
    def vSet2tSet = LocalContext(Set(), vSet.map(t => TypeName(t.name)))
    def moveT2V(ts: Set[TypeName]) = {
      val inters = tSet.intersect(ts)
      LocalContext(vSet ++ inters.map(x => Var(x.name)), tSet -- inters)
    }
    def intersect(rst: LocalContext) = LocalContext(vSet intersect rst.vSet, tSet intersect rst.tSet)
    def contains(v: Var) = vSet.contains(v) || tSet.contains(TypeName(v.name))
    def contains(tv: TypeName) = vSet.contains(Var(tv.name)) || tSet.contains(tv)
    override def toString(): String = "(" ++ vSet.mkString(", ") ++ "; " ++ tSet.mkString(", ") ++ ")"
  }
  private def asContext(v: Var) = LocalContext(Set(v), Set())
  private def asContextV(vS: IterableOnce[Var]) = LocalContext(vS.iterator.toSet, Set())
  private def asContext(t: TypeName) = LocalContext(Set(), Set(t))
  private def asContextT(tS: IterableOnce[TypeName]) = LocalContext(Set(), tS.iterator.toSet)
  private def emptyCtx = LocalContext(Set(), Set())

  case class ClassInfoCache(
    originNm: TypeName, 
    liftedNm: TypeName, 
    var capturedParams: LocalContext, 
    fields: MSet[Var], 
    innerClses: MMap[TypeName, ClassInfoCache], 
    supClses: Set[TypeName],
    outerCls: Option[ClassInfoCache],
    body: NuTypeDef, 
    depth: Int
  ){
    override def toString(): String = liftedNm.name ++ "@" ++ capturedParams.toString() ++ "^" ++ outerCls.map(_.liftedNm.toString()).getOrElse("_")
  }
  type ClassCache = Map[TypeName, ClassInfoCache]
  type NamePath = List[String]

  var retSeq: List[NuTypeDef] = Nil
  var anonymCnt: Int = 0
  var clsCnt: Int = 0
  val logOutput: StringBuilder = new StringBuilder
  val primiTypes = new mlscript.Typer(false, false, false).primitiveTypes

  private def log(str: String): Unit = {
    logOutput.append(str)
    if(logDebugMsg){
      println(str)
    }
  }
  def getLog: String = logOutput.toString()

  private def genAnoName(textNm: String = "Ano"): String = {
    anonymCnt = anonymCnt + 1
    textNm ++ "$" ++ anonymCnt.toString()
  }

  private def genParName(clsNm: String): String = "par$" ++ clsNm
  
  private def genInnerName(outerClsNm: TypeName, innerNm: String) = {
    clsCnt = clsCnt+1
    outerClsNm.name ++ "_" ++ innerNm ++ "$" ++ clsCnt.toString()
  }

  private def tupleEntityToVar(fld: (Option[Var], Fld)): Option[Var] = fld match{
    case (None, Fld(_, _, v: Var)) => Some(v)
    case (Some(v: Var), _) => Some(v)
    case _ => None
  }

  private def getFields(etts: List[Statement]): Set[Var] = {
    etts.flatMap{
      case NuFunDef(_, nm, _, _) => Some(nm)
      case NuTypeDef(_, TypeName(nm), _, _, _, _) => Some(Var(nm))
      case Let(_, name, _, _) => Some(name)
      case _ => None 
    }.toSet
  }

  private def selPath2Term(path: List[String], varNm: Var): Term = path match {
    case Nil => varNm
    case (head :: tail) => Sel(selPath2Term(tail, Var(head)), varNm)
  }

  private def buildPathToVar(v: Var)(using outer: Option[ClassInfoCache]): Option[Term] = {
    def findField(ot: Option[ClassInfoCache]): Option[List[TypeName]] = {
      ot match{
        case None => None
        case Some(info) => 
          if(info.fields.contains(v) || info.capturedParams.vSet.contains(v))
            Some(List(info.liftedNm))
          else findField(info.outerCls).map(l => info.liftedNm :: l)
      }
    }
    val tmp = findField(outer)
    tmp.map(l => {
      selPath2Term(l.map(x => genParName(x.name)).updated(0, "this").reverse, v)
    })
  }
  private def toFldsEle(trm: Term): (Option[Var], Fld) = (None, Fld(false, false, trm))

  def getSupClsInfoByTerm(parentTerm: Term): (List[TypeName], List[(Var, Fld)]) = parentTerm match{
    case Var(nm) => List(TypeName(nm)) -> Nil
    case App(Var(nm), _: Tup) => List(TypeName(nm)) -> Nil
    case App(App(Var("&"), t1), t2) => 
      val ret1 = getSupClsInfoByTerm(t1)
      val ret2 = getSupClsInfoByTerm(t2)
      (ret1._1 ++ ret2._1) -> (ret1._2 ++ ret2._2)
    case TyApp(trm, targs) => getSupClsInfoByTerm(trm)
    //SPECIAL CARE: Tup related issue
    case Tup(flds) => 
      val ret = flds.filter(_._1.isEmpty).map(fld => getSupClsInfoByTerm(fld._2.value)).unzip
      ret._1.flatten -> ret._2.fold(Nil)(_ ++ _)
    case Bra(rcd, trm) => getSupClsInfoByTerm(trm)
    case Rcd(fields) => (Nil, fields)
    case _ => (Nil, Nil)
  }
  
  private def splitEntities(etts: List[Statement]) = {
    val tmp = etts.map{
      case cls: NuTypeDef => (Some(cls), None, None)
      case func: NuFunDef => (None, Some(func), None)
      case trm: Term => (None, None, Some(trm))
      case others => throw CodeGenError(s"Not supported entity type: $others")
    }.unzip3
    (tmp._1.flatten, tmp._2.flatten, tmp._3.flatten)
  }

  private def genClassNm(orgNm: String)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): TypeName = {
    TypeName(outer match{
      case None => 
        clsCnt = clsCnt+1
        orgNm ++ "$" ++ clsCnt.toString()
      case Some(value) => genInnerName(value.liftedNm, orgNm)
    })
  }

  private def getFreeVars(stmt: Located)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): LocalContext = stmt match{
    case v:Var => 
      log(s"get free var find $v: ${ctx.vSet.contains(v)}/${buildPathToVar(v).isDefined}/${cache.contains(TypeName(v.name))}/${v.name.equals("this")}")
      if(ctx.vSet.contains(v) || buildPathToVar(v).isDefined || cache.contains(TypeName(v.name)) || v.name.equals("this") || primiTypes.contains(v.name)) then emptyCtx else asContext(v)
    case t: NamedType => 
      log(s"get type $t under $ctx, $cache, $outer")
      asContextT(t.collectTypeNames.map(TypeName(_)).filterNot(x => ctx.contains(x) || cache.contains(x) || primiTypes.contains(x.name)))
    case Lam(lhs, rhs) => 
      val lhsVs = getFreeVars(lhs)
      getFreeVars(rhs)(using ctx ++ lhsVs) -+ lhsVs
    case NuFunDef(_, vm, tps, Left(trm)) =>
      getFreeVars(trm).extV(vm).extT(tps)
    case OpApp(_, trm) => getFreeVars(trm)
    case Sel(trm, _) => getFreeVars(trm)
    case Asc(trm, tp) =>
      getFreeVars(trm) ++ getFreeVars(tp)
    case Tup(tupLst) => 
      tupLst.map{
        case (Some(v), Fld(_, _, trm)) => getFreeVars(trm).vSet2tSet.addV(v)
        case (_, Fld(_, _, rhs)) => getFreeVars(rhs)
      }.fold(emptyCtx)(_ ++ _)
    case Rcd(fields) => 
      fields.map{
        case (v, Fld(_, _, trm)) => getFreeVars(trm).vSet2tSet
      }.fold(emptyCtx)(_ ++ _)
    case TyApp(trm, tpLst) =>
      getFreeVars(trm).addT(tpLst.flatMap(_.collectTypeNames.map(TypeName(_))))
    case NuTypeDef(_, nm, tps, param, pars, body) =>
      val prmVs = getFreeVars(param)(using emptyCtx, Map(), None)
      val newVs = prmVs.vSet ++ getFields(body.entities) + Var(nm.name)
      val nCtx = ctx.addV(newVs).addT(nm).addT(tps)
      val parVs = pars.map(getFreeVars(_)(using nCtx)).fold(emptyCtx)(_ ++ _)
      val bodyVs = body.entities.map(getFreeVars(_)(using nCtx)).fold(emptyCtx)(_ ++ _)
      (bodyVs ++ parVs -+ prmVs).extT(tps)
    case Blk(stmts) => 
      val newVs = getFields(stmts)
      stmts.map(getFreeVars(_)(using ctx.addV(newVs))).fold(emptyCtx)(_ ++ _)
    case Let(isRec, name, rhs, body) => 
      getFreeVars(rhs)(using ctx.addV(name)) ++ getFreeVars(body)(using ctx.addV(name))
    case others =>
      others.children.map(getFreeVars).fold(emptyCtx)(_ ++ _)
  }

  private def collectClassInfo(cls: NuTypeDef, preClss: Set[TypeName])(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): ClassInfoCache = {
    val NuTypeDef(_, nm, tps, param, pars, body) = cls
    log(s"grep context of ${cls.nme.name} under {\n$ctx\n$cache\n$outer\n}\n")
    val (clses, funcs, trms) = splitEntities(cls.body.entities)
    val (supNms, rcdFlds) = pars.map(getSupClsInfoByTerm).unzip
    val flds = rcdFlds.flatten.map{
      case (v, Fld(_, _, trm)) => 
        val tmp = getFreeVars(trm)(using emptyCtx)
        val ret = tmp.tSet ++ tmp.vSet.map(x => TypeName(x.name))
        (v, ret)
    }.unzip
    log(s"par record: ${flds._2.flatten}")
    val fields = (param.fields.flatMap(tupleEntityToVar) ++ funcs.map(_.nme) ++ clses.map(x => Var(x.nme.name)) ++ trms.flatMap(grepFieldsInTrm) ++ flds._1).toSet
    val nCtx = ctx.addV(fields).addV(flds._1).extT(tps)
    val tmpCtx = ((body.entities.map(getFreeVars(_)(using nCtx)) ++ pars.map(getFreeVars(_)(using nCtx))).fold(emptyCtx)(_ ++ _).moveT2V(preClss)
                  ).addT(flds._2.flatten.toSet).extV(supNms.flatten.map(x => Var(x.name)))

    log(s"ret ctx for ${cls.nme.name}: $tmpCtx")
    val ret = ClassInfoCache(nm, genClassNm(nm.name), tmpCtx, MSet(fields.toSeq: _*), MMap(), supNms.flatten.toSet, outer, cls, outer.map(_.depth).getOrElse(0)+1)
    ret
  }

  private def liftCaseBranch(brn: CaseBranches)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (CaseBranches, LocalContext) = brn match{
    case Case(v: Var, body, rest) => 
      val nTrm = liftTermNew(body)(using ctx.addV(v))
      val nRest = liftCaseBranch(rest)
      (Case(v, nTrm._1, nRest._1), nTrm._2 ++ nRest._2)
    case Case(pat, body, rest) => 
      val nTrm = liftTermNew(body)
      val nRest = liftCaseBranch(rest)
      (Case(pat, nTrm._1, nRest._1), nTrm._2 ++ nRest._2)
    case Wildcard(body) => 
      val nTrm = liftTermNew(body)
      (Wildcard(nTrm._1), nTrm._2)
    case NoCases => (brn, emptyCtx)
  }

  private def liftIf(body: IfBody)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (IfBody, LocalContext) = body match{
    case IfElse(expr) => 
      val ret = liftTermNew(expr)
      (IfElse(ret._1), ret._2)
    case IfThen(expr, rhs) => 
      val nE = liftTermNew(expr)
      val nR = liftTermNew(rhs)
      (IfThen(nE._1, nR._1), nE._2 ++ nR._2)
    case _ => ???
  }

  private def liftTuple(tup: Tup)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (Tup, LocalContext) = {
    val ret = tup.fields.map{
        case (None, Fld(b1, b2, trm)) => 
          val tmp = liftTermNew(trm)
          ((None, Fld(b1, b2, tmp._1)), tmp._2)
        case (Some(v), Fld(b1, b2, trm)) =>
          val nTrm = liftTermAsType(trm)
          ((Some(v), Fld(b1, b2, nTrm._1)), nTrm._2)
      }.unzip
    (Tup(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
  }

  private def liftConstr(tp: TypeName, prm: Tup)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (TypeName, Tup, LocalContext) = {
    def findAncestor(crt: ClassInfoCache, target: Option[ClassInfoCache]): Option[(List[String], Option[String])] = {
      (crt.outerCls, target) match{
        case (None, None) =>  None
        case (Some(c1), Some(c2)) if c1.depth == c2.depth => Some((crt.liftedNm.name :: Nil, Some(genParName(c1.liftedNm.name))))
        case (Some(c1), _) => findAncestor(c1, target).map(l => (crt.liftedNm.name :: l._1, l._2))
        case (None, _) => Some(Nil, None)
      }
    }
    log(s"lift constr for $tp$prm under $ctx, $cache, $outer")
    if(!cache.contains(tp)){
      throw new CodeGenError(s"Cannot find type ${tp.name}. Class values are not supported in lifter. ")
    }
    else {
      val cls@ClassInfoCache(_, nm, capParams, _, _, _, out, _, _) = cache.get(tp).get
      val nParams = liftTuple(Tup(prm.fields ++ capParams.vSet.toList.map(toFldsEle(_))))
      if(outer.isDefined){
        log("find ancestor " + outer.get + " & " + cls)
        findAncestor(outer.get, out) match{
          case None => 
            log("case 1")
            (nm, nParams._1, nParams._2)
          case Some((selPt, Some(varNm))) =>
            log("case 2")
            (nm, Tup(toFldsEle(selPath2Term(selPt.map(genParName).updated(0, "this").reverse, Var(varNm))) :: nParams._1.fields), nParams._2) 
          case Some((_, None)) =>
            log("case 3")
            (nm, Tup(toFldsEle(Var("this")) :: nParams._1.fields), nParams._2) 
        }
      }
      else (nm, nParams._1, nParams._2)
    }
  }

  private def liftTermNew(target: Term)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (Term, LocalContext) = target match{
    case v: Var => 
      if(ctx.contains(v) || v.name.equals("this") || primiTypes.contains(v.name))   (v, emptyCtx)
      else if(cache.contains(TypeName(v.name))){
        val ret = liftConstr(TypeName(v.name), Tup(Nil))
        App(Var(ret._1.name), ret._2) -> ret._3
      }
      else {
        buildPathToVar(v) match{
          case Some(value) => (value, emptyCtx)
          case None => (v, asContext(v))
        }
      }
    case Lam(lhs, rhs) => 
      val lctx = getFreeVars(lhs)(using emptyCtx, cache, None)
      val (ltrm, _) = liftTermNew(lhs)(using ctx.addV(lctx.vSet))
      val (rtrm, rctx) = liftTermNew(rhs)(using ctx.addV(lctx.vSet))
      (Lam(ltrm, rtrm), rctx -+ lctx)
    case t: Tup => 
      liftTuple(t)
    case Rcd(fields) => 
      val ret = fields.map{
        case (v, Fld(b1, b2, trm)) => 
          val tmp = liftTermAsType(trm)
          ((v, Fld(b1, b2, tmp._1)), tmp._2)
      }.unzip
      (Rcd(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
    case Asc(trm, ty) => 
      val ret = liftTermNew(trm)
      val nTy = liftType(ty)
      (Asc(ret._1, nTy._1), ret._2 ++ nTy._2)
    case App(v: Var, prm: Tup) if cache.contains(TypeName(v.name)) => 
      val ret = liftConstr(TypeName(v.name), prm)
      (App(Var(ret._1.name), ret._2), ret._3)
    case App(lhs, rhs) => 
      val (ltrm, lctx) = liftTermNew(lhs)
      val (rtrm, rctx) = liftTermNew(rhs)
      (App(ltrm, rtrm), lctx ++ rctx)
    case Assign(lhs, rhs) => 
      val (ltrm, lctx) = liftTermNew(lhs)
      val (rtrm, rctx) = liftTermNew(rhs)
      (Assign(ltrm, rtrm), lctx ++ rctx)
    case Bind(lhs, rhs) => 
      val (ltrm, lctx) = liftTermNew(lhs)
      val (rtrm, rctx) = liftTermAsType(rhs)
      (Bind(ltrm, rtrm), lctx ++ rctx)
    case Bra(rcd, trm) => 
      val ret = liftTermNew(trm)
      (Bra(rcd, ret._1), ret._2)
    case CaseOf(trm, cases) => 
      val nTrm = liftTermNew(trm)
      val nCases = liftCaseBranch(cases)
      (CaseOf(nTrm._1, nCases._1), nTrm._2 ++ nCases._2)
    case If(body, None) => 
      val ret = liftIf(body)
      (If(ret._1, None), ret._2)
    case If(body, Some(trm)) => 
      val ret = liftIf(body)
      val nTrm = liftTermNew(trm)
      (If(ret._1, Some(nTrm._1)), ret._2 ++ nTrm._2)
    case Let(isRec, name, rhs, body) => 
      val nRhs = if(isRec) liftTermNew(rhs)(using ctx.addV(name)) else liftTermNew(rhs)
      val nBody = liftTermNew(body)(using ctx.addV(name))
      (Let(isRec, name, nRhs._1, nBody._1), nRhs._2 ++ nBody._2)
    case Sel(receiver, fieldName) => 
      val nRec = liftTermNew(receiver)
      (Sel(nRec._1, fieldName), nRec._2)
    case Splc(fields) => ???
    case Subs(arr, idx) => 
      val (ltrm, lctx) = liftTermNew(arr)
      val (rtrm, rctx) = liftTermNew(idx)
      (Subs(ltrm, rtrm), lctx ++ rctx)
    case Test(trm, ty) => 
      val (ltrm, lctx) = liftTermNew(trm)
      val (rtrm, rctx) = liftTermAsType(ty)
      (Test(ltrm, rtrm), lctx ++ rctx)
    case TyApp(lhs, targs) => 
      val ret = liftTermNew(lhs)
      val nTs = targs.map(liftType).unzip
      (TyApp(ret._1, nTs._1), nTs._2.fold(ret._2)(_ ++ _))
    case With(trm, fields) => ???
    case New(Some((t: TypeName, prm: Tup)), TypingUnit(Nil)) => 
      val ret = liftConstr(t, prm)
      (New(Some((ret._1, ret._2)), TypingUnit(Nil)), ret._3)
    case New(Some((t: TypeName, prm: Tup)), tu) =>
      log(s"new $t in ctx $ctx, $cache, $outer")
      val nTpNm = TypeName(genAnoName(t.name))
      val cls = cache.get(t).get
      val supArgs = Tup(cls.body.params.fields.flatMap(tupleEntityToVar).map(toFldsEle))
      val anoCls = NuTypeDef(Cls, nTpNm, Nil, cls.body.params, List(App(Var(t.name), supArgs)), tu)
      val nSta = New(Some((nTpNm, prm)), TypingUnit(Nil))
      val ret = liftEntitiesNew(List(anoCls, nSta))
      (Blk(ret._1), ret._2)
    case New(None, tu) =>
      val nTpNm = TypeName(genAnoName())
      val anoCls = NuTypeDef(Cls, nTpNm, Nil, Tup(Nil), Nil, tu)
      val nSta = New(Some((nTpNm, Tup(Nil))), TypingUnit(Nil))
      val ret = liftEntitiesNew(List(anoCls, nSta))
      (Blk(ret._1), ret._2)
    case New(head, body) => ???
    case Blk(stmts) => 
      val ret = liftEntitiesNew(stmts)
      (Blk(ret._1), ret._2)
    case lit: Lit => (lit, emptyCtx)
  }

  //serves for lifting Tup(Some(_), Fld(_, _, trm)), where trm refers to a type
  private def liftTermAsType(target: Term)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (Term, LocalContext) = 
    log(s"liftTermAsType $target in $ctx, $cache")
    target match{
    case v: Var => 
      if (!ctx.contains(v) && !primiTypes.contains(v.name))
        cache.get(TypeName(v.name)).map(x => Var(x.liftedNm.name) -> emptyCtx).getOrElse(v -> asContext(TypeName(v.name)))
      else (v -> emptyCtx)
    case Lam(lhs, rhs) => 
      val lret = liftTermAsType(lhs)
      val rret = liftTermAsType(rhs)
      Lam(lret._1, rret._1) -> (lret._2 ++ rret._2)
    case TyApp(lhs, targs) => 
      val lret = liftTermAsType(lhs)
      val tRets = targs.map(liftType).unzip
      TyApp(lret._1, tRets._1) -> (tRets._2.fold(lret._2)(_ ++ _))
    case Tup(fields) => 
      val ret = fields.map{
        case (oV, Fld(b1, b2, trm)) => 
          val tmp = liftTermAsType(trm)
          (oV, Fld(b1, b2, tmp._1)) -> tmp._2
      }.unzip
      Tup(ret._1) -> ret._2.fold(emptyCtx)(_ ++ _)
    case Bra(rcd, trm) => 
      val ret = liftTermAsType(trm)
      Bra(rcd, ret._1) -> ret._2
    case Rcd(fields) => 
      val ret = fields.map{
        case (v, Fld(b1, b2, trm)) => 
          val tmp = liftTermAsType(trm)
          ((v, Fld(b1, b2, tmp._1)), tmp._2)
      }.unzip
      (Rcd(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
    case _ => ???
  }

  private def liftTypeName(target: TypeName)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (TypeName, LocalContext) = {
    if(ctx.contains(target) || primiTypes.contains(target.name)) { target -> emptyCtx }
    else {
      cache.get(target).map(x => (x.liftedNm -> emptyCtx)).getOrElse(target -> asContext(target)) 
    }
  }

  private def liftTypeField(target: Field)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (Field, LocalContext) = {
    val (inT, iCtx) = target.in.map(liftType).unzip
    val (outT, oCtx) = liftType(target.out)
    Field(inT, outT) -> (iCtx.getOrElse(emptyCtx) ++ oCtx)
  }

  private def liftType(target: Type)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (Type, LocalContext) = target match{
    case AppliedType(base, targs) => 
      val (nTargs, nCtx) = targs.map(liftType).unzip
      val (nBase, bCtx) = liftTypeName(base)
      AppliedType(nBase, nTargs) -> (nCtx.fold(emptyCtx)(_ ++ _) ++ bCtx)
    case Bounds(lb, ub) =>
      val nlhs = liftType(lb)
      val nrhs = liftType(ub)
      Bounds(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
    case Constrained(base, where) =>
      val (nTargs, nCtx) = where.map(x => {
        val tmp = liftType(x._2)
        (x._1, tmp._1.asInstanceOf[Bounds]) -> tmp._2
      }).unzip
      val (nBase, bCtx) = liftType(base)
      Constrained(nBase, nTargs) -> (nCtx.fold(emptyCtx)(_ ++ _) ++ bCtx)
    case Function(lhs, rhs) =>
      val nlhs = liftType(lhs)
      val nrhs = liftType(rhs)
      Function(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
    case Neg(base) =>
      val ret = liftType(base)
      Neg(ret._1) -> ret._2
    case Record(fields) =>
      val ret = fields.map(x => 
        val (nX, nXCtx) = liftTypeName(TypeName(x._1.name))
        val (nFld, nFldCtx) = liftTypeField(x._2)
        (Var(nX.name) -> nFld) -> (nXCtx ++ nFldCtx)
      ).unzip
      Record(ret._1) -> ret._2.fold(emptyCtx)(_ ++ _)
    case Recursive(uv, body) =>
      val ret = liftType(body)
      Recursive(uv, ret._1) -> ret._2
    case Rem(base, names) =>
      val ret = liftType(base)
      Rem(ret._1, names) -> ret._2
    case Splice(fields) =>
      val ret = fields.map{
          case Left(tp) => 
            val tmp = liftType(tp)
            Left(tmp._1) -> tmp._2
          case Right(fld) =>
            val tmp = liftTypeField(fld)
            Right(tmp._1) -> tmp._2
      }.unzip
      Splice(ret._1) -> ret._2.fold(emptyCtx)(_ ++ _)
    case Tuple(fields) =>
      val ret = fields.map(x => 
        val (nFld, nFldCtx) = liftTypeField(x._2)
        (x._1 -> nFld) -> nFldCtx
      ).unzip
      Tuple(ret._1) -> ret._2.fold(emptyCtx)(_ ++ _)
    case WithExtension(base, rcd) =>
      val nBase = liftType(base)
      val nRcd = liftType(rcd)
      WithExtension(nBase._1, nRcd._1.asInstanceOf[Record]) -> (nBase._2 ++ nRcd._2)
    case Inter(lhs, rhs) =>
      val nlhs = liftType(lhs)
      val nrhs = liftType(rhs)
      Inter(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
    case Union(lhs, rhs) =>
      val nlhs = liftType(lhs)
      val nrhs = liftType(rhs)
      Union(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
    case x : TypeName =>
      liftTypeName(x)
    // Bot, Literal, Top, TypeTag, TypeVar
    case others => others -> emptyCtx
  }
  

  private def liftFunc(func: NuFunDef)(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (NuFunDef, LocalContext) = {
    log(s"liftFunc $func under $ctx # $cache # $outer")
    val NuFunDef(rec, nm, tpVs, body) = func
    body match{
      case Left(value) => 
        val ret = liftTermNew(value)(using ctx.addV(nm).addT(tpVs))
        (func.copy(rhs = Left(ret._1)), ret._2)
      case Right(PolyType(targs, body)) => 
        val nBody = liftType(body)(using ctx.addT(tpVs))
        val nTargs = targs.map(liftTypeName(_)(using ctx.addT(tpVs))).unzip
        (func.copy(rhs = Right(PolyType(nTargs._1, nBody._1))), nTargs._2.fold(nBody._2)(_ ++ _))
    }
  }
  

  private def grepFieldsInTrm(trm: Term): Option[Var] = trm match{
    case Let(isRec, name, rhs, body) => Some(name)
    case _ => None
  }

  private def mixClsInfos(clsInfos: Map[TypeName, ClassInfoCache], newClsNms: Set[Var])(using cache: ClassCache): Map[TypeName, ClassInfoCache] = {
    val nameInfoMap: MMap[TypeName, ClassInfoCache] = MMap(clsInfos.toSeq: _*)
    log(s"mix cls infos $nameInfoMap")
    // val fullMp = cache ++ nameInfoMap
    val clsNmsAsTypeNm = newClsNms.map(x => TypeName(x.name))
    val len = clsInfos.size
    for(_ <- 1 to len){
      val tmp = nameInfoMap.toList
      tmp.foreach{case (nmOfCls, infoOfCls@ClassInfoCache(_, _, ctx, flds, inners, sups, _, _, _)) => {
        val usedClsNmList = ctx.vSet.map(x => TypeName(x.name)).intersect(clsNmsAsTypeNm)
        val newCtxForCls = usedClsNmList.foldLeft(ctx)((c1, c2) => c1 ++ nameInfoMap.get(c2).get.capturedParams)
        val supClsNmList = infoOfCls.supClses
        val newFields = supClsNmList.foreach(c2 => flds.addAll(
          nameInfoMap.get(c2).map(_.fields).getOrElse(cache.get(c2).map(_.fields).getOrElse(Nil))
          ))
        val newInners = supClsNmList.foreach(c2 => inners.addAll(
          nameInfoMap.get(c2).map(_.innerClses).getOrElse(cache.get(c2).map(_.innerClses).getOrElse(Nil))
          ))
        val newCtxFromSup = supClsNmList.map(c2 => 
          nameInfoMap.get(c2).map(_.capturedParams).getOrElse(cache.get(c2).map(_.capturedParams).getOrElse(emptyCtx))
          ).fold(emptyCtx)(_ ++ _)
        infoOfCls.capturedParams = newCtxForCls ++ newCtxFromSup
      }}
    }
    nameInfoMap.foreach((x1, x2) => x2.capturedParams = (x2.capturedParams extV newClsNms).extT(x2.innerClses.keySet))
    nameInfoMap.toMap
  }

  private def liftEntitiesNew(etts: List[Statement])(using ctx: LocalContext, cache: ClassCache, outer: Option[ClassInfoCache]): (List[Statement], LocalContext) = {
    log("liftEntities: " ++ etts.headOption.map(_.toString()).getOrElse(""))
    val (newCls, newFuncs, rstTrms) = splitEntities(etts)
    val newClsNms = newCls.map(x => Var(x.nme.name)).toSet
    val newFuncNms = newFuncs.map(_.nme)
    val nmsInTrm = rstTrms.flatMap(grepFieldsInTrm)
    val clsInfos = newCls.map(x => {
      val infos = collectClassInfo(x, newCls.map(_.nme).toSet)(using emptyCtx)
      infos.capturedParams = infos.capturedParams.copy(vSet = infos.capturedParams.vSet.intersect(ctx.vSet ++ newClsNms ++ newFuncNms ++ nmsInTrm))
      x.nme -> infos}).toMap
    log("captured cls infos: \n" ++ clsInfos.toString())
    val refinedInfo = mixClsInfos(clsInfos, newClsNms)
    val newCache = cache ++ refinedInfo
    refinedInfo.foreach((_, clsi) => completeClsInfo(clsi)(using newCache))

    newCls.foreach(x => liftTypeDefNew(x)(using newCache))
    val (liftedFuns, funVs) = newFuncs.map(liftFunc(_)(using ctx.addV(newFuncNms), newCache)).unzip
    val (liftedTerms, termVs) = rstTrms.map(liftTermNew(_)(using ctx.addV(newFuncNms), newCache)).unzip
    (liftedFuns ++ liftedTerms, (funVs ++ termVs).fold(emptyCtx)(_ ++ _))
  }

  private def completeClsInfo(clsInfo: ClassInfoCache)(using cache: ClassCache): Unit = {
    val ClassInfoCache(_, nName, freeVs, flds, inners, _, _, cls, _) = clsInfo
    val (clsList, _, _) = splitEntities(cls.body.entities)
    val innerClsNmSet = clsList.map(_.nme).toSet
    val innerClsInfos = clsList.map(x => x.nme -> collectClassInfo(x, innerClsNmSet)(using asContextV(freeVs.vSet ++ flds), cache, Some(clsInfo))).toMap
    val refinedInfos = mixClsInfos(innerClsInfos, innerClsNmSet.map(x => Var(x.name)))
    refinedInfos.foreach((_, info) => completeClsInfo(info)(using cache ++ refinedInfos))
    inners.addAll(refinedInfos)
  }

  private def liftTypeDefNew(target: NuTypeDef)(using cache: ClassCache, outer: Option[ClassInfoCache]): Unit = {
    def getAllInners(sups: Set[TypeName]): ClassCache = {
      sups.flatMap(
        t => cache.get(t).map(x => getAllInners(x.supClses) ++ x.innerClses)
      ).flatten.toMap
    }
    log("lift type " + target.toString() + " with cache " + cache.toString())
    val NuTypeDef(kind, nme, tps, params, pars, body) = target
    val nOuter = cache.get(nme)
    val ClassInfoCache(_, nName, freeVs, flds, inners, sups, _, _, _) = nOuter.get
    val (clsList, funcList, termList) = splitEntities(body.entities)
    val innerNmsSet = clsList.map(_.nme).toSet

    val nCache = cache ++ inners ++ getAllInners(sups)
    val nTps = (tps ++ (freeVs.tSet -- nCache.keySet).toList).distinct
    val nCtx = freeVs.addT(nTps)
    val nParams = 
      outer.map(x => List(toFldsEle(Var(genParName(x.liftedNm.name))))).getOrElse(Nil)
      ++ params.fields
      ++ freeVs.vSet.map(toFldsEle) 
    val nPars = pars.map(liftTermNew(_)(using emptyCtx, nCache, nOuter)).unzip
    val nFuncs = funcList.map(liftFunc(_)(using emptyCtx, nCache, nOuter)).unzip
    val nTerms = termList.map(liftTermNew(_)(using emptyCtx, nCache, nOuter)).unzip
    clsList.foreach(x => liftTypeDefNew(x)(using nCache, nOuter))
    retSeq = retSeq.appended(NuTypeDef(kind, nName, nTps, Tup(nParams), nPars._1, TypingUnit(nFuncs._1 ++ nTerms._1)))
  }

  def liftTypingUnit(rawUnit: TypingUnit): TypingUnit = {
    log("=========================\n")
    log(s"lifting: \n${showStructure(rawUnit)}\n")
    retSeq = Nil
    val re = liftEntitiesNew(rawUnit.entities)(using emptyCtx, Map(), None)
    log(s"freeVars: ${re._2}")
    // println(logOutput.toString())
    TypingUnit(retSeq.toList++re._1)
  }
}
