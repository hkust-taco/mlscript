package mlscript
package compiler

import mlscript.utils.*
import mlscript.utils.shorthands.*
import scala.collection.mutable.StringBuilder as StringBuilder
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer as ArrayBuffer
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.codegen.CodeGenError
import mlscript.compiler.mono.MonomorphError

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
    def intersectV(rst: Set[Var]) = LocalContext(vSet.intersect(rst), tSet)
    def contains(v: Var) = vSet.contains(v) || tSet.contains(TypeName(v.name))
    def contains(tv: TypeName) = vSet.contains(Var(tv.name)) || tSet.contains(tv)
    override def toString(): String = "(" ++ vSet.mkString(", ") ++ "; " ++ tSet.mkString(", ") ++ ")"
  }
  private def asContext(v: Var) = LocalContext(Set(v), Set())
  private def asContextV(vS: IterableOnce[Var]) = LocalContext(vS.iterator.toSet, Set())
  private def asContext(t: TypeName) = LocalContext(Set(), Set(t))
  private def asContextT(tS: IterableOnce[TypeName]) = LocalContext(Set(), tS.iterator.toSet)
  private def emptyCtx = LocalContext(Set(), Set())
  private def emptyCtxObj = LocalContext(Set(Var("this")), Set())

  case class ClassInfoCache(
    originNm: TypeName, 
    liftedNm: TypeName, 
    var capturedParams: LocalContext, 
    fields: MutSet[Var], 
    innerClses: MutMap[TypeName, ClassInfoCache], 
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
  val globalFunctions: ArrayBuffer[NuFunDef] = ArrayBuffer()
  var anonymCnt: Int = 0
  var clsCnt: Int = 0
  val logOutput: StringBuilder = new StringBuilder
  val primiTypes = new mlscript.Typer(false, false, false, true).primitiveTypes

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
    case (None, Fld(_, v: Var)) => Some(v)
    case (Some(v: Var), _) => Some(v)
    case _ => None
  }

  private def getFields(etts: List[Statement]): Set[Var] = {
    etts.flatMap{
      case NuFunDef(_, nm, _, _, _) => Some(nm)
      case nuty: NuTypeDef => Some(Var(nuty.name))
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
  private def toFldsEle(trm: Term): (Option[Var], Fld) = (None, Fld(FldFlags(false, false, false), trm))

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

  private def genClassNm(orgNm: String)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): TypeName = {
    TypeName(outer match{
      case None =>
        clsCnt = clsCnt+1
        orgNm ++ "$" ++ clsCnt.toString()
      case Some(value) => genInnerName(value.liftedNm, orgNm)
    })
  }

  private def getFreeVars(stmt: Located)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): LocalContext = stmt match{
    case v:Var => 
      val caseEmpty = ctx.vSet.contains(v) || cache.contains(TypeName(v.name)) || globFuncs.contains(v) || primiTypes.contains(v.name)
      val caseThis = buildPathToVar(v).isDefined && !ctx.vSet.contains(Var("this"))
      log(s"get free var find $v: $caseEmpty/$caseThis")
      if(caseEmpty) then emptyCtx
      else if(caseThis) asContext(Var("this"))
      else asContext(v)
    case t: NamedType => 
      log(s"get type $t under $ctx, $cache, $outer")
      asContextT(t.collectTypeNames.map(TypeName(_)).filterNot(x => ctx.contains(x) || cache.contains(x) || primiTypes.contains(x.name)))
    case Lam(lhs, rhs) =>
      val lhsVs = getFreeVars(lhs)
      getFreeVars(rhs)(using ctx ++ lhsVs) -+ lhsVs
    case NuFunDef(_, vm, _, tps, Left(trm)) =>
      getFreeVars(trm).extV(vm).extT(tps)
    case OpApp(_, trm) => getFreeVars(trm)
    case Sel(trm, _) => getFreeVars(trm)
    case Asc(trm, tp) =>
      getFreeVars(trm) ++ getFreeVars(tp)
    case Tup(tupLst) =>
      tupLst.map{
        case (Some(v), Fld(_, trm)) => getFreeVars(trm).vSet2tSet.addV(v)
        case (_, Fld(_, rhs)) => getFreeVars(rhs)
      }.fold(emptyCtx)(_ ++ _)
    case Rcd(fields) =>
      fields.map{
        case (v, Fld(_, trm)) => getFreeVars(trm).vSet2tSet
      }.fold(emptyCtx)(_ ++ _)
    case TyApp(trm, tpLst) =>
      getFreeVars(trm).addT(tpLst.flatMap(_.collectTypeNames.map(TypeName(_))))
    case NuTypeDef(_, nm, tps, param, _, _, pars, _, _, body) =>
      val prmVs = getFreeVars(param.getOrElse(Tup(Nil)))(using emptyCtx, Map(), globFuncs, None)
      val newVs = prmVs.vSet ++ getFields(body.entities) + Var(nm.name)
      val nCtx = ctx.addV(newVs).addT(nm).addT(tps.map(_._2))
      val parVs = pars.map(getFreeVars(_)(using nCtx)).fold(emptyCtx)(_ ++ _)
      val bodyVs = body.entities.map(getFreeVars(_)(using nCtx)).fold(emptyCtx)(_ ++ _)
      (bodyVs ++ parVs -+ prmVs).extT(tps.map(_._2))
    case Blk(stmts) =>
      val newVs = getFields(stmts)
      stmts.map(getFreeVars(_)(using ctx.addV(newVs))).fold(emptyCtx)(_ ++ _)
    case Let(isRec, name, rhs, body) =>
      getFreeVars(rhs)(using ctx.addV(name)) ++ getFreeVars(body)(using ctx.addV(name))
    case others =>
      others.children.map(getFreeVars).fold(emptyCtx)(_ ++ _)
  }

  private def collectClassInfo(cls: NuTypeDef, preClss: Set[TypeName])(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): ClassInfoCache = {
    val NuTypeDef(_, nm, tps, param, _, _, pars, _, _, body) = cls
    log(s"grep context of ${cls.nme.name} under $ctx # $cache # $globFuncs # $outer ")
    val (clses, funcs, trms) = splitEntities(cls.body.entities)
    val (supNms, rcdFlds) = pars.map(getSupClsInfoByTerm).unzip
    val flds = rcdFlds.flatten.map{
      case (v, Fld(_, trm)) => 
        val tmp = getFreeVars(trm)(using emptyCtxObj)
        val ret = tmp.tSet ++ tmp.vSet.map(x => TypeName(x.name))
        (v, ret)
    }.unzip
    log(s"par record: ${flds._2.flatten}")
    val fields = (param.fold(Nil)(t => t.fields).flatMap(tupleEntityToVar) ++ funcs.map(_.nme) ++ clses.map(x => Var(x.nme.name)) ++ trms.flatMap(grepFieldsInTrm) ++ flds._1).toSet
    val nCtx = ctx.addV(fields).addV(flds._1).extT(tps.map(_._2)).addV(Var("this"))
    val tmpCtx = ((body.entities.map(getFreeVars(_)(using nCtx)) ++ pars.map(getFreeVars(_)(using nCtx))).fold(emptyCtx)(_ ++ _).moveT2V(preClss)
                  ).addT(flds._2.flatten.toSet).extV(supNms.flatten.map(x => Var(x.name)))

    log(s"ret ctx for ${cls.nme.name}: $tmpCtx")
    val ret = ClassInfoCache(nm, genClassNm(nm.name), tmpCtx, MutSet(fields.toSeq: _*), MutMap(), supNms.flatten.toSet, outer, cls, outer.map(_.depth).getOrElse(0)+1)
    ret
  }

  private def liftCaseBranch(brn: CaseBranches)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (CaseBranches, LocalContext) = brn match{
    case Case(v: Var, body, rest) => 
      val nTrm = liftTerm(body)(using ctx.addV(v))
      val nRest = liftCaseBranch(rest)
      (Case(v, nTrm._1, nRest._1), nTrm._2 ++ nRest._2)
    case Case(pat, body, rest) =>
      val nTrm = liftTerm(body)
      val nRest = liftCaseBranch(rest)
      (Case(pat, nTrm._1, nRest._1), nTrm._2 ++ nRest._2)
    case Wildcard(body) =>
      val nTrm = liftTerm(body)
      (Wildcard(nTrm._1), nTrm._2)
    case NoCases => (brn, emptyCtx)
  }

  private def liftIf(body: IfBody)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (IfBody, LocalContext) = body match{
    case IfElse(expr) => 
      val ret = liftTerm(expr)
      (IfElse(ret._1), ret._2)
    case IfThen(expr, rhs) =>
      val nE = liftTerm(expr)
      val nR = liftTerm(rhs)
      (IfThen(nE._1, nR._1), nE._2 ++ nR._2)
    case _ => throw MonomorphError(s"Unknown IfBody: ${body}")
  }

  private def liftTuple(tup: Tup)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (Tup, LocalContext) = {
    val ret = tup.fields.map{
        case (None, Fld(flags, trm)) =>
          val tmp = liftTerm(trm)
          ((None, Fld(flags, tmp._1)), tmp._2)
        case (Some(v), Fld(flags, trm)) =>
          val nTrm = liftTermAsType(trm)
          ((Some(v), Fld(flags, nTrm._1)), nTrm._2)
      }.unzip
    (Tup(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
  }

  private def liftConstr(tp: TypeName, prm: Tup)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (TypeName, Tup, LocalContext) = {
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

  private def newLambObj(lhs: Term, rhs: Term) = 
    New(None, TypingUnit(List(NuFunDef(None, Var("apply"), None, Nil, Left(Lam(lhs, rhs)))(N, N, N, N, false)))) //TODO: Use Proper Arguments

  private def liftTerm(target: Term)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (Term, LocalContext) = 
    log(s"liftTermNew $target in $ctx, $cache, $globFuncs, $outer")
    target match{
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
      val prmCnt = getFreeVars(lhs)(using emptyCtx, cache, globFuncs, None).vSet.size
      val nTpNm = TypeName(genAnoName("Lambda"+prmCnt))
      val anoCls = NuTypeDef(
        Cls, nTpNm, Nil, S(Tup(Nil)), N, N, Nil, N, N, 
        TypingUnit(List(NuFunDef(None, Var("apply"), N, Nil, Left(Lam(lhs, rhs)))(N, N, N, N, false))))(N, N) //TODO: Use Proper Arguments
      val nSta = New(Some((nTpNm, Tup(Nil))), TypingUnit(Nil))
      val ret = liftEntities(List(anoCls, nSta))
      (Blk(ret._1), ret._2)
    case t: Tup => 
      liftTuple(t)
    case Rcd(fields) =>
      val ret = fields.map{
        case (v, Fld(flags, trm)) =>
          val tmp = liftTermAsType(trm)
          ((v, Fld(flags, tmp._1)), tmp._2)
      }.unzip
      (Rcd(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
    case Asc(trm, ty) =>
      val ret = liftTerm(trm)
      val nTy = liftType(ty)
      (Asc(ret._1, nTy._1), ret._2 ++ nTy._2)
    case App(v: Var, prm: Tup) if cache.contains(TypeName(v.name)) =>
      val ret = liftConstr(TypeName(v.name), prm)
      (App(Var(ret._1.name), ret._2), ret._3)
    case App(v: Var, prm: Tup) if globFuncs.contains(v) => 
      val (nFuncName, nCtxs) = globFuncs.get(v).get
      val addiArgs = nCtxs.vSet.toList.map(toFldsEle(_))
      val nPrm = liftTuple(prm)
      (App(nFuncName, Tup(nPrm._1.fields ++ addiArgs)), nPrm._2)
    case App(lhs, rhs) => 
      val (ltrm, lctx) = liftTerm(lhs)
      val (rtrm, rctx) = liftTerm(rhs)
      (App(ltrm, rtrm), lctx ++ rctx)
    case Assign(lhs, rhs) =>
      val (ltrm, lctx) = liftTerm(lhs)
      val (rtrm, rctx) = liftTerm(rhs)
      (Assign(ltrm, rtrm), lctx ++ rctx)
    case Bind(lhs, rhs) =>
      val (ltrm, lctx) = liftTerm(lhs)
      val (rtrm, rctx) = liftTermAsType(rhs)
      (Bind(ltrm, rtrm), lctx ++ rctx)
    case Bra(rcd, trm) =>
      val ret = liftTerm(trm)
      (Bra(rcd, ret._1), ret._2)
    case CaseOf(trm, cases) =>
      val nTrm = liftTerm(trm)
      val nCases = liftCaseBranch(cases)
      (CaseOf(nTrm._1, nCases._1), nTrm._2 ++ nCases._2)
    case If(body, None) =>
      val ret = liftIf(body)
      (If(ret._1, None), ret._2)
    case If(body, Some(trm)) =>
      val ret = liftIf(body)
      val nTrm = liftTerm(trm)
      (If(ret._1, Some(nTrm._1)), ret._2 ++ nTrm._2)
    case Let(isRec, name, rhs, body) =>
      val nRhs = if(isRec) liftTerm(rhs)(using ctx.addV(name)) else liftTerm(rhs)
      val nBody = liftTerm(body)(using ctx.addV(name))
      (Let(isRec, name, nRhs._1, nBody._1), nRhs._2 ++ nBody._2)
    case Sel(receiver, fieldName) =>
      val nRec = liftTerm(receiver)
      (Sel(nRec._1, fieldName), nRec._2)
    case Splc(fields) => throw MonomorphError(s"Unimplemented liftTerm: ${target}")
    case Subs(arr, idx) =>
      val (ltrm, lctx) = liftTerm(arr)
      val (rtrm, rctx) = liftTerm(idx)
      (Subs(ltrm, rtrm), lctx ++ rctx)
    case Test(trm, ty) =>
      val (ltrm, lctx) = liftTerm(trm)
      val (rtrm, rctx) = liftTermAsType(ty)
      (Test(ltrm, rtrm), lctx ++ rctx)
    case TyApp(lhs, targs) =>
      val ret = liftTerm(lhs)
      val nTs = targs.map(liftType).unzip
      (TyApp(ret._1, nTs._1), nTs._2.fold(ret._2)(_ ++ _))
    case With(trm, fields) => throw MonomorphError(s"Unimplemented liftTerm: ${target}")
    case New(Some((t: TypeName, prm: Tup)), TypingUnit(Nil)) =>
      val ret = liftConstr(t, prm)
      (New(Some((ret._1, ret._2)), TypingUnit(Nil)), ret._3)
    case New(Some((t: TypeName, prm: Tup)), tu) =>
      log(s"new $t in ctx $ctx, $cache, $outer")
      val nTpNm = TypeName(genAnoName(t.name))
      val cls = cache.get(t).get
      val supArgs = Tup(cls.body.params.fold(Nil)(t => t.fields).flatMap(tupleEntityToVar).map(toFldsEle))
      val anoCls = NuTypeDef(Cls, nTpNm, Nil, cls.body.params, None, None,
                    List(App(Var(t.name), supArgs)), None, None, tu)(None, None)
      val nSta = New(Some((nTpNm, prm)), TypingUnit(Nil))
      val ret = liftEntities(List(anoCls, nSta))
      (Blk(ret._1), ret._2)
    case New(None, tu) =>
      val nTpNm = TypeName(genAnoName())
      val anoCls = NuTypeDef(Cls, nTpNm, Nil, None, None, None, Nil, None, None, tu)(None, None)
      val nSta = New(Some((nTpNm, Tup(Nil))), TypingUnit(Nil))
      val ret = liftEntities(List(anoCls, nSta))
      (Blk(ret._1), ret._2)
    case New(head, body) => throw MonomorphError(s"Unimplemented liftTerm: ${target}")
    case Blk(stmts) =>
      val ret = liftEntities(stmts)
      (Blk(ret._1), ret._2)
    case lit: Lit => (lit, emptyCtx)
    case Inst(bod) =>
      val (trm, ctx) = liftTerm(bod)
      (Inst(trm), ctx)
    case Forall(ps, bod) =>
      val (trm, ctx) = liftTerm(bod)
      (Forall(ps, trm), ctx)
    case Where(bod, sts) =>
      val (bod2, ctx) = liftTerm(bod)
      val (sts2, ctx2) = liftEntities(sts)
      (Where(bod2, sts2), ctx2)
    case _: Eqn | _: Super | _: Quoted | _: Unquoted => throw MonomorphError(s"Unimplemented liftTerm: ${target}") // TODO
    case patmat: AdtMatchWith => lastWords(s"Cannot liftTermNew ${patmat}")
  }

  //serves for lifting Tup(Some(_), Fld(_, _, trm)), where trm refers to a type
  private def liftTermAsType(target: Term)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (Term, LocalContext) = 
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
        case (oV, Fld(flags, trm)) =>
          val tmp = liftTermAsType(trm)
          (oV, Fld(flags, tmp._1)) -> tmp._2
      }.unzip
      Tup(ret._1) -> ret._2.fold(emptyCtx)(_ ++ _)
    case Bra(rcd, trm) =>
      val ret = liftTermAsType(trm)
      Bra(rcd, ret._1) -> ret._2
    case Rcd(fields) =>
      val ret = fields.map{
        case (v, Fld(flags, trm)) =>
          val tmp = liftTermAsType(trm)
          ((v, Fld(flags, tmp._1)), tmp._2)
      }.unzip
      (Rcd(ret._1), ret._2.fold(emptyCtx)(_ ++ _))
    case _ => throw MonomorphError(s"Unimplemented liftTermAsType: ${target}")
  }

  private def liftTypeName(target: TypeName)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (TypeName, LocalContext) = {
    if(ctx.contains(target) || primiTypes.contains(target.name)) { target -> emptyCtx }
    else {
      cache.get(target).map(x => (x.liftedNm -> emptyCtx)).getOrElse(target -> asContext(target)) 
    }
  }

  private def liftTypeField(target: Field)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (Field, LocalContext) = {
    val (inT, iCtx) = target.in.map(liftType).unzip
    val (outT, oCtx) = liftType(target.out)
    Field(inT, outT) -> (iCtx.getOrElse(emptyCtx) ++ oCtx)
  }

  private def liftType(target: Type)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (Type, LocalContext) = target match{
    case AppliedType(base, targs) => 
      val (nTargs, nCtx) = targs.map(liftType).unzip
      val (nBase, bCtx) = liftTypeName(base)
      AppliedType(nBase, nTargs) -> (nCtx.fold(emptyCtx)(_ ++ _) ++ bCtx)
    case Bounds(lb, ub) =>
      val nlhs = liftType(lb)
      val nrhs = liftType(ub)
      Bounds(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
    case Constrained(base: Type, bounds, where) =>
      val (nTargs, nCtx) = bounds.map { case (tv, Bounds(lb, ub)) =>
        val nlhs = liftType(lb)
        val nrhs = liftType(ub)
        (tv, Bounds(nlhs._1, nrhs._1)) -> (nlhs._2 ++ nrhs._2)
      }.unzip
      val (bounds2, nCtx2) = where.map { case Bounds(lb, ub) =>
        val nlhs = liftType(lb)
        val nrhs = liftType(ub)
        Bounds(nlhs._1, nrhs._1) -> (nlhs._2 ++ nrhs._2)
      }.unzip
      val (nBase, bCtx) = liftType(base)
      Constrained(nBase, nTargs, bounds2) ->
        ((nCtx ++ nCtx2).fold(emptyCtx)(_ ++ _) ++ bCtx)
    case Constrained(_, _, _) => die
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
    case PolyType(targs, body) =>
      val (body2, ctx) = liftType(body)
      PolyType(targs, body2) -> ctx
    case Top | Bot | _: Literal | _: TypeTag | _: TypeVar => target.asInstanceOf[Type] -> emptyCtx
    case _: Selection => throw MonomorphError(s"Unimplemented liftType: ${target}") // TODO
  }
  

  private def liftMemberFunc(func: NuFunDef)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (NuFunDef, LocalContext) = {
    log(s"liftMemberFunc $func under $ctx # $cache # $globFuncs # $outer")
    val NuFunDef(rec, nm, sn, tpVs, body) = func
    body match{
      case Left(Lam(lhs@Tup(etts), rhs)) =>
        val lctx = getFreeVars(lhs)(using emptyCtx, cache, globFuncs, None)
        val lret = liftTuple(lhs)(using ctx.addV(lctx.vSet))
        val ret = liftTerm(rhs)(using ctx.addV(lctx.vSet).addT(tpVs))
        (func.copy(rhs = Left(Lam(lret._1, ret._1)))(func.declareLoc, func.virtualLoc, func.signature, func.outer, func.genField), ret._2 -+ lret._2) //TODO: Check correctness
      case Left(value) => 
        // will be treated as Lam(Tup(Nil), rhs)
        val ret = liftTerm(value)(using ctx.addT(tpVs))
        (func.copy(rhs = Left(Lam(Tup(Nil), ret._1)))(func.declareLoc, func.virtualLoc, func.signature, func.outer, func.genField), ret._2) //TODO: Check correctness
      case Right(PolyType(targs, body)) => 
        val nBody = liftType(body)(using ctx.addT(tpVs))
        val nTargs = targs.map {
          case L(tp) => liftTypeName(tp)(using ctx.addT(tpVs)).mapFirst(Left.apply)
          case R(tv) => R(tv) -> emptyCtx
        }.unzip
        (func.copy(rhs = Right(PolyType(nTargs._1, nBody._1)))(func.declareLoc, func.virtualLoc, func.signature, func.outer, func.genField),
          nTargs._2.fold(nBody._2)(_ ++ _))
      case _ => throw MonomorphError(s"Unimplemented liftMemberFunc: ${func}") // TODO
    }
  }

  private def liftGlobalFunc(func: NuFunDef)(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): Unit = {
    log(s"liftGlobalFunc $func under $ctx # $cache # $globFuncs # $outer")
    val NuFunDef(rec, nm, _, tpVs, body) = func
    val nTpVs = tpVs ++ globFuncs.get(nm).get._2.tSet.toList
    globalFunctions.addOne(body match{
      case Left(Lam(lhs@Tup(etts), rhs)) =>
        val tmp = globFuncs.get(nm).get._2.vSet.toList.map(toFldsEle)
        val lctx = getFreeVars(lhs)(using emptyCtx, cache, globFuncs, None)
        val lret = liftTuple(lhs)(using ctx.addV(lctx.vSet) ++ globFuncs.get(nm).get._2, cache, globFuncs)
        val ret = liftTerm(rhs)(using ctx.addV(lctx.vSet) ++ globFuncs.get(nm).get._2, cache, globFuncs)
        NuFunDef(rec, globFuncs.get(nm).get._1, N, nTpVs, Left(Lam(Tup(lret._1.fields ++ tmp), ret._1)))(N, N, N, N, true) //TODO: Use proper arguments
      case Left(rhs) => 
        // will be treated as Lam(Tup(Nil), rhs)
        val tmp = globFuncs.get(nm).get._2.vSet.toList.map(toFldsEle)
        val ret = liftTerm(rhs)(using ctx ++ globFuncs.get(nm).get._2, cache, globFuncs)
        NuFunDef(rec, globFuncs.get(nm).get._1, N, nTpVs, Left(Lam(Tup(tmp), ret._1)))(N, N, N, N, true) //TODO: Use proper arguments
        // val ret = liftTermNew(value)(using ctx.addV(nm) ++ globFuncs.get(nm).get._2, cache, globFuncs)
        // NuFunDef(rec, globFuncs.get(nm).get._1, nTpVs, Left(ret._1))
      case Right(PolyType(targs, body)) => 
        val nBody = liftType(body)(using ctx ++ globFuncs.get(nm).get._2, cache, globFuncs, None)
        val nTargs = targs.map({
          case L(tn) => 
            liftTypeName(tn)(using ctx.addT(nTpVs), cache, globFuncs, None) match
              case (tn, ctx) => (L(tn), ctx)
          case R(tv) => R(tv) -> emptyCtx}).unzip
        NuFunDef(rec, globFuncs.get(nm).get._1, N, nTpVs, Right(PolyType(nTargs._1, nBody._1)))(N, N, N, N, true) //TODO: Use proper arguments
      case _ => throw MonomorphError(s"Unimplemented liftGlobalFunc: ${func}")
    })
  }
  

  private def grepFieldsInTrm(trm: Term): Option[Var] = trm match{
    case Let(isRec, name, rhs, body) => Some(name)
    case _ => None
  }

  private def mixClsInfos(clsInfos: Map[String, ClassInfoCache], funcInfos: Map[String, LocalContext])(using cache: ClassCache): (Map[String, ClassInfoCache], Map[String, LocalContext]) = {
    val nameInfoMap: MutMap[String, ClassInfoCache] = MutMap(clsInfos.toSeq: _*)
    val nameFuncMap: MutMap[String, LocalContext] = MutMap(funcInfos.toSeq: _*)
    log(s"mix cls infos $nameInfoMap, $nameFuncMap")
    // val fullMp = cache ++ nameInfoMap
    val clsNmsAsTypeNm = clsInfos.keySet.map(x => TypeName(x))
    val len = clsInfos.size + nameFuncMap.size
    for(_ <- 0 to len){
      nameInfoMap.toList.foreach{case (nmOfCls, infoOfCls@ClassInfoCache(_, _, ctx, flds, inners, sups, _, _, _)) => {
        val usedClsNmList = ctx.vSet.map(_.name).intersect(clsInfos.keySet)
        val newCtxForCls_tmp = usedClsNmList.foldLeft(ctx)((c1, c2) => c1 ++ nameInfoMap.get(c2).get.capturedParams)

        val usedFuncNmList = ctx.vSet.map(_.name).intersect(funcInfos.keySet)
        val newCtxForCls = usedFuncNmList.foldLeft(newCtxForCls_tmp)((c, x) => c ++ nameFuncMap.get(x).get)

        val supClsNmList = infoOfCls.supClses
        supClsNmList.foreach(c2 => flds.addAll(
          nameInfoMap.get(c2.name).map(_.fields).getOrElse(cache.get(c2).map(_.fields).getOrElse(Nil))
          ))
        supClsNmList.foreach(c2 => inners.addAll(
          nameInfoMap.get(c2.name).map(_.innerClses).getOrElse(cache.get(c2).map(_.innerClses).getOrElse(Nil))
          ))
        val newCtxFromSup = supClsNmList.map(c2 => 
          nameInfoMap.get(c2.name).map(_.capturedParams).getOrElse(cache.get(c2).map(_.capturedParams).getOrElse(emptyCtx))
          ).fold(emptyCtx)(_ ++ _)
        infoOfCls.capturedParams = newCtxForCls ++ newCtxFromSup
      }}
      nameFuncMap.toList.foreach((nm, ctx) => {
        val usedClsNmList = ctx.vSet.map(_.name).intersect(clsInfos.keySet)
        val usedFuncNmList = ctx.vSet.map(_.name).intersect(funcInfos.keySet)
        val nCtx = (usedClsNmList.map(x => nameInfoMap.get(x).get.capturedParams) ++ usedFuncNmList.map(x => nameFuncMap.get(x).get)).foldLeft(ctx)(_ ++ _)
        nameFuncMap.update(nm, nCtx)
      })
    }
    nameInfoMap.foreach((x1, x2) => x2.capturedParams = (x2.capturedParams.extV(clsInfos.keySet.map(Var(_)))).extV(funcInfos.keySet.map(Var(_))).extT(x2.innerClses.keySet))
    nameFuncMap.toList.foreach((x, c) => nameFuncMap.update(x, c.extV(clsInfos.keySet.map(Var(_))).extV(funcInfos.keySet.map(Var(_)))))
    log(s"mix result: $nameInfoMap, $nameFuncMap")
    nameInfoMap.toMap -> nameFuncMap.toMap
  }
  

  private def liftEntities(etts: List[Statement])(using ctx: LocalContext, cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): (List[Statement], LocalContext) = {
    log("liftEntities: " ++ etts.headOption.map(_.toString()).getOrElse(""))
    val (newCls, newFuncs, rstTrms) = splitEntities(etts)
    val newClsNms = newCls.map(x => Var(x.nme.name)).toSet
    val newFuncNms = newFuncs.map(_.nme)
    val nmsInTrm = rstTrms.flatMap(grepFieldsInTrm)
    val clsInfos = newCls.map(x => {
      val infos = collectClassInfo(x, newCls.map(_.nme).toSet)(using emptyCtx)
      infos.capturedParams = infos.capturedParams.intersect(ctx.addT(infos.capturedParams.tSet).addV(newClsNms ++ newFuncNms ++ nmsInTrm -- globFuncs.keySet ++ outer.map(_ => Var("this"))))
      x.nme.name -> infos}).toMap
    val funcInfos = 
      newFuncs.map(x => x.nme.name -> (x.rhs match {
        case Left(trm) => getFreeVars(trm)(using emptyCtx)
                            .intersect(ctx.addV(newClsNms ++ newFuncNms ++ nmsInTrm -- globFuncs.keySet ++ outer.map(_ => Var("this"))))
                            .extT(x.tparams) 
        case _ => emptyCtx})
      ).toMap
    log("captured cls infos: \n" ++ clsInfos.toString())
    log("captured func infos: \n" ++ funcInfos.toString())
    val (refinedClsInfo, refinedFuncInfo) = mixClsInfos(clsInfos, funcInfos)
    val newCache = cache ++ refinedClsInfo.map(x => (TypeName(x._1) -> x._2))
    refinedClsInfo.foreach((_, clsi) => completeClsInfo(clsi)(using newCache))
    val newGlobalFuncs = refinedFuncInfo.map((nm, vs) => (Var(nm) -> (Var(genAnoName(nm)), vs)))

    newCls.foreach(x => liftTypeDef(x)(using newCache, globFuncs ++ newGlobalFuncs))
    (newFuncs zip refinedFuncInfo).foreach((f, c) => liftGlobalFunc(f)(using ctx, newCache, globFuncs ++ newGlobalFuncs))
    val (liftedTerms, termVs) = rstTrms.map(liftTerm(_)(using ctx.addV(newFuncNms), newCache, globFuncs ++ newGlobalFuncs)).unzip
    (liftedTerms, (termVs).fold(emptyCtx)(_ ++ _))
  }

  private def completeClsInfo(clsInfo: ClassInfoCache)(using cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)]): Unit = {
    val ClassInfoCache(_, nName, freeVs, flds, inners, _, _, cls, _) = clsInfo
    val (clsList, _, _) = splitEntities(cls.body.entities)
    val innerClsNmSet = clsList.map(_.nme).toSet
    val innerClsInfos = clsList.map(x => x.nme.name -> collectClassInfo(x, innerClsNmSet)(using asContextV(freeVs.vSet ++ flds), cache, globFuncs, Some(clsInfo))).toMap
    val refinedInfos = mixClsInfos(innerClsInfos, Map())._1.map(x => (TypeName(x._1) -> x._2))
    refinedInfos.foreach((_, info) => completeClsInfo(info)(using cache ++ refinedInfos))
    inners.addAll(refinedInfos)
  }

  private def liftTypeDef(target: NuTypeDef)(using cache: ClassCache, globFuncs: Map[Var, (Var, LocalContext)], outer: Option[ClassInfoCache]): Unit = {
    def getAllInners(sups: Set[TypeName]): ClassCache = {
      sups.flatMap(
        t => cache.get(t).map(x => getAllInners(x.supClses) ++ x.innerClses)
      ).flatten.toMap
    }
    log("lift type " + target.toString() + " with cache " + cache.toString())
    val NuTypeDef(kind, nme, tps, params, _, sig, pars, supAnn, thisAnn, body) = target
    val nOuter = cache.get(nme)
    val ClassInfoCache(_, nName, freeVs, flds, inners, sups, _, _, _) = nOuter.get
    val (clsList, funcList, termList) = splitEntities(body.entities)
    val innerNmsSet = clsList.map(_.nme).toSet

    val nCache = cache ++ inners ++ getAllInners(sups)
    val nTps = (tps.map(_._2) ++ (freeVs.tSet -- nCache.keySet).toList).distinct
    val nCtx = freeVs.addT(nTps)
    val nParams = 
      outer.map(x => List(toFldsEle(Var(genParName(x.liftedNm.name))))).getOrElse(Nil)
      ++ params.fold(Nil)(t => t.fields)
      ++ freeVs.vSet.map(toFldsEle) 
    val nPars = pars.map(liftTerm(_)(using emptyCtx, nCache, globFuncs, nOuter)).unzip
    val nFuncs = funcList.map(liftMemberFunc(_)(using emptyCtx, nCache, globFuncs, nOuter)).unzip
    val nTerms = termList.map(liftTerm(_)(using emptyCtx, nCache, globFuncs, nOuter)).unzip
    clsList.foreach(x => liftTypeDef(x)(using nCache, globFuncs, nOuter))
    retSeq = retSeq.appended(NuTypeDef(
      kind, nName, nTps.map((None, _)), S(Tup(nParams)), None, None, nPars._1,
      None, None, TypingUnit(nFuncs._1 ++ nTerms._1))(None, None))
  }

  def liftTypingUnit(rawUnit: TypingUnit): TypingUnit = {
    log("=========================\n")
    log(s"lifting: \n${showStructure(rawUnit)}\n")
    retSeq = Nil
    globalFunctions.clear()
    val re = liftEntities(rawUnit.entities)(using emptyCtx, Map(), Map(), None)
    log(s"freeVars: ${re._2}")
    // println(logOutput.toString())
    TypingUnit(retSeq.toList ++ globalFunctions.toList ++ re._1)
  }
}
