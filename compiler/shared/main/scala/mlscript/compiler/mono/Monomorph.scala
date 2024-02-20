package mlscript.compiler.mono

import mlscript.compiler.debug.{Debug, DummyDebug}
import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.{AppliedType, TypeName}
import mlscript.{App, Asc, Assign, Bind, Blk, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, FldFlags, If}
import mlscript.{IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock, Statement}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import scala.collection.immutable.{HashMap, ListMap}
import scala.collection.mutable.{Map as MutMap, Set as MutSet}
import scala.collection.mutable.ListBuffer
import mlscript.Cls
import mlscript.CaseBranches
import mlscript.TypeDefKind
import mlscript.AppliedType.apply
import mlscript.compiler.*
import mlscript.compiler.mono.specializer.{MonoVal, TypeVal, ObjVal, FuncVal, LiteralVal, PrimVal, VarVal, TupVal, UnknownVal, BoundedTerm}
import java.util.IdentityHashMap
import scala.collection.JavaConverters._

class Monomorph(debug: Debug = DummyDebug):
  import Helpers._
  import Monomorph._

  /**
   * Specialized implementations of function declarations.
   * function name -> (function, mutable parameters (?), parameters, output value)
   */
  private val nuFunImpls = MutMap[String, (NuFunDef, MutMap[String, NuFunDef], Option[List[BoundedTerm]], VarVal)]()

  private val nuFunDependence = MutMap[String, Set[String]]()

  val nuEvalQueue = MutSet[String]()
  val nuEvalCnt = MutMap[String, Int]()
  
  //private val nuTyImpls = MutMap[TypeName, SpecializationMap[NuTypeDef]]()
  private val nuAllTypeImpls = MutMap[String, NuTypeDef]()

  private def nuAddType(typeDef: NuTypeDef) =
    //nuTyImpls.addOne(typeDef.nme, SpecializationMap(typeDef))
    nuAllTypeImpls.addOne(typeDef.name, typeDef)
  
  val specializer = new mono.specializer.Specializer(this)(using debug)


  object VarValMap {
    var vxCnt: Int = 0
    val vMap: MutMap[Int, BoundedTerm] = MutMap[Int, BoundedTerm]()
    def get(v: VarVal): BoundedTerm = vMap.get(v.vx) match 
      case Some(value) => value
      case None => ???
    def refresh(): VarVal = {
      vxCnt += 1
      val ret = VarVal(vxCnt, 0, get)
      vMap.addOne(vxCnt -> BoundedTerm(ret))
      ret
    }
    def update(v: VarVal, s: BoundedTerm): Unit = {
      debug.writeLine(s"Updating vMap ${v.vx} with ${s}")
      vMap.update(v.vx, s)
    }
  }

  val evaluationMap = new IdentityHashMap[Term, BoundedTerm]().asScala
  def getRes(term: Term): BoundedTerm = evaluationMap.getOrElse(term, throw MonomorphError(s"Bounds for ${term} not found."))

  private def nuAddFunction(func: NuFunDef): Unit = {
    debug.writeLine(s"Adding Function ${func}")
    nuFunImpls.addOne(func.name, (func, MutMap(), func.body match
      case Lam(Tup(params), body) => Some(params.map(_ => BoundedTerm()))
      case _ => None
    , VarValMap.refresh()))
    nuFunDependence.addOne(func.name, Set())
  }

  private def nuGetResult(mains: List[Statement]): List[Statement] = 
    List[Statement]()
    .concat(nuAllTypeImpls.values.map(_.copy(body = TypingUnit(Nil))(None, None)))
    .concat(nuFunImpls.values.map(_._1))
    .concat(mains)
  
  def nuDefunctionalize(tu: TypingUnit): TypingUnit =
    val nuTerms = tu.entities.zipWithIndex.flatMap {
      case (term: Term, i) =>
        val mainFunc = NuFunDef(None, Var(s"main$$$$$i"), None, Nil, Left(Lam(Tup(Nil), term)))(None, None, None, None, false)
        nuAddFunction(mainFunc)
        nuEvalQueue.add(mainFunc.name)
        Some(App(Var(s"main$$$$$i"), Tup(Nil)))
      case (tyDef: NuTypeDef, _) =>
        nuAddType(tyDef)
        None
      case (funDef: NuFunDef, _) =>
        funDef.rhs match
          case Left(value) => nuAddFunction(funDef)
          case Right(value) => ??? 
        None
      case _ => ???
    }
    while (!nuEvalQueue.isEmpty) {
      debug.writeLine(s"Queue: ${nuEvalQueue}")
      val next = nuEvalQueue.head
      nuEvalQueue.remove(next)
      nuUpdateFunction(next)
    }
    debug.writeLine(s"${PrettyPrinter.showTypingUnit(TypingUnit(nuGetResult(nuTerms)))}")
    debug.writeLine(s"========DEFUNC PHASE========")
    nuFunImpls.mapValuesInPlace{
      case (_, (func@NuFunDef(isLetRec, nm, sn, tp, rhs), mp, la, lr)) =>
        rhs match 
          case Left(Lam(lhs, rhs)) =>
            (NuFunDef(isLetRec, nm, sn, tp, Left(Lam(lhs,specializer.nuDefunctionalize(rhs)(using evaluationMap))))(None, None, None, None, false), mp, la, lr)
          case Left(body) => 
            (NuFunDef(isLetRec, nm, sn, tp, Left(specializer.nuDefunctionalize(body)(using evaluationMap)))(None, None, None, None, false), mp, la, lr)
          case Right(tp) => ???
    }
    val ret = nuGetResult(nuTerms)
    TypingUnit(ret)

  private def nuUpdateFunction(funcName: String): Unit = {
    val updateCount = nuEvalCnt.get(funcName).getOrElse(0)
    if(updateCount <= 10){
      debug.writeLine(s"updating ${funcName} for ${updateCount}th time")
      nuEvalCnt.update(funcName, updateCount+1)
      nuUpdateFunc(funcName)
    }
    else{
      throw new MonomorphError("stack overflow!!!")
    }
  }
  def nuGetFuncRetVal(name: String, args: Option[List[BoundedTerm]])(using evalCtx: Map[String, BoundedTerm], callingStack: List[String]): BoundedTerm = {
    nuFunImpls.get(name) match
      case None => throw MonomorphError(s"Function ${name} does not exist")
      case Some((funDef, mp, oldArgs, vals)) => 
        funDef.rhs match
          case Left(body) => 
            nuFunDependence.update(name, nuFunDependence.getOrElse(name, Set()) ++ callingStack.headOption)
            val hasArgs = oldArgs.isDefined
            val params = extractLamParams(body)
            val mergedArgs = oldArgs.map(old => (old zip (args.get)).map(_ ++ _).zip(params.get).map(
              (x,y) => /*if(y._1.spec) then x else x.literals2Prims*/ x // TODO: Specialization for literals
            ))
            debug.writeLine(s"old args ${oldArgs}")
            debug.writeLine(s"new args ${args}")
            debug.writeLine(s"merged args ${mergedArgs}")
            // FIXME: do paramless funcs need multiple evaluations? currently only eval paramless funcs once
            if (!nuEvalCnt.contains(name) || (hasArgs && (oldArgs.get zip mergedArgs.get).exists(x => x._1.compare(x._2)))) {
              nuFunImpls.update(name, (funDef, mp, mergedArgs, vals))
              if(!nuEvalQueue.contains(name))
                if(!nuEvalCnt.contains(name))
                  then 
                    debug.writeLine(s"first time eval function ${name}")
                    nuUpdateFunction(name)
                  else 
                    debug.writeLine(s"new arg eval function ${name}")
                    nuEvalQueue.add(name)
            }
            BoundedTerm(nuFunImpls.get(name).get._4)
          case Right(tp) => ???
  }

  private def nuUpdateFunc(funcName: String): Unit = {
    debug.writeLine(s"Evaluating ${funcName}")
    val (func, mps, args, res) = nuFunImpls.get(funcName).get
    debug.writeLine(s"args = ${args}")
    func.rhs match
      case Left(value) =>
        val params = extractLamParams(value) 
        val body = params match 
          case Some(_) => extractLamBody(value) 
          case None => value
        val ctx = params match
          case Some(p) => 
            if p.length != args.get.length
            then throw MonomorphError("Argument length mismatch in function update")
            else (p.map(_._2.name) zip args.get).toMap
          case None => Map()
        specializer.nuEvaluate(body)(using ctx, List(func.name), evaluationMap)
        evaluationMap.addOne(value, getRes(body))
        val oldExp = VarValMap.get(nuFunImpls.get(funcName).get._4)
        if (oldExp.compare(getRes(value))) {
          debug.writeLine(s"Bounds of ${funcName} changed, adding dependent functions to evalQueue")
          debug.writeLine(s"Before: ${oldExp}")
          debug.writeLine(s"After : ${getRes(value)}")
          nuFunDependence.get(funcName).get.foreach(x => if !nuEvalQueue.contains(x) then {
            debug.writeLine(s"Added ${x}")
            nuEvalQueue.add(x)
          })
        } else {
          debug.writeLine(s"No change in bounds of ${funcName}")
        }
        //debug.writeLine(s"old body: ${showStructure(value)} => new body: ${showStructure(nuBody)}")
        nuFunImpls.updateWith(funcName)(_.map(x => {
          VarValMap.update(x._4, getRes(value))
          (x._1, x._2, x._3, x._4)
        }))
      case Right(value) => throw MonomorphError("Should not update function typeDef")
  }

  /*
    Find a variable in the global env 
    TODO: Does TypeValue affect evaluation and dependence?
  */
  def nuFindVar(name: String)(using evalCtx: Map[String, BoundedTerm], callingStack: List[String]): BoundedTerm =
    nuFunImpls.get(name) match
      case Some(res) =>
        val (func, _, _, _) = res
        nuFunDependence.update(name, nuFunDependence.get(name).get ++ callingStack.headOption)
        val params = func.rhs match
          //case Left(Lam(lhs, rhs)) => Some(extractParams(lhs).map(_._2.name).toList)
          case Left(body) => extractLamParams(body).map(_.map(_._2.name).toList)
          case Right(tp) => ???
        params match 
          case Some(p) => BoundedTerm(FuncVal(name, params, Nil))
          case None => 
            val res = nuGetFuncRetVal(name, None)
            res
      case None => 
        nuAllTypeImpls.get(name) match
          case Some(res) => BoundedTerm(TypeVal(name))
          case None => throw MonomorphError(s"Variable ${name} not found during evaluation")

  def nuCreateObjValue(tpName: String, args: List[BoundedTerm]): MonoVal = 
    nuAllTypeImpls.get(tpName) match
      case Some(NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, _, _, body)) => 
        debug.writeLine(s"Creating Object Value for ${tpName} with arguments ${args}")
        debug.indent()
        val ags = (params match
          case Some(p) => 
            if (extractObjParams(p).length != args.length) throw MonomorphError("ObjValue param mismatch")
            extractObjParams(p).map(_._2.name).zip(args).toList // FIXME: Different structure for Obj Params
          case None => Nil)
        val obj = ObjVal(tpName, ags.map((p, _) => p), MutMap(ags: _*)) // TODO: parent object fields
        debug.writeLine(s"Parents term is ${parents}")
        val parentObjs = parents.map{
          case Var(name) => BoundedTerm(nuCreateObjValue(name, Nil))
          case App(Var(name), t: Tup) => 
            specializer.nuEvaluate(t)(using Map("this"->BoundedTerm(obj)) ++ ags, List(tpName), evaluationMap)
            BoundedTerm(nuCreateObjValue(name, extractFuncArgs(t).map(getRes)))
          case other => throw MonomorphError(s"Unexpected parent object format ${other}")
        }
        debug.writeLine(s"Parent objects are ${parentObjs}")
        obj.fields.addAll(parentObjs.zipWithIndex.map((e, i) => s"sup$$$i" -> e))
        debug.writeLine(s"Created Object Value ${obj}")
        debug.outdent()
        obj
      case None => throw MonomorphError(s"TypeName ${tpName} not found in implementations ${nuAllTypeImpls}")

  def createTupVal(fields: List[BoundedTerm]): TupVal = 
    TupVal(fields.zipWithIndex.map((term, i) => (Var(i.toString()) -> term)).toMap)

  def nuGetFieldVal(obj: ObjVal, field: String): BoundedTerm =
    debug.writeLine(s"select ${field} from ${obj.name}")
    nuAllTypeImpls.get(obj.name) match
      case None => throw MonomorphError(s"ObjectValue ${obj} not found in implementations ${nuAllTypeImpls}")
      case Some(typeDef) => 
        typeDef.body.entities.flatMap{
          case func@NuFunDef(_, Var(nme), _, _, Left(_)) if nme.equals(field) => Some(func)
          case _ => None
        }.headOption match
        case Some(NuFunDef(isLetRec, Var(nme), sn, tp, Left(body))) => 
          debug.writeLine(s"found some func")
          val nuFuncName = s"${nme}$$${obj.name}"
          if (!nuFunImpls.contains(nuFuncName)) {
            nuAddFunction(NuFunDef(isLetRec, Var(nuFuncName), sn, tp, Left(addThisParam(body)))(None, None, None, None, false))
          } 
          BoundedTerm(FuncVal(nuFuncName, extractLamParams(body).map(_.map(_._2.name).toList), List("this" -> BoundedTerm(obj))))
        case _ => 
          debug.writeLine(s"did not find func, try obj fields")
          obj.fields.get(field) match
          case Some(value) => value
          case None => 
            debug.writeLine(s"did not find in fields, try superclass")
            obj.fields.flatMap(x => {
              if (x._1.matches("sup\\$[0-9]+")) {
                x._2.asValue match{
                  case Some(o: ObjVal) => 
                    Some(nuGetFieldVal(o, field))
                  case _ => None
                }
              }
              else None
            }).headOption match
              case Some(value) => value
              case None => throw MonomorphError(s"Field value ${field} not found in ObjectValue ${obj}")