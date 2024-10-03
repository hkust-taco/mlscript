package mlscript
package compiler
package mono

import scala.collection.immutable.{HashMap, ListMap}
import scala.collection.mutable.{Map as MutMap, Set as MutSet}
import scala.collection.mutable.ListBuffer
import java.util.IdentityHashMap
import scala.jdk.CollectionConverters._
import mlscript.Mod

class Monomorph(debug: Debug = DummyDebug):
  import Helpers._
  import Monomorph._

  /**
   * Specialized implementations of function declarations.
   * function name -> (function, mutable parameters (?), parameters, output value)
   */
  private val funImpls = MutMap[String, (NuFunDef, MutMap[String, NuFunDef], Option[List[BoundedTerm]], VarVal)]()

  private val funDependence = MutMap[String, Set[String]]()

  val evalQueue = MutSet[String]()
  val evalCnt = MutMap[String, Int]()
  
  private val allTypeImpls = MutMap[String, NuTypeDef]()

  private def addType(typeDef: NuTypeDef) =
    allTypeImpls.addOne(typeDef.name, typeDef)
  
  val specializer = new Specializer(this)(using debug)


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

  private def addFunction(func: NuFunDef): Unit = {
    debug.writeLine(s"Adding Function ${func}")
    funImpls.addOne(func.name, (func, MutMap(), func.body match
      case Lam(Tup(params), body) => Some(params.map(_ => BoundedTerm()))
      case _ => None
    , VarValMap.refresh()))
    funDependence.addOne(func.name, Set())
  }

  private def getResult(mains: List[Statement]): List[Statement] = 
    List[Statement]()
    .concat(allTypeImpls.values.map(_.copy(body = TypingUnit(Nil))(None, None, Nil)))
    .concat(funImpls.values.map(_._1))
    .concat(mains)
  
  def defunctionalize(tu: TypingUnit): TypingUnit =
    val nuTerms = tu.entities.zipWithIndex.flatMap {
      case (term: Term, i) =>
        val mainFunc = NuFunDef(None, Var(s"main$$$$$i"), None, Nil, Left(Lam(Tup(Nil), term)))(None, None, None, None, None, false, Nil)
        addFunction(mainFunc)
        evalQueue.add(mainFunc.name)
        Some(App(Var(s"main$$$$$i"), Tup(Nil)))
      case (tyDef: NuTypeDef, _) =>
        addType(tyDef)
        None
      case (funDef: NuFunDef, _) =>
        funDef.rhs match
          case Left(value) => addFunction(funDef)
          case Right(value) => ??? 
        None
      case _ => ???
    }
    while (!evalQueue.isEmpty) {
      debug.writeLine(s"Queue: ${evalQueue}")
      val next = evalQueue.head
      evalQueue.remove(next)
      updateFunc(next)
    }
    debug.writeLine(s"${PrettyPrinter.showTypingUnit(TypingUnit(getResult(nuTerms)))}")
    debug.writeLine(s"========DEFUNC PHASE========")
    funImpls.mapValuesInPlace{
      case (_, (func@NuFunDef(isLetRec, nm, sn, tp, rhs), mp, la, lr)) =>
        rhs match 
          case Left(Lam(lhs, rhs)) =>
            (NuFunDef(isLetRec, nm, sn, tp, Left(Lam(lhs,specializer.defunctionalize(rhs)(using evaluationMap))))(None, None, None, None, None, false, Nil), mp, la, lr)
          case Left(body) => 
            (NuFunDef(isLetRec, nm, sn, tp, Left(specializer.defunctionalize(body)(using evaluationMap)))(None, None, None, None, None, false, Nil), mp, la, lr)
          case Right(tp) => ???
    }
    val ret = getResult(nuTerms)
    TypingUnit(ret)

  def getFuncRetVal(name: String, args: Option[List[BoundedTerm]])(using evalCtx: Map[String, BoundedTerm], callingStack: List[String]): BoundedTerm = {
    funImpls.get(name) match
      case None => throw MonomorphError(s"Function ${name} does not exist")
      case Some((funDef, mp, oldArgs, vals)) => 
        funDef.rhs match
          case Left(body) => 
            funDependence.update(name, funDependence.getOrElse(name, Set()) ++ callingStack.headOption)
            val hasArgs = oldArgs.isDefined
            val params = extractLamParams(body)
            val mergedArgs = oldArgs.map(old => (old zip (args.get)).map(_ ++ _).zip(params.get).map(
              (x,y) => /*if(y._1.spec) then x else x.literals2Prims*/ x // TODO: Specialization for literals
            ))
            debug.writeLine(s"old args ${oldArgs}")
            debug.writeLine(s"new args ${args}")
            debug.writeLine(s"merged args ${mergedArgs}")
            // FIXME: do paramless funcs need multiple evaluations? currently only eval paramless funcs once
            if (!evalCnt.contains(name) || (hasArgs && (oldArgs.get zip mergedArgs.get).exists(x => x._1.compare(x._2)))) {
              funImpls.update(name, (funDef, mp, mergedArgs, vals))
              if(!evalQueue.contains(name))
                if(!evalCnt.contains(name))
                  then 
                    debug.writeLine(s"first time eval function ${name}")
                    updateFunc(name)
                  else 
                    debug.writeLine(s"new arg eval function ${name}")
                    evalQueue.add(name)
            }
            BoundedTerm(funImpls.get(name).get._4)
          case Right(tp) => ???
  }

  private def updateFunc(funcName: String): Unit = {
    val updateCount = evalCnt.get(funcName).getOrElse(0)
    if(updateCount > 10){
      throw new MonomorphError("stack overflow!!!")
    }
    debug.writeLine(s"updating ${funcName} for ${updateCount}th time")
    evalCnt.update(funcName, updateCount+1)
    debug.writeLine(s"Evaluating ${funcName}")
    val (func, mps, args, res) = funImpls.get(funcName).get
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
        specializer.evaluate(body)(using ctx, List(func.name), evaluationMap)
        evaluationMap.addOne(value, getRes(body))
        val oldExp = VarValMap.get(funImpls.get(funcName).get._4)
        if (oldExp.compare(getRes(value))) {
          debug.writeLine(s"Bounds of ${funcName} changed, adding dependent functions to evalQueue")
          debug.writeLine(s"Before: ${oldExp}")
          debug.writeLine(s"After : ${getRes(value)}")
          funDependence.get(funcName).get.foreach(x => if !evalQueue.contains(x) then {
            debug.writeLine(s"Added ${x}")
            evalQueue.add(x)
          })
        } else {
          debug.writeLine(s"No change in bounds of ${funcName}")
        }
        //debug.writeLine(s"old body: ${showStructure(value)} => new body: ${showStructure(nuBody)}")
        funImpls.updateWith(funcName)(_.map(x => {
          VarValMap.update(x._4, getRes(value))
          (x._1, x._2, x._3, x._4)
        }))
      case Right(value) => throw MonomorphError("Should not update function typeDef")
  }

  /*
    Find a variable in the global env 
  */
  def findVar(name: String)(using evalCtx: Map[String, BoundedTerm], callingStack: List[String]): BoundedTerm =
    funImpls.get(name) match
      case Some(res) =>
        val (func, _, _, _) = res
        funDependence.update(name, funDependence.get(name).get ++ callingStack.headOption)
        val params = func.rhs match
          case Left(body) => extractLamParams(body).map(_.map(_._2.name).toList)
          case Right(tp) => ???
        params match 
          case Some(p) => BoundedTerm(FuncVal(name, params, Nil))
          case None => 
            val res = getFuncRetVal(name, None)
            res
      case None => 
        allTypeImpls.get(name) match
          case Some(res) if res.kind == Cls => BoundedTerm(TypeVal(name))
          case Some(res) if res.kind == Mod => BoundedTerm(createObjValue(name, Nil))
          case None => throw MonomorphError(s"Variable ${name} not found during evaluation")
          case _ => throw MonomorphError(s"Variable ${name} unhandled")

  def createObjValue(tpName: String, args: List[BoundedTerm]): MonoVal = 
    allTypeImpls.get(tpName) match
      case Some(NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, _, _, body)) => 
        debug.writeLine(s"Creating Object Value for ${tpName} with arguments ${args}")
        debug.indent()
        val ags = (params match
          case Some(p) => 
            if (extractObjParams(p).length != args.length) throw MonomorphError("ObjValue param mismatch")
            extractObjParams(p).map(_._2.name).zip(args).toList // FIXME: Different structure for Obj Params
          case None => Nil)
        val obj = ObjVal(tpName, ags.map((p, _) => p), MutMap(ags*)) // TODO: parent object fields
        debug.writeLine(s"Parents term is ${parents}")
        val parentObjs = parents.map{
          case Var(name) => BoundedTerm(createObjValue(name, Nil))
          case App(Var(name), t: Tup) => 
            specializer.evaluate(t)(using Map("this"->BoundedTerm(obj)) ++ ags, List(tpName), evaluationMap)
            BoundedTerm(createObjValue(name, extractFuncArgs(t).map(getRes)))
          case other => throw MonomorphError(s"Unexpected parent object format ${other}")
        }
        debug.writeLine(s"Parent objects are ${parentObjs}")
        obj.fields.addAll(parentObjs.zipWithIndex.map((e, i) => s"sup$$$i" -> e))
        debug.writeLine(s"Created Object Value ${obj}")
        debug.outdent()
        obj
      case None => throw MonomorphError(s"TypeName ${tpName} not found in implementations ${allTypeImpls}")

  def createTupVal(fields: List[BoundedTerm]): TupVal = 
    TupVal(fields.zipWithIndex.map((term, i) => (Var(i.toString()) -> term)).toMap)

  def getFieldVal(obj: ObjVal, field: String): BoundedTerm =
    debug.writeLine(s"select ${field} from ${obj.name}")
    allTypeImpls.get(obj.name) match
      case None => throw MonomorphError(s"ObjectValue ${obj} not found in implementations ${allTypeImpls}")
      case Some(typeDef) => 
        typeDef.body.entities.flatMap{
          case func@NuFunDef(_, Var(nme), _, _, Left(_)) if nme.equals(field) => Some(func)
          case _ => None
        }.headOption match
        case Some(NuFunDef(isLetRec, Var(nme), sn, tp, Left(body))) => 
          debug.writeLine(s"found some func")
          val nuFuncName = s"${nme}$$${obj.name}"
          if (!funImpls.contains(nuFuncName)) {
            addFunction(NuFunDef(isLetRec, Var(nuFuncName), sn, tp, Left(addThisParam(body)))(None, None, None, None, None, false, Nil))
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
                    Some(getFieldVal(o, field))
                  case _ => None
                }
              }
              else None
            }).headOption match
              case Some(value) => value
              case None => throw MonomorphError(s"Field value ${field} not found in ObjectValue ${obj}")