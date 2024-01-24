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
import mlscript.compiler.mono.specializer.Builtin
import mlscript.compiler.mono.specializer.Context
import mlscript.compiler.*
import mlscript.compiler.printer.ExprPrinter
import mlscript.compiler.mono.specializer.BoundedExpr
import mlscript.compiler.mono.specializer.{MonoValue, TypeValue, ObjectValue, UnknownValue, FunctionValue, VariableValue}
import mlscript.compiler.mono.specializer.{MonoVal, TypeVal, ObjVal, FuncVal, LiteralVal, PrimVal, VarVal, TupVal, UnknownVal, BoundedTerm}
import java.util.IdentityHashMap
import scala.collection.JavaConverters._

class Monomorph(debug: Debug = DummyDebug) extends DataTypeInferer:
  import Helpers._
  import Monomorph._

  /**
   * Specialized implementations of function declarations.
   * function name -> (function, mutable parameters (?), parameters, output value)
   */
  private val funImpls = MutMap[String, (Item.FuncDecl, MutMap[String, Item.FuncDecl], Option[List[BoundedExpr]], VariableValue)]()
  private val nuFunImpls = MutMap[String, (NuFunDef, MutMap[String, NuFunDef], Option[List[BoundedTerm]], VarVal)]()

  private def getfunInfo(nm: String): String = 
    val info = funImpls.get(nm).get
    s"$nm: (${info._3.mkString(" X ")}) -> ${info._4} @${funDependence.get(nm).get.mkString("{", ", ", "}")}"

  private val funDependence = MutMap[String, Set[String]]()
  private val nuFunDependence = MutMap[String, Set[String]]()

  val evalQueue = MutSet[String]()
  val evalCnt = MutMap[String, Int]()

  val nuEvalQueue = MutSet[String]()
  val nuEvalCnt = MutMap[String, Int]()
  
  /**
   * Specialized implementations of each type declarations.
   */
  private val tyImpls = MutMap[String, SpecializationMap[Item.TypeDecl]]()
  private val allTypeImpls = MutMap[String, Item.TypeDecl]()
  
  //private val nuTyImpls = MutMap[TypeName, SpecializationMap[NuTypeDef]]()
  private val nuAllTypeImpls = MutMap[String, NuTypeDef]()
  /**
   * Add a prototype type declaration.
   */
  private def addPrototypeTypeDecl(typeDecl: Item.TypeDecl) =
    tyImpls.addOne(typeDecl.name.name, SpecializationMap(typeDecl))
    allTypeImpls.addOne(typeDecl.name.name, typeDecl)

  private def nuAddType(typeDef: NuTypeDef) =
    //nuTyImpls.addOne(typeDef.nme, SpecializationMap(typeDef))
    nuAllTypeImpls.addOne(typeDef.name, typeDef)

  /**
   * An iterator going through all type declarations.
   */
  private def allTypeDecls: IterableOnce[Item.TypeDecl] =
    tyImpls.values.flatMap { _.iterator }

  /**
   * A global store of monomorphized lambda classes.
   */
  private val lamTyDefs = MutMap[String, Item.TypeDecl]()
  /**
   * A global store of anonymous classes. For example, `new { ... }`.
   */
  private val anonymTyDefs = MutMap[String, Item.TypeDecl]()

  def findClassByName(name: String): Option[mlscript.compiler.Item.TypeDecl] =
    allTypeImpls.get(name)
  
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

  private def addNewFunction(func: Item.FuncDecl): Unit = {
    funImpls.addOne(func.name.name, (func, MutMap(), func.params match
        case Some(p) => Some(p.map(_ => BoundedExpr()))
        case None => None
      , VariableValue.refresh()
      ))
    funDependence.addOne(func.name.name, Set())
  }

  private def nuAddFunction(func: NuFunDef): Unit = {
    debug.writeLine(s"Adding Function ${func}")
    nuFunImpls.addOne(func.name, (func, MutMap(), func.body match
      case Lam(Tup(params), body) => Some(params.map(_ => BoundedTerm()))
      case _ => None
    , VarValMap.refresh()))
    nuFunDependence.addOne(func.name, Set())
  }

  private def getResult(exps: List[Expr]) = mlscript.compiler.ModuleUnit(
    Iterable[Expr | Item]()
    .concat(allTypeImpls.values.map(_.copy(body = Isolation(Nil))))
    .concat(funImpls.map(x => x._2._1))
    .concat(lamTyDefs.values)
    .concat(anonymTyDefs.values)
    .concat(exps)
    .toList)

  private def nuGetResult(mains: List[Statement]): List[Statement] = 
    List[Statement]()
    .concat(nuAllTypeImpls.values.map(_.copy(body = TypingUnit(Nil))(None, None)))
    .concat(nuFunImpls.values.map(_._1))
    .concat(mains)
  
  /**
   * This function defunctionalizes the top-level `TypingUnit` into a `Module`.
   */
  def defunctionalize(tu: TypingUnit): ModuleUnit =
    // debug.trace("MONO MODL", PrettyPrinter.show(tu)) {
      val exps = tu.entities.zipWithIndex.flatMap[Expr] {
        case (term: Term, i) =>
          val exp = term2Expr(term)
          val funcName = s"main$$$$$i"
          val asFunc: Item.FuncDecl = Item.FuncDecl(None, Expr.Ref(funcName), Some(Nil), exp)
          addNewFunction(asFunc)
          evalQueue.addOne(funcName)
          Some(Expr.Apply(Expr.Ref(funcName), Nil))
        case (tyDef: NuTypeDef, _) => 
          val ret = type2Item(tyDef)
          addPrototypeTypeDecl(ret)
          None
        case (funDef: NuFunDef, _) =>
          val funcItem = func2Item(funDef)
          funcItem match
            case funcDecl: Item.FuncDecl =>
              addNewFunction(funcDecl)
            case _ => ()
          None
        case (other, _) => throw MonomorphError(s"Unknown Statement in TypingUnit: ${other}")
      };
      debug.log(getResult(exps).getDebugOutput.toLines(using false).mkString("\n"))
      while(!evalQueue.isEmpty){
        val crt = evalQueue.head
        evalQueue.remove(crt)
        updateFunction(crt)
      }
      funImpls.mapValuesInPlace{
        case (_, (Item.FuncDecl(isLetRec, nm, p, body), mp, la, lr)) =>
          (Item.FuncDecl(isLetRec, nm, p, specializer.defunctionalize(body)), mp, la, lr)
      }
      val ret = getResult(exps)
      debug.log("")
      debug.log("==============final function signatures==================")
      try {
        funImpls.foreach(
          (nm, info) => {
            debug.log(s"$nm: (${info._3.mkString(" X ")}) -> ${info._4}")
          }
        )
      } catch e => (
        debug.log(s"ERROR: ${e.getStackTrace().take(20).mkString("\n")}")
      )
       
      ret
    // }()
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
  
  def toTypingUnit(mu: ModuleUnit): TypingUnit =
    val statements = mu.items.flatMap {
      case e: Expr => Some(expr2Term(e))
      case i: Item => Some(item2Term(i))
    }
    TypingUnit(statements)

  private def updateFunction(crt: String): Unit = {
    debug.log(s"evaluating $crt, rests: ${evalQueue}")
    val cnt = evalCnt.get(crt).getOrElse(0)
    if(cnt <= 10){
      evalCnt.update(crt, cnt+1)
      debug.log("=" * 10 + s" updating $crt " + "=" * 10)
      debug.log(getfunInfo(crt))
      updateFunc(crt)
      debug.log(getfunInfo(crt))
    }
    else{
      throw new MonomorphError("stack overflow!!!")
    }
  }

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

  /**
   * This function monomorphizes the nested `TypingUnit` into a `Isolation`.
   */
  private def trans2Expr(body: TypingUnit): Isolation =
    debug.trace("MONO BODY", PrettyPrinter.show(body)) {
      Isolation(body.entities.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
        case term: Term =>
          Some(term2Expr(term))
        case tyDef: NuTypeDef => 
          val ret = type2Item(tyDef)
          addPrototypeTypeDecl(ret)
          None
        case funDef: NuFunDef =>
          Some(func2Item(funDef))
        case other => throw MonomorphError(s"Unknown Statement in TypingUnit: ${other}")
      })
    }(identity)
  
  def getFuncRetVal(name: String, args: List[BoundedExpr])(using evalCtx: Context, callingStack: List[String]): BoundedExpr = {
    debug.trace[BoundedExpr]("SPEC CALL", name + args.mkString(" with (", ", ", ")")) {
      if(funImpls.contains(name)){
        val (funcdecl, mps, oldArgs, oldVs) = funImpls.get(name).get
        oldArgs match
          case Some(b) =>
            val oldArgs = b
            val old = funDependence.get(name).get
            funDependence.update(name, old ++ callingStack.headOption)
            // debug.log(s"adding dependence ${callingStack.headOption}")
            val nArgs = (oldArgs zip (args.map(_.unfoldVars))).map(_ ++ _).zip(funcdecl.params.getOrElse(Nil)).map(
              (x,y) => if(y._1.spec) then x else x.literals2Prims
            )
            
            debug.log(s"comparing ${oldArgs.mkString("(", ", ", ")")} with ${nArgs.map(_.getDebugOutput).mkString("(", ", ", ")")}")
            if(evalCnt.get(name).isEmpty || (oldArgs zip nArgs).find(x => x._1.compare(x._2)).isDefined){
              funImpls.update(name, (funcdecl, mps, Some(nArgs), oldVs))
              if(!evalQueue.contains(name)){
                if(evalCnt.get(name).isEmpty){
                  debug.log(s"first time encounter $name")
                  updateFunction(name)
                }
                else{
                  debug.log(s"find finer args")
                  evalQueue.add(name)
                }
              }
            }
          case None => ()
        BoundedExpr(funImpls.get(name).get._4)
      }
      else {
        debug.log(s"calling unknown function $name(${args.mkString(",")})")
        debug.log(funImpls.keySet.toString())
        BoundedExpr(UnknownValue())
      }
    }(identity)
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

  private def updateFunc(name: String): Unit = {
    val (funcdecl, mps, args, _) = funImpls.get(name).get
    funcdecl.params match
      case Some(p) => 
        val ctx = (p.map(_._2.name) zip args.getOrElse(Nil)).toMap
        val nBody = specializer.evaluate(funcdecl.body)(using Context()++ctx, List(funcdecl.name.name))
        val nVs = nBody.expValue
        val oldVs = VariableValue.get(funImpls.get(name).get._4)
        debug.log(s"comparing ${oldVs} with ${nVs}")
        if(oldVs.compare(nVs)){
          debug.log(s"adding these funcs to queue: ${funDependence.get(name).get}")
          funDependence.get(name).get.foreach(x => if !evalQueue.contains(x) then evalQueue.add(x))
        }
        funImpls.updateWith(name)(_.map(x => {
          val nFuncDecl: Item.FuncDecl = x._1.copy(body = nBody)
          VariableValue.update(x._4, nVs)
          (nFuncDecl, x._2, x._3, x._4)
        }))
      case None => ()
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

  def findVar(name: String)(using evalCtx: Context, callingStack: List[String]): MonoValue = {
    if(funImpls.contains(name)){
      val funcBody = funImpls.get(name).get
      funDependence.update(name, funDependence.get(name).get ++ callingStack.headOption)
      FunctionValue(name, funcBody._1.params.getOrElse(Nil).map(_._2.name), Nil)
    }
    else{
      UnknownValue()
    }
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

  private def partitationArguments(name: String, params: List[Parameter], args: List[Expr]): (List[Expr], List[Expr]) =
    if (args.length != params.length) {
      debug.log("")
      throw MonomorphError(s"$name expect ${params.length} arguments but ${args.length} were given")
    }
    val staticArguments = params.iterator.zip(args).flatMap({
      case ((flags, _, _), value) if flags.spec => Some(value)
      case _ => None
    }).toList
    val dynamicArguments = params.iterator.zip(args).flatMap({
      case ((flags, _, _), value) if !flags.spec => Some(value)
      case _ => None
    }).toList
    (staticArguments, dynamicArguments)

  private def generateSignature(staticArguments: List[Expr])(using MonomorphContext): String =
    staticArguments.iterator.map(infer(_, None)).mkString("__", "_", "")

  private def specializeClassCall(name: String, args: List[Expr])(using MonomorphContext): Option[Expr] =
    debug.trace("SPEC CALL", "class " + name + args.mkString(" with (", ", ", ")")) {
      ???
    }(_.fold(Debug.noPostTrace)(identity))

  def createObjValue(tpName: String, args: List[BoundedExpr]): MonoValue = 
    debug.trace("SPEC NEW", s"$tpName($args)"){
    if(allTypeImpls.contains(tpName)){
      val tp = allTypeImpls.get(tpName).get
      val ags = (tp.params.getOrElse(Nil).map(_._2.name) zip args) // FIXME: May not be correct
      val ret = ObjectValue(tpName, MutMap(ags: _*))
      val pars = tp.parents.map((supTp, prms) => {
        val evArgs = prms.map(specializer.evaluate(_)(using Context() ++ (("this"->BoundedExpr(ret)) :: ags), List(tpName)).expValue)
        BoundedExpr(createObjValue(supTp.base.name, evArgs))
      })
      val parObjs = pars.zipWithIndex.map((e, i) => s"sup$$$i" -> e)
      debug.log(s"par objs: $parObjs")
      ret.fields.addAll(parObjs)
      ret
    }
    else throw MonomorphError(s"tpName ${tpName} not found in implementations ${allTypeImpls}")
  }(identity)

  def nuCreateObjValue(tpName: String, args: List[BoundedTerm]): MonoVal = 
    nuAllTypeImpls.get(tpName) match
      case Some(NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, _, _, body)) => 
        val ags = (params match
          case Some(p) => 
            if (extractObjParams(p).length != args.length) throw MonomorphError("ObjValue param mismatch")
            extractObjParams(p).map(_._2.name).zip(args).toList // FIXME: Different structure for Obj Params
          case None => Nil)
        val obj = ObjVal(tpName, ags.map((p, _) => p), MutMap(ags: _*)) // TODO: parent object fields
        val parentObjs = parents.map{
          case Var(name) => BoundedTerm(nuCreateObjValue(name, Nil))
          case App(Var(name), t: Tup) => 
            specializer.nuEvaluate(t)(using Map("this"->BoundedTerm(obj)) ++ ags, List(tpName), evaluationMap)
            BoundedTerm(nuCreateObjValue(name, extractFuncArgs(t).map(getRes)))
          case other => throw MonomorphError(s"Unexpected parent object format ${other}")
        }
        obj.fields.addAll(parentObjs.zipWithIndex.map((e, i) => s"sup$$$i" -> e))
        obj
      case None => throw MonomorphError(s"TypeName ${tpName} not found in implementations ${nuAllTypeImpls}")

  def createTupVal(fields: List[BoundedTerm]): TupVal = 
    TupVal(fields.zipWithIndex.map((term, i) => (Var(i.toString()) -> term)).toMap)

  def getFieldVal(obj: ObjectValue, field: String): BoundedExpr = 
    debug.trace("SPEC SEL", s"$obj :: $field"){
    if(allTypeImpls.contains(obj.name)){
      val tpDef = allTypeImpls.get(obj.name).get
      val func = tpDef.body.items.flatMap{
        case funcDecl@Item.FuncDecl(isLetRec, Expr.Ref(nm), prms, bd) if nm.equals(field) =>
          Some(funcDecl)
        case _ => None
      }.headOption
      if(func.isDefined){
        debug.log("defined")
        val Item.FuncDecl(isLetRec, nm, prms, bd) = func.get
        val nFuncName = s"${nm.name}$$${obj.name}"
        if(!funImpls.contains(nFuncName)){
          val nFunc: Item.FuncDecl = Item.FuncDecl(isLetRec, Expr.Ref(nFuncName), Some((FldFlags.empty, Expr.Ref("this"), None) :: prms.getOrElse(Nil)), bd)
          addNewFunction(nFunc)
        }
        BoundedExpr(FunctionValue(nFuncName, prms.getOrElse(Nil).map(_._2.name), List("this" -> BoundedExpr(obj))))
      }
      else if(obj.fields.contains(field))
        debug.log("contains")
        obj.fields.get(field).get
      else{
        debug.log("else")
        obj.fields.flatMap(x => {
          if (x._1.matches("sup\\$[0-9]+")) {
            x._2.asValue match{
              case Some(o: ObjectValue) => 
                Some(getFieldVal(o, field))
              case _ => None
            }
          }
          else None
        }).headOption.getOrElse(
          throw MonomorphError(s"Field ${field} not Found in"+obj.toString())
        )
      }
    }
    else {
      throw MonomorphError(s"ObjectValue ${obj} not found in implementations ${allTypeImpls}")
    }
  }(identity)

  def nuGetFieldVal(obj: ObjVal, field: String): BoundedTerm =
    debug.writeLine(s"select ${field} from ${obj.name}")
    nuAllTypeImpls.get(obj.name) match
      case None => throw MonomorphError(s"ObjectValue ${obj} not found in implementations ${allTypeImpls}")
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

object Monomorph:
  class SpecializationMap[T <: Item](val prototype: T):
    private var basePrototype: Option[T] = None
    private val implementations = MutMap[String, T]()

    inline def getOrInsert(signature: String, op: => T): T =
      implementations.getOrElseUpdate(signature, op)
    inline def size: Int = implementations.size
    // signature + item
    inline def +=(entry: (String, T)): T =
      implementations.addOne(entry)
      entry._2
    inline def base: Option[T] = basePrototype
    inline def base_=(op: => T): Unit =
      basePrototype match 
        case None => basePrototype = Some(op)
        case Some(_) => ()
    inline def isEmpty: Boolean = implementations.isEmpty
    inline def iterator: Iterator[T] =
      if implementations.isEmpty then Iterator.empty else
        basePrototype.iterator.concat(implementations.values)