package mlscript.compiler.mono

import mlscript.compiler.debug.{Debug, DummyDebug}
import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.{AppliedType, TypeName}
import mlscript.{App, Asc, Assign, Bind, Blk, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, If}
import mlscript.{IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import scala.collection.immutable.{HashMap}
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
import mlscript.compiler.mono.specializer.{MonoValue, ObjectValue, UnknownValue, FunctionValue, VariableValue}

class Monomorph(debug: Debug = DummyDebug) extends DataTypeInferer:
  import Helpers._
  import Monomorph._

  /**
   * Specialized implementations of function declarations.
   */
  private val funImpls = MutMap[String, (Item.FuncDecl, MutMap[String, Item.FuncDecl], List[BoundedExpr], VariableValue)]()

  private def getfunInfo(nm: String): String = 
    val info = funImpls.get(nm).get
    s"$nm: (${info._3.mkString(" X ")}) -> ${info._4} @${funDependence.get(nm).get.mkString("{", ", ", "}")}"

  private val funDependence = MutMap[String, Set[String]]()

  val evalQueue = MutSet[String]()
  val evalCnt = MutMap[String, Int]()
  
  /**
   * Specialized implementations of each type declarations.
   */
  private val tyImpls = MutMap[String, SpecializationMap[Item.TypeDecl]]()
  private val allTypeImpls = MutMap[String, Item.TypeDecl]()
  /**
   * Add a prototype type declaration.
   */
  private def addPrototypeTypeDecl(typeDecl: Item.TypeDecl) =
    tyImpls.addOne(typeDecl.name.name, SpecializationMap(typeDecl))
    allTypeImpls.addOne(typeDecl.name.name, typeDecl)
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
  
  val specializer = mono.specializer.Specializer(this)(using debug)

  private def addNewFunction(func: Item.FuncDecl): Unit = {
    funImpls.addOne(func.name.name, (func, MutMap(), func.params.map(_ => BoundedExpr()), VariableValue.refresh()))
    funDependence.addOne(func.name.name, Set())
  }

  private def getResult(exps: List[Expr]) = mlscript.compiler.Module(exps.concat[Expr | Item](funImpls.map(x => x._2._1))
       .concat(allTypeImpls.values.map(x => x.copy(body = Isolation(Nil))))
       .concat(lamTyDefs.values)
       .concat(anonymTyDefs.values)
       .toList)

  /**
   * This function defunctionalizes the top-level `TypingUnit` into a `Module`.
   */
  def defunctionalize(tu: TypingUnit): Module =
    // debug.trace("MONO MODL", PrettyPrinter.show(tu)) {
      val exps = tu.entities.zipWithIndex.flatMap[Expr] {
        case (term: Term, i) =>
          val exp = term2Expr(term)
          val funcName = s"main$$$$$i"
          val asFunc: Item.FuncDecl = Item.FuncDecl(Expr.Ref(funcName), Nil, exp)
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
      };
      debug.log(getResult(exps).getDebugOutput.toLines(using false).mkString("\n"))
      while(!evalQueue.isEmpty){
        val crt = evalQueue.head
        evalQueue.remove(crt)
        updateFunction(crt)
      }
      funImpls.mapValuesInPlace{
        case (_, (Item.FuncDecl(nm, as, body), mp, la, lr)) =>
          (Item.FuncDecl(nm, as, specializer.defunctionalize(body)), mp, la, lr)
      }
      val ret = getResult(exps)
      debug.log("")
      debug.log("==============final function signatures==================")
      funImpls.foreach(
        (nm, info) => {
          debug.log(s"$nm: (${info._3.mkString(" X ")}) -> ${info._4}")
        }
      )
       
       ret
    // }()
  
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
      })
    }(identity)
  
  def getFuncRetVal(name: String, args: List[BoundedExpr])(using evalCtx: Context, callingStack: List[String]): BoundedExpr = {
    debug.trace[BoundedExpr]("SPEC CALL", name + args.mkString(" with (", ", ", ")")) {
      if(funImpls.contains(name)){
        val (funcdecl, mps, oldArgs, oldVs) = funImpls.get(name).get
        val old = funDependence.get(name).get
        funDependence.update(name, old ++ callingStack.headOption)
        // debug.log(s"adding dependence ${callingStack.headOption}")
        val nArgs = (oldArgs zip (args.map(_.unfoldVars))).map(_ ++ _).zip(funcdecl.params).map(
          (x,y) => if(y._1) then x else x.literals2Prims
        )
        
        debug.log(s"comparing ${oldArgs.mkString("(", ", ", ")")} with ${nArgs.map(_.getDebugOutput).mkString("(", ", ", ")")}")
        if(evalCnt.get(name).isEmpty || (oldArgs zip nArgs).find(x => x._1.compare(x._2)).isDefined){
          funImpls.update(name, (funcdecl, mps, nArgs, oldVs))
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
        BoundedExpr(funImpls.get(name).get._4)
      }
      else {
        debug.log("!!!!!!!")
        debug.log(s"calling unknown function $name(${args.mkString(",")})")
        debug.log(funImpls.keySet.toString())
        BoundedExpr(UnknownValue())
      }
    }(identity)
  }

  private def updateFunc(name: String): Unit = {
    val (funcdecl, mps, args, _) = funImpls.get(name).get
    val ctx = (funcdecl.params.map(_._2.name) zip args).toMap
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
  }

  def findVar(name: String)(using evalCtx: Context, callingStack: List[String]): MonoValue = {
    if(funImpls.contains(name)){
      val funcBody = funImpls.get(name).get
      funDependence.update(name, funDependence.get(name).get ++ callingStack.headOption)
      FunctionValue(name, funcBody._1.params.map(_._2.name), Nil)
    }
    else{
      UnknownValue()
    }
  }

  private def partitationArguments(name: String, params: List[Parameter], args: List[Expr]): (List[Expr], List[Expr]) =
    if (args.length != params.length) {
      debug.log("")
      throw MonomorphError(s"$name expect ${params.length} arguments but ${args.length} were given")
    }
    val staticArguments = params.iterator.zip(args).flatMap({
      case ((true, _), value) => Some(value)
      case _ => None
    }).toList
    val dynamicArguments = params.iterator.zip(args).flatMap({
      case ((false, _), value) => Some(value)
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
      val ags = (tp.params.map(_._2.name) zip args)
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
    else ???
  }(identity)

  def getFieldVal(obj: ObjectValue, field: String): BoundedExpr = 
    debug.trace("SPEC SEL", s"$obj :: $field"){
    if(allTypeImpls.contains(obj.name)){
      val tpDef = allTypeImpls.get(obj.name).get
      val func = tpDef.body.items.flatMap{
        case funcDecl@Item.FuncDecl(Expr.Ref(nm), prms, bd) if nm.equals(field) =>
          Some(funcDecl)
        case _ => None
      }.headOption
      if(func.isDefined){
        val Item.FuncDecl(nm, prms, bd) = func.get
        val nFuncName = s"${nm.name}$$${obj.name}"
        if(!funImpls.contains(nFuncName)){
          val nFunc: Item.FuncDecl = Item.FuncDecl(Expr.Ref(nFuncName), (false, Expr.Ref("this")) :: prms, bd)
          addNewFunction(nFunc)
        }
        BoundedExpr(FunctionValue(nFuncName, prms.map(_._2.name), List("this" -> BoundedExpr(obj))))
      }
      else if(obj.fields.contains(field))
        obj.fields.get(field).get
      else{
        obj.fields.flatMap(x => {
          if (x._1.matches("sup\\$[0-9]+")) {
            x._2.asValue match{
              case Some(o: ObjectValue) => 
                Some(getFieldVal(o, field))
              case _ => None
            }
          }
          else None
        }).headOption.get//OrElse(BoundedExpr(UnknownValue()))
      }
    }
    else {
      ???
    }
  }(identity)

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