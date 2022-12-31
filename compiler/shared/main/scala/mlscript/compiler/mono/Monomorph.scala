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
  private val funImpls = MutMap[String, (Item.FuncDecl, MutMap[String, Item.FuncDecl], List[(BoundedExpr, Int)], VariableValue)]()

  private def getfunInfo(nm: String): String = 
    val info = funImpls.get(nm).get
    s"$nm: (${info._3.mkString(" X ")}) -> ${info._4} @${funDependence.get(nm).get.mkString("{", ", ", "}")}"

  // private def allFunImpls: IterableOnce[(Item.FuncDecl, Item.FuncDecl)] =
  //   funImpls.iterator.flatMap { case (name, (protoFunc, implFunc, _, _)) =>
  //     implFunc.values.map((protoFunc, _))
  //   }
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

  def addNewFunction(func: Item.FuncDecl): Unit = {
    funImpls.addOne(func.name.name, (func, MutMap(), func.params.map(_ => BoundedExpr()->0), VariableValue.refresh()))
    funDependence.addOne(func.name.name, Set())
  }

  def getResult(exps: List[Expr]) = mlscript.compiler.Module(exps.concat[Expr | Item](funImpls.map(x => x._2._1))
       .concat(allTypeImpls.values.map(x => x.copy(body = Isolation(Nil))))
       .concat(lamTyDefs.values)
       .concat(anonymTyDefs.values)
       .toList)

  /**
   * This function monomorphizes the top-level `TypingUnit` into a `Module`.
   */
  def monomorphize(tu: TypingUnit): Module =
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
          debug.log(s"$nm: (${info._3.map(_._1).mkString(" X ")}) -> ${info._4}")
          // updateFunc(nm)
          // debug.log("")
        }
      )
       
       ret
    // }()
  
  def updateFunction(crt: String): Unit = {
    debug.log(s"evaluating $crt, rests: ${evalQueue}")
    val cnt = evalCnt.get(crt).getOrElse(0)
    if(cnt <= 4){
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
  def monomorphizeBody(body: TypingUnit): Isolation =
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

  /**
   * This function flattens a top-level type definition and returns the root
   * type definition. There is a simple class lifting here.
   */
  // private def monomorphizeTypeDef(tyDef: NuTypeDef): Item.TypeDecl =
    // debug.trace("MONO TDEF", PrettyPrinter.show(tyDef)) {
      /**
       * The recursive function doing the real work.
       * @param tyDef the type definition
       * @param namePath enclosing class names and this class name
       */
      // def rec(tyDef: NuTypeDef, namePath: List[String]): Item.TypeDecl =
      //   // debug.trace[Item.TypeDecl]("LIFT", PrettyPrinter.show(tyDef)) {
      //     val NuTypeDef(kind, _, tparams, params, parents, body) = tyDef
      //     val isolation = Isolation(body.entities.flatMap {
      //       // Question: Will there be pure terms in class body?
      //       case term: Term =>
      //         Some(term2Expr(term))
      //       case subTypeDef: NuTypeDef =>
      //         rec(subTypeDef, subTypeDef.nme.name :: namePath)
      //         None
      //       case subFunDef: NuFunDef =>
      //         Some(monomorphizeFunDef(subFunDef))
      //     })
      //     val className = namePath.reverseIterator.mkString("_")
      //     val typeDecl: Item.TypeDecl = Item.TypeDecl(
      //       className, // name
      //       kind, // kind
      //       tparams, // typeParams
      //       toFuncParams(params).toList, // params
      //       parents.map {
      //         case Var(name) => (TypeName(name), Nil)
      //         case App(Var(name), _) => (TypeName(name), Nil)
      //         case _ => throw MonomorphError("unsupported parent term")
      //       }, // parents
      //       isolation // body
      //     )
      //     addPrototypeTypeDecl(typeDecl)
      //     typeDecl
      //   // }()

      // rec(tyDef, tyDef.nme.name :: Nil)
    // }(identity)
    
  /**
   * This function monomorphizes a function definition in smoe typing units.
   * @param tyDecls the destination of nested type declarations
   */
  // private def monomorphizeFunDef(funDef: NuFunDef): Item.FuncDecl | Item.FuncDefn =
  //   // debug.trace[Item.FuncDecl | Item.FuncDefn]("MONO FUNC", PrettyPrinter.show(funDef)) {
  //     val NuFunDef(_, nme, targs, rhs) = funDef
  //     rhs match
  //       case Left(Lam(params, body)) =>
  //         Item.FuncDecl(nme, toFuncParams(params).toList, term2Expr(body))
  //       case Left(body: Term) => Item.FuncDecl(nme, Nil, term2Expr(body))
  //       case Right(polyType) => Item.FuncDefn(nme, targs, polyType)
    // }(identity)

  /**
   * This function monomophizes a `Term` into an `Expr`.
   */
  // def monomorphizeTerm(term: Term)(using context: MonomorphContext): Expr =
  //   debug.trace[Expr]("MONO " + term.getClass.getSimpleName.toUpperCase, PrettyPrinter.show(term)) {
  //     term match
  //       case Var(name) => Expr.Ref(name)
  //       case Lam(lhs, rhs) => monomorphizeLambda(lhs, rhs)
  //       case App(App(Var("=>"), Bra(false, args: Tup)), body) =>
  //         monomorphizeLambda(args, body)
  //       case App(App(Var("."), self), App(Var(method), args: Tup)) =>
  //         debug.log(s"meet a member method invocation")
  //         Expr.Apply(Expr.Select(monomorphizeTerm(self), method), List.from(toFuncArgs(args).map(monomorphizeTerm)))
  //       case App(lhs, rhs) =>
  //         debug.log("Monomorphizing the callee...")
  //         val callee = monomorphizeTerm(lhs)
  //         debug.log("Monomorphizing arguments...")
  //         val arguments = toFuncArgs(rhs).map(monomorphizeTerm).toList
  //         debug.log("Specializing the invocation...")
  //         callee match
  //           case Expr.Ref(name) =>
  //             specializeCall(name, arguments).fold(Expr.Apply(callee, arguments))(identity)
  //           case _ => Expr.Apply(callee, arguments)
  //       case Tup(fields) =>
  //         Expr.Tuple(fields.map {
  //           case (_, Fld(mut, spec, value)) => monomorphizeTerm(value)
  //         })
  //       case Rcd(fields) =>
  //         Expr.Record(fields.map {
  //           case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(value))
  //         })
  //       case Sel(receiver, fieldName) =>
  //         Expr.Select(monomorphizeTerm(receiver), fieldName)
  //       case Let(true, Var(name), rhs, body) =>
  //         val exprRhs = monomorphizeTerm(rhs)(using context + (name, DataType.Unknown))
  //         val exprBody = monomorphizeTerm(body)(using context + (name, infer(exprRhs, None)))
  //         Expr.LetIn(true, name, exprRhs, exprBody)
  //       case Let(false, Var(name), rhs, body) =>
  //         val exprRhs = monomorphizeTerm(rhs)
  //         val exprBody = monomorphizeTerm(body)(using context + (name, infer(exprRhs, None)))
  //         Expr.LetIn(false, name, exprRhs, exprBody)
  //       case Blk(stmts) => Expr.Block(stmts.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
  //         case term: Term => Some(monomorphizeTerm(term))
  //         case tyDef: NuTypeDef =>
  //           monomorphizeTypeDef(tyDef)
  //           None
  //         case funDef: NuFunDef => Some(monomorphizeFunDef(funDef))
  //         case mlscript.DataDefn(_) => throw MonomorphError("unsupported DataDefn")
  //         case mlscript.DatatypeDefn(_, _) => throw MonomorphError("unsupported DatatypeDefn")
  //         case mlscript.TypeDef(_, _, _, _, _, _, _) => throw MonomorphError("unsupported TypeDef")
  //         case mlscript.Def(_, _, _, _) => throw MonomorphError("unsupported Def")
  //         case mlscript.LetS(_, _, _) => throw MonomorphError("unsupported LetS")
  //       })
  //       case Bra(rcd, term) => monomorphizeTerm(term)
  //       case Asc(term, ty) => Expr.As(monomorphizeTerm(term), ty)
  //       case _: Bind => throw MonomorphError("cannot monomorphize `Bind`")
  //       case _: Test => throw MonomorphError("cannot monomorphize `Test`")
  //       case With(term, Rcd(fields)) =>
  //         Expr.With(monomorphizeTerm(term), Expr.Record(fields.map {
  //           case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(term))
  //         }))
  //       case CaseOf(term, cases) => ???
  //       case Subs(array, index) =>
  //         Expr.Subscript(monomorphizeTerm(array), monomorphizeTerm(index))
  //       case Assign(lhs, rhs) =>
  //         Expr.Assign(monomorphizeTerm(lhs), monomorphizeTerm(rhs))
  //       case New(None, body) =>
  //         val className = s"Anonym_${anonymTyDefs.size}"
  //         val classDecl = Item.classDecl(className, Nil, monomorphizeBody(body))
  //         Expr.Apply(className, Nil)
  //       case New(Some((constructor, args)), body) =>
  //         val typeName = constructor match
  //           case AppliedType(TypeName(name), _) => name
  //           case TypeName(name)                 => name
  //         monomorphizeNew(typeName, toFuncArgs(args).toList, body)
  //       // case Blk(unit) => Expr.Isolated(monomorphizeBody(TypingUnit(unit)))
  //       case If(body, alternate) => body match
  //         case IfThen(condition, consequent) =>
  //           Expr.IfThenElse(
  //             monomorphizeTerm(condition),
  //             monomorphizeTerm(consequent),
  //             alternate.map(monomorphizeTerm)
  //           )
  //         case term: IfElse => throw MonomorphError("unsupported IfElse")
  //         case term: IfLet => throw MonomorphError("unsupported IfLet")
  //         case term: IfOpApp => throw MonomorphError("unsupported IfOpApp")
  //         case term: IfOpsApp => throw MonomorphError("unsupported IfOpsApp")
  //         case term: IfBlock => throw MonomorphError("unsupported IfBlock")
  //       case IntLit(value) => Expr.Literal(value)
  //       case DecLit(value) => Expr.Literal(value)
  //       case StrLit(value) => Expr.Literal(value)
  //       case UnitLit(undefinedOrNull) => 
  //         Expr.Literal(if undefinedOrNull
  //                      then UnitValue.Undefined
  //                      else UnitValue.Null)
  //   }(identity)

  // def monomorphizeLambda(args: Term, body: Term): Expr =
  //   debug.trace("MONO LAMBDA", args.toString + " => " + body) {
  //     val params = toFuncParams(args).toList
  //     // TODO: Capture variables referenced in the lambda body.
  //     // We should capture: closure variables and referenced type variables.
  //     val className = s"Lambda_${lamTyDefs.size}"
  //     val applyMethod: Item.FuncDecl =
  //       Item.FuncDecl("apply", toFuncParams(args).toList, term2Expr(body)(using MonomorphContext.empty))
  //     val classBody = Isolation(applyMethod :: Nil)
  //     val classDecl = Item.classDecl(className, Nil, classBody)
  //     // Add to the global store.
  //     lamTyDefs.addOne((className, classDecl))
  //     // Returns a class construction.
  //     Expr.Apply(Expr.Ref(className), Nil)
  //   }(identity)

  /**
   * `new C(...) { ... }` expressions are converted into
   * `{ class CImpl extends C(...) { ... }; CImpl() }`.
   * ~~This requires you to add a `LetClass` construct to `mlscript.Term`.~~
   */
  // def monomorphizeNew(name: String, termArgs: List[Term], termBody: TypingUnit): Expr.Apply =
  //   debug.trace[Expr.Apply]("MONO NEW", {
  //     name + termArgs.iterator.map(_.toString).mkString("(", ", ", ")") +
  //       " with " + PrettyPrinter.show(termBody)
  //   }) {
  //     val args = termArgs.map(term2Expr(_)(using MonomorphContext.empty))
  //     val body = monomorphizeBody(termBody)
  //     val specTypeDecl = specializeTypeDef(name, args, body)
  //     Expr.Apply(specTypeDecl.name, Nil)
  //   }(identity)

  // def specializeCall(name: String, args: List[Expr])(using MonomorphContext): Option[Expr] =
  //   debug.trace("SPEC CALL", name + args.mkString(" with (", ", ", ")")) {
  //     if tyImpls.contains(name) then specializeClassCall(name, args)
  //     else if funImpls.contains(name) then specializeFunctionCall(name, args)
  //     else {
  //       debug.log(s"Not found: $name")
  //       None
  //     }
  //   }()
  
  def monomorphizeCall(name: String, args: List[BoundedExpr])(using evalCtx: Context, callingStack: List[String]): BoundedExpr = {
    debug.trace[BoundedExpr]("SPEC CALL", name + args.mkString(" with (", ", ", ")")) {
      if(funImpls.contains(name)){
        val (funcdecl, mps, oldArgsWithCnt, oldVs) = funImpls.get(name).get
        val (oldArgs, lastUpdateCnt) = oldArgsWithCnt.unzip
        val old = funDependence.get(name).get
        funDependence.update(name, old ++ callingStack.headOption)
        // debug.log(s"adding dependence ${callingStack.headOption}")
        val nArgs = (oldArgs zip args).map(_ ++ _)
        debug.log(s"comparing ${oldArgsWithCnt.mkString("(", ", ", ")")} with ${nArgs.map(_.getDebugOutput).mkString("(", ", ", ")")}")
        if(evalCnt.get(name).isEmpty || (oldArgs zip nArgs).find(x => x._1.compare(x._2)).isDefined || (oldArgs zip lastUpdateCnt).find(x => x._1.eleCnt > x._2).isDefined){
          funImpls.update(name, (funcdecl, mps, nArgs.map(x => (x, x.eleCnt)), oldVs))
          if(!evalQueue.contains(name)){
            if(evalCnt.get(name).isEmpty){
              debug.log(s"first time encounter $name")
              updateFunction(name)
            }
            else{
              // val newA = (oldArgs zip nArgs).find(x => x._1.compare(x._2)).get
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
    val ctx = (funcdecl.params.map(_._2.name) zip args.unzip._1).toMap
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
      // debug.log(s"merging ${nVs.hashCode()%1000000} into ${x._4.hashCode()%1000000}")
      VariableValue.update(x._4, nVs)
      // debug.log(s"merged: ${x._4.hashCode()%1000000}")
      (nFuncDecl, x._2, x._3, x._4)
    }))
    // funImpls.get(name).get._4 += nVs
    // funImpls.update(name, funImpls.get(name).get.copy(_4 = nVs))
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

  def specializeClassCall(name: String, args: List[Expr])(using MonomorphContext): Option[Expr] =
    debug.trace("SPEC CALL", "class " + name + args.mkString(" with (", ", ", ")")) {
      // import TypeDeclKind._
      // tyImpls.get(name).flatMap { specClassMap => specClassMap.prototype match
      //   case Item.TypeDecl(Expr.Ref(name), Class, typeParams, params, parents, body) =>
      //     val (staticArguments, dynamicArguments) = partitationArguments(name, params, args)
      //     val (staticParameters, dynamicParameters) = params.partition(_._1)
      //     if (staticArguments.isEmpty) {
      //       None
      //     } else {
      //       val signature = generateSignature(staticArguments)
      //       val specClassDecl = specClassMap.getOrInsert(signature, {
      //         specClassMap.base = Item.TypeDecl(
      //           Expr.Ref(name), // name
      //           Class, // kind
      //           typeParams, // typeParams
      //           dynamicParameters, // params
      //           Nil, // parents
      //           Isolation.empty // body
      //         )
      //         val values = params.iterator.zip(args).flatMap({
      //           case ((true, Expr.Ref(name)), value) => Some((name, value))
      //           case ((false, _), _) => None
      //         })
      //         val typeImpl: Item.TypeDecl = Item.TypeDecl(
      //           Expr.Ref(s"${name}" + signature), // name
      //           Class, // kind
      //           typeParams, // typeParams
      //           dynamicParameters, // params
      //           (TypeName(name), dynamicParameters.map(_._2)) :: Nil, // parents
      //           specializeClass(specClassMap.prototype)(using Context(values)) // body
      //         )
      //         allTypeImpls += (typeImpl.name.name -> typeImpl)
      //         typeImpl
      //       })
      //       Some(Expr.Apply(specClassDecl.name, dynamicArguments))
      //     }
      //   case Item.TypeDecl(_, Trait, _, _, _, _) =>
      //     throw new MonomorphError(s"cannot specialize trait $name")
      //   case Item.TypeDecl(_, Alias, _, _, _, _) =>
      //     throw new MonomorphError(s"cannot specialize type alias $name")
      // }
      ???
    }(_.fold(Debug.noPostTrace)(identity))

  def specializeNew(name: String, args: List[BoundedExpr]): MonoValue = {
    if(allTypeImpls.contains(name)){
      val tp = allTypeImpls.get(name).get
      val ags = (tp.params.map(_._2.name) zip args)
      ObjectValue(name, MutMap(ags: _*))
    }
    else ???
  }

  def specializeSelect(obj: ObjectValue, field: String): MonoValue = {
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
        FunctionValue(nFuncName, prms.map(_._2.name), List("this" -> BoundedExpr(obj)))
      }
      else{
        ???
      }
    }
    else {
      ???
    }
  }

  // TODO: Remove `Option[Expr]` by passing the callee.
  def specializeFunctionCall(name: String, args: List[Expr])(using MonomorphContext): Option[Expr] =
    debug.trace("SPEC CALL", "function " + name + args.mkString(" with (", ", ", ")")) {
      // funImpls.get(name).flatMap { case (Item.FuncDecl(ref, params, body), impls) =>
      //   val (staticArguments, dynamicArguments) = partitationArguments(name, params, args)
      //   if (staticArguments.isEmpty) {
      //     None
      //   } else {
      //     val signature = generateSignature(staticArguments)
      //     val specFuncDecl = impls.get(signature).getOrElse[Item.FuncDecl] {
      //       val values = params.iterator.zip(args).flatMap({
      //         case ((true, Expr.Ref(name)), value) => Some((name, value))
      //         case ((false, _), _) => None
      //       })
      //       val specFuncBody = specializeExpr(body)(using Context(values))
      //       val staticParams = params.filter(!_._1)
      //       val specFuncName = s"${name}" + signature
      //       val funcDecl: Item.FuncDecl = Item.FuncDecl(specFuncName, staticParams, specFuncBody)
      //       impls.addOne((specFuncName, funcDecl))
      //       funcDecl
      //     }
      //     Some(Expr.Apply(specFuncDecl.name, dynamicArguments))
      //   }
      // }
      ???
    }(_.fold(Debug.noPostTrace)(identity))

  def specializeExpr(expr: Expr)(using ctx: Context, typeContext: MonomorphContext): Expr =
    debug.trace[Expr]("SPEC EXPR", expr, "in context", ctx) {
      // expr match
      //   case Expr.Ref(name) => ctx.get(name) match
      //     case Some(value) => value
      //     case None => expr
      //   case _: Expr.Lambda => expr
      //   case Expr.Apply(Expr.Apply(ident @ Expr.Ref(name), lhsExpr :: Nil), rhsExpr :: Nil)
      //       if Builtin.isBinaryOperator(name) =>
      //     val lhs = specializeExpr(lhsExpr)
      //     val rhs = specializeExpr(rhsExpr)
      //     Builtin.evalulateBinaryOperation(name, lhs, rhs)
      //       .getOrElse(Expr.Apply(Expr.Apply(ident, lhs :: Nil), rhs :: Nil))
      //   case Expr.Apply(callee, arguments) =>
      //     val specCallee = specializeExpr(callee)
      //     val specArgs = arguments.map(specializeExpr)
      //     specCallee match
      //       case Expr.Ref(name) => specializeCall(name, specArgs).getOrElse(expr)
      //       case Expr.Lambda(params, body) =>
      //         // Same as `specializeFuncDecl` but I should extract some common stuffs.
      //         ???
      //       case Expr.Select(receiver, Expr.Ref(fieldName)) =>
      //         infer(receiver, None) match
      //           case DataType.Class(declaration) => declaration.body.get(fieldName) match
      //             case Some(memberFuncDecl: Item.FuncDecl) =>
      //               // FIXME: the context should be from the class
      //               val specFuncDecl = specializeFunction(memberFuncDecl)
      //               val branches = ArrayBuffer[CaseBranch]()
      //               val alias: Expr.Ref = Expr.Ref("alpha") // alpha conversion needed
      //               branches += CaseBranch.Instance(
      //                 declaration.name,
      //                 alias,
      //                 Expr.Apply(Expr.Select(alias, specFuncDecl.name), specArgs)
      //               )
      //               Expr.Match(receiver, branches)
      //             case Some(memberFuncDefn: Item.FuncDefn) =>
      //               throw MonomorphError(s"class ${declaration.name.name}.$fieldName is not implemented")
      //             case None => throw MonomorphError(s"class ${declaration.name.name} does not have $fieldName")
      //           case other => throw MonomorphError(s"cannot select a non-class instance")
      //       case other => throw MonomorphError(s"not a callable: $other")
      //   case Expr.Tuple(elements) => Expr.Tuple(elements.map(specializeExpr))
      //   case Expr.Record(fields) => Expr.Record(fields.map {
      //     case (key, value) => (key, specializeExpr(value))
      //   })
      //   case Expr.Select(receiver, field) =>
      //     // We can do more.
      //     Expr.Select(specializeExpr(receiver), field)
      //   case Expr.LetIn(true, name, Expr.Lambda(params, body), cont) =>
      //     // Create a callable entry in the context and recursively specialize
      //     // the continuation.
      //     throw MonomorphError(s"recursive local functions are not implemented")
      //   case Expr.LetIn(true, _, _, _) =>
      //     throw MonomorphError(s"recursive non-function definition are not allowed")
      //   case Expr.LetIn(false, Expr.Ref(name), rhs, body) =>
      //     val specRhs = specializeExpr(rhs)
      //     specializeExpr(body)(using ctx + (name -> specRhs))
      //   case Expr.Block(items) =>
      //     val onlyExpressions = items.iterator.flatMap {
      //       case expr: Expr => Some(expr)
      //       case _ => None
      //     }
      //     onlyExpressions.map(specializeExpr).toList match
      //       case Nil => Expr.Literal(UnitValue.Undefined)
      //       case items => items.last
      //   case expr: Expr.Literal => expr
      //   case Expr.IfThenElse(condition, consequent, alternate) =>
      //     specializeExpr(
      //       if specializeExpr(condition).asBoolean()
      //       then consequent
      //       else alternate.getOrElse(Expr.Literal(UnitValue.Undefined))
      //     )
      //   case _ => throw MonomorphError(s"unimplemented ${expr.getClass()}")
      ???
    }(identity)

  /**
   * This function monomorphizes the given class with given arguments.
   * @return specialized class name and all included classes
   */
  def specializeTypeDef(
      name: String,
      args: List[Expr],
      body: Isolation
  ): Item.TypeDecl =
    debug.trace[Item.TypeDecl]("SPEC TDEF", name + args.mkString("(", ", ", ")") + " {\n" + body + "\n}") {
      tyImpls.get(name) match {
        case Some(classSpecMap) =>
          val Item.TypeDecl(_, kind, typeParams, params, parents, body) = classSpecMap.prototype
          val implClassName: Expr.Ref = Expr.Ref(s"${name}_${classSpecMap.size}")
          Item.TypeDecl(implClassName, kind, typeParams, params, parents, body)
          // FIXME: Logic here does not work.
        case None => throw new MonomorphError(s"cannot specialize undeclared type $name")
      }
    }(identity)

  def specializeFunction(funcProto: Item.FuncDecl)(using ctx: Context, typeContext: MonomorphContext): Item.FuncDecl =
    Item.FuncDecl(funcProto.name, funcProto.params, specializeExpr(funcProto.body))

  def specializeClass(classProto: Item.TypeDecl)(using ctx: Context, typeContext: MonomorphContext): Isolation =
    debug.trace("SPEC CLASS", s"class ${classProto.name.name}", "in value context", ctx) {
      Isolation(classProto.body.items.map {
        case expr: Expr => specializeExpr(expr)
        case funcDecl: Item.FuncDecl => specializeFunction(funcDecl)
        case other => throw MonomorphError(s"$other is not supported")
      })
    }(identity)

  def infer(expr: Expr, compatiableType: Option[DataType])(using context: MonomorphContext): DataType =
    debug.trace("INFER", expr.toString) {
      expr match
        case Expr.Ref(name) => context.get(name).getOrElse(DataType.Unknown)
        case other => super.infer(expr, compatiableType)
    }(_.toString)

  // Shorthand implicit conversions.

  // private given Conversion[String, Expr.Ref] with
  //   def apply(name: String): Expr.Ref = Expr.Ref(name)

  // private given Conversion[Var, Expr.Ref] with
  //   def apply(nme: Var): Expr.Ref = Expr.Ref(nme.name)

  // private given Conversion[TypeName, Expr.Ref] with
  //   def apply(nme: TypeName): Expr.Ref = Expr.Ref(nme.name)

  // private given Conversion[TypeDefKind, TypeDeclKind] with
  //   import mlscript.{Als, Cls, Trt}
  //   def apply(kind: TypeDefKind): TypeDeclKind = kind match
  //     case Als => TypeDeclKind.Alias
  //     case Cls => TypeDeclKind.Class
  //     case Trt => TypeDeclKind.Trait

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