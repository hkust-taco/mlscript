package mlscript.compiler.mono.specializer

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map as MutMap
import mlscript.compiler.debug.Debug
import mlscript.compiler.mono.MonomorphError
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.UnitValue
import mlscript.TypeName
import mlscript.compiler.Item
import mlscript.compiler.CaseBranch
import mlscript.compiler.Expr

class Specializer(monoer: Monomorph)(using debug: Debug){

  // def evaluateFunction(callee: MonoValue, arguments: List[MonoValue])(using evalCtx: Context, callingStack: List[String], typeCtx: Map[String, Item.TypeDecl], funcCtx: Map[String, Item.FuncDecl]): BoundedExpr = {
  // 	debug.trace[BoundedExpr]("FUNC ", callee.toString() + arguments.mkString("(", ", ", ")")) {
  // 		callee match
  // 			case LiteralValue(s: String) if Builtin.isBinaryOperator(s) && arguments.length == 2 =>
  // 				val retValue = Builtin.evaluateBinaryOpValue(s, arguments.head, arguments.tail.head)
  // 				if(retValue.isDefined){
  // 					BoundedExpr(retValue.get)
  // 				}
  // 				else BoundedExpr(UnknownValue())
  // 			case FunctionValue(name, body, prm, thisCtx) => 
  // 				val argCtx = Context.toCtx(prm.zip(arguments))
  // 				val ret = evaluate(body)(using evalCtx ++ Context.toCtx(thisCtx) ++ argCtx, name :: callingStack)
  // 				ret._2
  // 			case _ => BoundedExpr(UnknownValue())
  // 	}(identity)
  // }

  // def evaluateConstructor(tpName: TypeName, arguments: List[MonoValue])(using evalCtx: Context, typeCtx: Map[String, Item.TypeDecl], funcCtx: Map[String, Item.FuncDecl]): BoundedExpr = 
  // 	debug.trace[BoundedExpr]("NEW ", tpName.toString() + arguments.mkString("(", ", ", ")")){
  // 	val Item.TypeDecl(name, kind, typeParams, params, parents, body) = typeCtx.get(tpName.name).get
  // 	val plainPrm = params.map(_._2.name)
  // 	val objValue: ObjectValue = ObjectValue(tpName.name, 
  // 		(plainPrm.zip(arguments.map(_.toBoundedExpr)) ++ body.items.flatMap{
  // 			case f@Item.FuncDecl(nm, prm, bd) => 
  // 				Some(nm.name -> funcDecl2Val(f).toBoundedExpr)
  // 			case _ => None
  // 		}).toMap)
  // 	objValue.fields.foreach{
  // 		case (nm, v: FunctionValue) if !plainPrm.contains(nm) => v.ctx.addOne("this" -> objValue.toBoundedExpr)
  // 		case _ => ()
  // 	}
  // 	BoundedExpr(objValue)
  // }(identity)

  // def funcDecl2Val(fd: Item.FuncDecl)(using evalCtx: Context): FunctionValue = {
  //   FunctionValue(fd.name.name, fd.body, fd.params.map(_._2.name), MutMap())
  // }

  def evaluate(rawExpr: Expr)(using evalCtx: Context, callingStack: List[String]): Expr = 
    // debug.trace[Expr]("EVAL ", rawExpr.toString()) {
    rawExpr match{
      case Expr.Ref(name) => 
        rawExpr.expValue = evalCtx.get(name)
        rawExpr
      case Expr.Apply(Expr.Apply(opE@Expr.Ref(op), a1), a2) if Builtin.isBinaryOperator(op) =>
        if(a1.length == 1 && a2.length == 1)
        {
          val a1E = evaluate(a1.head)
          val a2E = evaluate(a2.head)
          val pairedAV = (a1E.expValue.asValue, a2E.expValue.asValue) match {
            case (Some(i1: LiteralValue), Some(i2: LiteralValue)) =>
              Builtin.evaluateBinaryOpValue(op, i1, i2) match{
                case Some(value) => value
                case None => PrimitiveValue()
              }
            case _ => PrimitiveValue()
          }
          val retExp = Expr.Apply(Expr.Apply(opE, List(a1E)), List(a2E))
          retExp.expValue = BoundedExpr(pairedAV)
          retExp
        }
        else ???
      
      case Expr.Apply(nm@Expr.Ref(name), arguments) =>
        val nArgs = arguments.map(evaluate(_))
        val args = nArgs.map(_.expValue)
        val retVal = monoer.monomorphizeCall(name, args)
        val retExp = Expr.Apply(nm, nArgs)
        retExp.expValue = retVal
        retExp

      case other@Expr.Apply(callee, arguments) => 
        val calE = evaluate(callee)
        val nArgs = arguments.map(evaluate)
        val args = nArgs.map(_.expValue)
        val cal = calE.expValue
        val retV = cal.values.map{
          case FunctionValue(name, prm, ctxArg) => 
            monoer.monomorphizeCall(name, ctxArg.unzip._2 ++ args)
          case _ => BoundedExpr(UnknownValue())
        }.fold(BoundedExpr())(_ ++ _)
        val retExp = Expr.Apply(calE, nArgs)
        retExp.expValue = retV
        retExp

      case Expr.Select(receiver, field) => 
        val rec = evaluate(receiver)
        val retV = rec.expValue.values.map{
          case ObjectValue(_, flds) if flds.contains(field.name) =>
            flds.get(field.name).get 
          case obj: ObjectValue => 
            BoundedExpr(monoer.specializeSelect(obj, field.name))
          case _ => 
            BoundedExpr(UnknownValue())
        }.fold(BoundedExpr())(_ ++ _)
        val retExp = Expr.Select(rec, field)
        retExp.expValue = retV
        retExp

      case Expr.LetIn(false, name, rhs, body) => 
        val nRhs = evaluate(rhs)
        val nCtx = evalCtx + (name.name -> nRhs.expValue)
        val nBody = evaluate(body)(using nCtx)
        val retExp = Expr.LetIn(false, name, nRhs, nBody)
        retExp.expValue = body.expValue
        retExp

      case l@Expr.Literal(value) => 
        l.expValue = BoundedExpr(LiteralValue(value))
        l

      case Expr.New(apply, arguments) => 
        val nArgs = arguments.map(evaluate(_))
        val args = nArgs.map(_.expValue)
        val retV = BoundedExpr(monoer.specializeNew(apply.name, args))
        val retExp = Expr.New(apply, nArgs)
        retExp.expValue = retV
        retExp

      case Expr.IfThenElse(condition, consequent, Some(alternate)) => 
        val nCond = evaluate(condition)
        val nCons = evaluate(consequent)
        val nAlter = evaluate(alternate)
        val retV = nCond.expValue.asValue match {
          case Some(x: LiteralValue) if x.asBoolean().isDefined => 
            if(x.asBoolean().get){
              nCons.expValue
            }
            else {
              nAlter.expValue
            }
          case _ => 
            nCons.expValue ++ nAlter.expValue
        }
        val retExp = Expr.IfThenElse(nCond, nCons, Some(nAlter))
        retExp.expValue = retV
        retExp
      case Expr.IfThenElse(condition, consequent, None) =>
        val nCond = evaluate(condition)
        val nCons = evaluate(consequent)
        val retExp = Expr.IfThenElse(nCond, nCons, None)
        retExp.expValue = BoundedExpr(LiteralValue(UnitValue.Undefined))
        retExp

      case self@Expr.Lambda(prm, body) => 
        ???

      case Expr.Isolated(isolation) => ???

      case Expr.Tuple(fields) => 
        if(fields.length == 1){
          evaluate(fields.head)
        }
        else
          ???
      case Expr.Record(fields) => ???
      case Expr.LetIn(true, name, rhs, body) => ???
      case Expr.Block(items) => 
        val exps = items.flatMap{
          case e: Expr => Some(evaluate(e))
          case _ => None
        }
        if(exps.length == 0){
          val retE = Expr.Literal(UnitValue.Undefined)
          val retV = BoundedExpr(LiteralValue(UnitValue.Undefined))
          retE.expValue = retV
          retE
        }
        else if(exps.length == 1){
          exps.head
        }
        else {
          val retV = exps.reverse.head.expValue
          val retE = Expr.Block(exps)
          retE.expValue = retV
          retE
        }

      case Expr.As(value, toType) => ???
      case Expr.Assign(assignee, value) => ???
      case Expr.With(value, fields) => ???
      case Expr.Subscript(receiver, index) => ???
      case Expr.Match(scrutinee, branches) => ???
    }
  // }(_.expValue)

  def defunctionalize(rawExpr: Expr): Expr = {
    val ret: Expr = rawExpr match {
      case _: (Expr.Ref | Expr.Literal) => rawExpr
      case Expr.Apply(sel@Expr.Select(receiver, field), args) => 
        val nRec = defunctionalize(receiver)
        val nArgs = args.map(defunctionalize)
        val branches = ArrayBuffer[CaseBranch]()
        receiver.expValue.values.foreach{
          case ObjectValue(name, _) => 
            branches.addOne(CaseBranch.Instance(Expr.Ref(name), Expr.Ref("obj"), Expr.Apply(Expr.Ref(s"$field$$$name"), Expr.Ref("obj") :: nArgs)))
          case _ => ()
        }
        Expr.Match(nRec, branches)
      case Expr.Apply(callee, arguments) => Expr.Apply(defunctionalize(callee), arguments.map(defunctionalize))
      case Expr.New(typeName, args) => Expr.New(typeName, args.map(defunctionalize))
      case Expr.Tuple(fields) => Expr.Tuple(fields.map(defunctionalize))
      case Expr.LetIn(isRec, name, rhs, body) => Expr.LetIn(isRec, name, defunctionalize(rhs), defunctionalize(body))
      case Expr.IfThenElse(condition, consequent, alternate) => Expr.IfThenElse(defunctionalize(condition), defunctionalize(consequent), alternate.map(defunctionalize))
      case Expr.Block(items) => Expr.Block(items.map{
        case e: Expr => defunctionalize(e)
        case other => other
      })
      case Expr.Select(receiver, field) => Expr.Select(defunctionalize(receiver), field)
      case _ => ???
    }
    ret.expValue = rawExpr.expValue
    ret
  }
  // def updateResult(rawExpr: Expr)(using evalCtx: Context, callingStack: List[String], diff: Map[String, BoundedExpr]): Option[BoundedExpr] = {
  // 	if(rawExpr.freeVars.intersect(diff.keySet).isEmpty){
  // 		None
  // 	}
  // 	else {
  // 		rawExpr match
  // 			case Expr.Ref(name) => diff.get(name)
  // 			case Expr.Apply(callee, arguments) => 

  // 			case Expr.Tuple(fields) =>
  // 			case Expr.Record(fields) =>
  // 			case Expr.Select(receiver, field) =>
  // 			case Expr.LetIn(isRec, name, rhs, body) =>
  // 			case Expr.Block(items) =>
  // 			case Expr.As(value, toType) =>
  // 			case Expr.Assign(assignee, value) =>
  // 			case Expr.With(value, fields) =>
  // 			case Expr.Subscript(receiver, index) =>
  // 			case Expr.Match(scrutinee, branches) =>
  // 			case Expr.Literal(value) =>
  // 			case Expr.New(typeName, args) =>
  // 			case Expr.IfThenElse(condition, consequent, alternate) =>
  // 			case Expr.Isolated(isolation) =>
  // 			case Expr.Lambda(params, body) => ???	
  // 	}
  // }
}
