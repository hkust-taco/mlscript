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

  def evaluate(rawExpr: Expr)(using evalCtx: Context, callingStack: List[String]): Expr = 
    // debug.trace[Expr]("EVAL ", rawExpr.toString()) {
    rawExpr match{
      case Expr.Ref(name) => 
        rawExpr.expValue = 
          if evalCtx.contains(name) then evalCtx.get(name) else BoundedExpr(monoer.findVar(name))
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

      case other@Expr.Apply(callee, arguments) => 
        val calE = evaluate(callee)
        val cal = calE.expValue
        val nArgs = arguments.map(evaluate)
        val args = nArgs.map(_.expValue)
        val retV = cal.getValue.map{
          case FunctionValue(name, prm, ctxArg) => 
            val callResult = monoer.monomorphizeCall(name, ctxArg.unzip._2 ++ args)
            // debug.log(s"call result: $callResult")
            callResult
          case o: ObjectValue => 
            val sel = monoer.specializeSelect(o, "apply")
            sel.asValue match
              case Some(FunctionValue(name, prm, ctx)) => 
                val callResult = monoer.monomorphizeCall(name, ctx.unzip._2 ++ args)
                // debug.log(s"call result: $callResult")
                callResult
              case _ => BoundedExpr(UnknownValue())
          case _ => BoundedExpr(UnknownValue())
        }.fold(BoundedExpr())((x, y) => {
          // debug.log(s"merging $x with $y")
          val xy = x ++ y
          // debug.log(s"result $xy")
          xy
        })
        val retExp = Expr.Apply(calE, nArgs)
        retExp.expValue = retV
        retExp

      case Expr.Select(receiver, field) => 
        val rec = evaluate(receiver)
        val retV = rec.expValue.getValue.map{
          case ObjectValue(_, flds) if flds.contains(field.name) =>
            flds.get(field.name).get 
          case obj: ObjectValue => 
            monoer.specializeSelect(obj, field.name)
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
        receiver.expValue.getValue.foreach{
          case o@ObjectValue(name, _) => 
            val selValue = monoer.specializeSelect(o, field.name)
            val branchExp = selValue.asValue match{
              // foo.f is a member function
              case Some(f: FunctionValue) =>
                Expr.Apply(Expr.Ref(f.name), Expr.Ref("obj") :: nArgs)
              // foo.f is (many candidate) lambda(Object)
              case _ if selValue.getValue.forall(_.isInstanceOf[ObjectValue]) =>
                // foo.f match ...
                val scrut = Expr.Select(Expr.Ref("obj"), field)
                val brchs = selValue.getValue.toList.map(_.asInstanceOf[ObjectValue])
                  .map(o => {
                    val lambdaMemFunc = monoer.specializeSelect(o, "apply").asValue.get.asInstanceOf[FunctionValue]
                    val caseVarNm: Expr.Ref = Expr.Ref(s"obj$$${o.name}")
                    CaseBranch.Instance(Expr.Ref(o.name), caseVarNm, 
                      Expr.Apply(Expr.Ref(lambdaMemFunc.name), caseVarNm :: nArgs))
                  })
                Expr.Match(scrut, ArrayBuffer(brchs: _*))
              case _ => ???

            }
            branches.addOne(CaseBranch.Instance(Expr.Ref(name), Expr.Ref("obj"), branchExp))
          case _ => ()
        }
        Expr.Match(nRec, branches)
      case Expr.Apply(callee, arguments) => 
        if(callee.expValue.getValue.find(_.isInstanceOf[ObjectValue]).isDefined)
          defunctionalize(Expr.Apply(Expr.Select(callee, Expr.Ref("apply")), arguments))
        else
          Expr.Apply(defunctionalize(callee), arguments.map(defunctionalize))
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
}
