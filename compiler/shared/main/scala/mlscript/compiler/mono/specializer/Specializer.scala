package mlscript.compiler.mono.specializer

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map as MutMap
import mlscript.compiler.debug.Debug
import mlscript.compiler.mono.MonomorphError
import mlscript.compiler.mono.Monomorph
import mlscript.compiler.UnitValue
import mlscript.compiler.UnitValue.{Null, Undefined}
import mlscript.TypeName
import mlscript.compiler.Item
import mlscript.compiler.CaseBranch
import mlscript.compiler.Expr
import mlscript.{App, Asc, Assign, Bind, Blk, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, FldFlags, If, PolyType, 
                 IfBody, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.UnitLit
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.compiler.mono.MonomorphError
import mlscript.NuTypeDef
import mlscript.NuFunDef
import scala.collection.mutable.ArrayBuffer
import mlscript.CaseBranches
import mlscript.Case
import mlscript.SimpleTerm
import mlscript.NoCases
import mlscript.Wildcard
import mlscript.DecLit
import mlscript.IntLit
import mlscript.StrLit
import mlscript.AppliedType
import mlscript.TypeName
import mlscript.TypeDefKind
import mlscript.compiler.mono.Monomorph
import mlscript.NuDecl
import mlscript.TypingUnit
import mlscript.compiler.Helpers.extractParams

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
        else throw MonomorphError(s"Malformed Expr: ${rawExpr}")

      case other@Expr.Apply(callee, arguments) => 
        val calE = evaluate(callee)
        val cal = calE.expValue
        val nArgs = arguments.map(evaluate)
        val args = nArgs.map(_.expValue)
        val retV = cal.getValue.map{
          case FunctionValue(name, prm, ctxArg) => 
            val callResult = monoer.getFuncRetVal(name, ctxArg.unzip._2 ++ args)
            // debug.log(s"call result: $callResult")
            callResult
          case o: ObjectValue => 
            val sel = monoer.getFieldVal(o, "apply")
            sel.asValue match
              case Some(FunctionValue(name, prm, ctx)) => 
                val callResult = monoer.getFuncRetVal(name, ctx.unzip._2 ++ args)
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
            monoer.getFieldVal(obj, field.name)
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
        val retV = BoundedExpr(monoer.createObjValue(apply.name, args))
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
        throw MonomorphError(s"Unhandled case: ${rawExpr}")

      case Expr.Isolated(isolation) => throw MonomorphError(s"Unhandled case: ${rawExpr}")

      case Expr.Tuple(fields) => 
        if(fields.length == 1){
          evaluate(fields.head)
        }
        else
          throw MonomorphError(s"Unhandled case: ${rawExpr}")
      case Expr.Record(fields) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
      case Expr.LetIn(true, name, rhs, body) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
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

      case Expr.As(value, toType) => 
        val retV = evaluate(value)
        rawExpr.expValue = retV.expValue
        rawExpr
      case Expr.Assign(assignee, value) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
      case Expr.With(value, fields) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
      case Expr.Subscript(receiver, index) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
      case Expr.Match(scrutinee, branches) => throw MonomorphError(s"Unhandled case: ${rawExpr}")
    }
  // }(_.expValue)
  
  /*
    Evaluate a Term given an evaluation Context and return a BoundedExpr
  */
  def nuEvaluate(term: Term)(using evalCtx: Map[String, BoundedExpr], callingStack: List[String]): BoundedExpr =
    term match
      case IntLit(value) => BoundedExpr(LiteralValue(value))
      case DecLit(value) => BoundedExpr(LiteralValue(value))
      case StrLit(value) => BoundedExpr(LiteralValue(value))
      case UnitLit(value) => BoundedExpr(LiteralValue(if value then Undefined else Null))
      case Var(name) => 
        evalCtx.getOrElse(name, BoundedExpr(monoer.nuFindVar(name)))
      case Lam(lhs, rhs) => throw MonomorphError("Should not encounter lambda during evaluation process")
      case App(lhs, rhs) => 
        BoundedExpr(nuEvaluate(lhs).getValue.map{
          case FunctionValue(name, params, ctx) => ???
          case ObjectValue(name, fields) => ???
          case TypeValue(name) => 
            monoer.nuCreateObjValue(name, extractParams(rhs).map((flags, nm, tp) => nuEvaluate(nm)).toList)
        })
      case New(Some((constructor, args)), _) => ???
      case New(None, body) => ???
      case Tup(fields) => ???
      case Rcd(fields) => ???
      case Sel(receiver, fieldName) => ???
      case Let(rec, Var(name), rhs, body) => ???
      case Blk(stmts) => ???
      case Bra(rcd, term) => ???
      case Asc(term, ty) => ???
      case _: Bind => ???
      case _: Test => ???
      case With(term, Rcd(fields)) => ???
      case CaseOf(term, cases) => ???     
      case Subs(array, index) => ???
      case Assign(lhs, rhs) => ???
      case If(body, alternate) => ??? 

  def defunctionalize(rawExpr: Expr): Expr = {
    val ret: Expr = rawExpr match {
      case _: (Expr.Ref | Expr.Literal) => rawExpr
      case Expr.Apply(sel@Expr.Select(receiver, field), args) => 
        val nRec = defunctionalize(receiver)
        val nArgs = args.map(defunctionalize)
        val branches = ArrayBuffer[CaseBranch]()
        receiver.expValue.getValue.foreach{
          case o@ObjectValue(name, _) => 
            val selValue = monoer.getFieldVal(o, field.name)
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
                    val lambdaMemFunc = monoer.getFieldVal(o, "apply").asValue.get.asInstanceOf[FunctionValue]
                    val caseVarNm: Expr.Ref = Expr.Ref(s"obj$$${o.name}")
                    CaseBranch.Instance(Expr.Ref(o.name), caseVarNm, 
                      Expr.Apply(Expr.Ref(lambdaMemFunc.name), caseVarNm :: nArgs))
                  })
                Expr.Match(scrut, ArrayBuffer(brchs: _*))
              case _ => throw MonomorphError(s"Unhandled case: ${rawExpr}")

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
      case Expr.As(value, toType) => Expr.As(defunctionalize(value), toType)
      case _ => throw MonomorphError(s"Unhandled case: ${rawExpr}")
    }
    ret.expValue = rawExpr.expValue
    ret
  }
}
