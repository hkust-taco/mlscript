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
                 IfBody, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock, LetS, Statement}
import mlscript.UnitLit
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
import mlscript.compiler.Helpers.extractLamParams
import mlscript.compiler.Helpers.toTuple
import mlscript.compiler.mono.specializer.{MonoVal, TypeVal, ObjVal, FuncVal, LiteralVal, PrimVal, VarVal, TupVal, UnknownVal, BoundedTerm}
import mlscript.compiler.Helpers.extractFuncArgs

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
    Evaluate a Term given an evaluation Context and populate its EvaledTerm
  */
  val builtInOps: Set[String] = Set("+", "-", ">", "<", "*", "==", "concat", "toString") 
  def nuEvaluate(term: Term)(using evalCtx: Map[String, BoundedTerm], callingStack: List[String], termMap: MutMap[Term, BoundedTerm]): Unit =
    def getRes(term: Term): BoundedTerm = termMap.getOrElse(term, throw MonomorphError(s"Bounds for ${term} not found."))
    debug.writeLine(s"╓Eval ${term}:")
    debug.indent()
    term match
      case lit: Lit => 
        termMap.addOne(term, BoundedTerm(LiteralVal(lit)))
        term
      case Var(name) => 
        debug.writeLine(s"evalCtx: ${evalCtx}")
        termMap.addOne(term, 
          if name == "true"
          then BoundedTerm(LiteralVal(true))
          else if name == "false"
          then BoundedTerm(LiteralVal(false))
          else evalCtx.getOrElse(name, monoer.nuFindVar(name)))
        term
      // case Lam(lhs, rhs) => throw MonomorphError("Should not encounter lambda during evaluation process")
      case App(lhs@Var(name), rhs) if builtInOps.contains(name) => 
        nuEvaluate(rhs)
        termMap.addOne(term, extractFuncArgs(rhs).map(getRes).fold(BoundedTerm())(_ ++ _))
      case App(lhs, rhs) => 
        nuEvaluate(lhs)
        nuEvaluate(rhs)
        termMap.addOne(term, getRes(lhs).getValue.map{ 
          case FuncVal(name, prm, ctx) =>
              debug.writeLine(s"Apply Function ${name}") 
              monoer.nuGetFuncRetVal(name, Some(ctx.unzip._2 ++ extractFuncArgs(rhs).map(getRes)))
          case o: ObjVal => monoer.nuGetFieldVal(o, "apply").asValue match
            case Some(FuncVal(name, prm, ctx)) => 
              monoer.nuGetFuncRetVal(name, Some(ctx.unzip._2 ++ extractFuncArgs(rhs).map(getRes))) // Unzipping ctx gives implicit "this"
            case other => throw MonomorphError(s"Encountered unknown value ${other} when evaluating object application")
          case TypeVal(name) => 
            BoundedTerm(monoer.nuCreateObjValue(name, extractFuncArgs(rhs).map(getRes).toList))
          case l@LiteralVal(i) => BoundedTerm(l)
        }.fold(BoundedTerm())(_ ++ _))
      case New(Some((constructor, args)), body) => 
        nuEvaluate(args)
        termMap.addOne(term, BoundedTerm(monoer.nuCreateObjValue(constructor.base.name, extractFuncArgs(args).map(getRes))))
      case Sel(receiver, fieldName) => 
        nuEvaluate(receiver)
        termMap.addOne(term, getRes(receiver).getValue.map{
          case obj: ObjVal => 
            obj.fields.get(fieldName.name) match
              case Some(fld) => 
                debug.writeLine("direct select")
                fld
              case None => 
                debug.writeLine("other select")
                debug.indent()
                val res = monoer.nuGetFieldVal(obj, fieldName.name).getValue.map {
                  case f@FuncVal(name, None, ctx) => 
                    debug.writeLine(s"got paramless func ${f}")
                    monoer.nuGetFuncRetVal(name, Some(ctx.unzip._2))
                  case other => BoundedTerm(other)
                }.fold(BoundedTerm())(_ ++ _)
                debug.outdent()
                res
          case tup: TupVal =>
            tup.fields.get(fieldName) match
              case Some(fld) => fld
              case None => throw MonomorphError(s"Invalid selction ${fieldName} from Tuple")
          // case func: FuncVal =>
          //   monoer.nuGetFuncRetVal(func.name, None)
          case other => throw MonomorphError(s"Cannot select from non-object value ${other}")
        }.fold(BoundedTerm())(_ ++ _))
      case Let(rec, Var(name), rhs, body) =>
        if !rec
        then 
          nuEvaluate(rhs)
          nuEvaluate(body)(using evalCtx + (name -> getRes(rhs)))
          termMap.addOne(term, getRes(body))
        else ??? //TODO: letrec
      case Blk(stmts) => 
        stmts.map{
          case t: Term => nuEvaluate(t)
          case other => throw MonomorphError(s"Encountered unlifted non-term ${other} in block ")
        }
        termMap.addOne(term, {
          if stmts.length == 0 
          then BoundedTerm(LiteralVal(UnitLit(false)))
          else stmts.reverse.head match 
            case t: Term => getRes(t)
        })
      case If(body, alternate) => 
        val res = body match
          case IfThen(condition, consequent) => 
            nuEvaluate(consequent)
            alternate.map(alt => nuEvaluate(alt))
            nuEvaluate(condition)
            termMap.addOne(term, getRes(condition).asValue match {
              // TODO: redundant branch elimination
              // case Some(x: LiteralVal) if x.asBoolean().isDefined =>
              //   if x.asBoolean().get
              //   then nuConsequent.evaledTerm
              //   else nuAlternate.map(_.evaledTerm).getOrElse(BoundedTerm(UnknownVal()))
              case _ => getRes(consequent) ++ alternate.map(getRes).getOrElse(BoundedTerm(UnknownVal()))
            })
          case other => throw MonomorphError(s"IfBody ${body} not handled")
        res
      case Asc(term, ty) => 
        nuEvaluate(term)
        termMap.addOne(term, getRes(term))
      case Tup(fields) => // TODO: give evaledTerm?
        fields.map{
          case (name, Fld(flags, value)) => nuEvaluate(value)
        }
        termMap.addOne(term, BoundedTerm(monoer.createTupVal(fields.map{case (name, Fld(flags, value)) => getRes(value)})))
      // case Bra(rcd, term) => ???
      // case _: Bind => ???
      // case _: Test => ???
      // case With(term, Rcd(fields)) => ???
      // case CaseOf(term, cases) => ???     
      // case Subs(array, index) => ???
      // case Assign(lhs, rhs) => ???
      // case New(None, body) => ???
      // case Rcd(fields) => ???
    debug.outdent()
    debug.writeLine(s"╙Result ${getRes(term).getValue.map(_.toString).toList}:")

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

  def nuDefunctionalize(term: Term)(using termMap: MutMap[Term, BoundedTerm]): Term = {
    def getRes(term: Term): BoundedTerm = termMap.getOrElse(term, throw MonomorphError(s"Bounds for ${term} not found."))
    // TODO: Change to use basic pattern match instead of UCS
    def valSetToBranches(vals: List[MonoVal], acc: List[Either[IfBody,Statement]] = List(Left(IfElse(Var("error")))))(using field: Var, args: Option[List[Term]]): List[Either[IfBody,Statement]] = 
      debug.writeLine(s"Expanding ${vals}")
      vals match
      case Nil => acc
      case head :: next => head match
        case o@ObjVal(name, params, fields) =>
          val selValue = monoer.nuGetFieldVal(o, field.name)
          debug.writeLine(s"selected value: ${selValue.asValue}")
          val branchCase = selValue.asValue match {
            case Some(f: FuncVal) =>
              IfThen(Var(name), App(Var(f.name), toTuple(Var("obj") :: args.getOrElse(Nil))))
            case Some(o@ObjVal(subName, subParams, subFields)) => 
              args match
                case Some(a) => //FIXME: Unverified
                  val scrut = Sel(Var("obj"), field)
                  val branches = selValue.getValue.toList.map(_.asInstanceOf[ObjVal])
                    .flatMap(o => {
                      val lambdaMemFunc = monoer.nuGetFieldVal(o, "apply").asValue.get.asInstanceOf[FuncVal]
                      val caseVarNm: Var = Var(s"obj$$${o.name}")
                      Right(NuFunDef(Some(false), Var("obj"), None, Nil, Left(Var(o.name)))(None, None, None, None, false)) :: 
                        List[Either[IfBody,Statement]](Left(IfThen(Var(o.name), App(Var(lambdaMemFunc.name), toTuple(caseVarNm :: a)))))
                    })
                  IfOpApp(scrut, Var("is"), IfBlock(branches))
                case None => 
                  //throw MonomorphError("Hey")
                  IfThen(App(Var(name), toTuple(params.map(k => Var(k)).toList)), field)
            case Some(LiteralVal(v)) =>
              IfThen(Var(name), v match
                case lit: Lit => lit
                case bool: Boolean => if bool then Var("true") else Var("false"))
            case None =>
              if selValue.getValue.size > 1 
              then 
                IfThen(App(Var(name), toTuple(params.map(k => Var(k)).toList)), field)
              else throw MonomorphError(s"Selection of field ${field} from object ${o} results in no values")
          }
          valSetToBranches(next, Left(branchCase) :: acc)
        // case t@TupVal(fields) =>
        //   val selValue = fields.getOrElse(field, throw MonomorphError(s"Invalid field selection ${field} from Tuple"))


    val ret = term match
      case x: (Lit | Var) => x
      case App(sel@Sel(receiver, field), args) => 
        debug.writeLine(s"Specializing ${term}")
        debug.indent()
        val nuReceiver = nuDefunctionalize(receiver)
        val nuArgs = nuDefunctionalize(args)
        val ifBlockLines = valSetToBranches(getRes(receiver).getValue.toList)(using field, Some(extractFuncArgs(nuArgs)))
        val ifBlk = IfBlock(ifBlockLines)
        val res = Let(false, Var("obj"), nuReceiver,
            If(IfOpApp(Var("obj"), Var("is"), ifBlk), None))
        debug.writeLine(s"Result: ${res}")
        debug.outdent()
        res
      case App(op@Var(name), args) if builtInOps.contains(name) =>
          App(op, nuDefunctionalize(args))
      case App(callee, args) => 
        if(getRes(callee).getValue.find(_.isInstanceOf[ObjVal]).isDefined)
          nuDefunctionalize(App(Sel(callee, Var("apply")), args))
        else 
          App(nuDefunctionalize(callee), nuDefunctionalize(args))
      case Tup(fields) => Tup(fields.map{
        case (name, Fld(flags, value)) => (name, Fld(flags, nuDefunctionalize(value)))})
      case If(IfThen(expr, rhs), els) => If(IfThen(nuDefunctionalize(expr), nuDefunctionalize(rhs)), els.map(nuDefunctionalize))
      case New(Some((constructor, args)), body) => New(Some((constructor, nuDefunctionalize(args))), body)
      case Sel(receiver, fieldName) => 
        val nuReceiver = nuDefunctionalize(receiver)
        if (getRes(receiver).getValue.forall(_.isInstanceOf[ObjVal]))
        then
          debug.writeLine(s"Specializing ${term}")
          debug.indent()
          val ifBlockLines = valSetToBranches(getRes(receiver).getValue.toList)(using fieldName, None)
          val ifBlk = IfBlock(ifBlockLines)
          val res = Let(false, Var("obj"), nuReceiver,
            If(IfOpApp(Var("obj"), Var("is"), ifBlk), None)
          )
          debug.writeLine(s"Result: ${res}")
          debug.outdent()
          res
        else 
          Sel(nuReceiver, fieldName)
      case Blk(stmts) => 
        Blk(stmts.map{
          case t: Term => nuDefunctionalize(t)
          case other => other
        })
      case _ => throw MonomorphError(s"Cannot Defunctionalize ${term}")
    ret
  }
}
