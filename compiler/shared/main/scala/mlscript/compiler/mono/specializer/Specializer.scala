package mlscript.compiler.mono.specializer

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map as MutMap
import mlscript.compiler.debug.Debug
import mlscript.compiler.mono.MonomorphError
import mlscript.compiler.mono.Monomorph
import mlscript.TypeName
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

  /*
    Evaluate a Term given an evaluation Context and populate its EvaledTerm
  */
  val builtInOps: Set[String] = Set("+", "-", ">", "<", "*", "==", "concat", "toString", "log") 
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
      case Asc(t, ty) => 
        nuEvaluate(t)
        termMap.addOne(term, getRes(t))
      case Tup(fields) => // TODO: give evaledTerm?
        fields.map{
          case (name, Fld(flags, value)) => nuEvaluate(value)
        }
        termMap.addOne(term, BoundedTerm(monoer.createTupVal(fields.map{case (name, Fld(flags, value)) => getRes(value)})))
      case Bra(rcd, t) => 
        nuEvaluate(t)
        termMap.addOne(term, getRes(t))
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
      case Bra(false, term) => Bra(false, nuDefunctionalize(term))
      case _ => throw MonomorphError(s"Cannot Defunctionalize ${term}")
    ret
  }
}
