package mlscript
package compiler
package mono

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.ArrayBuffer
import mlscript.compiler.Helpers.*
class Specializer(monoer: Monomorph)(using debug: Debug){

  /*
    Evaluate a Term given an evaluation Context and update its result in the term map
  */
  val builtInOps: Set[String] = Set("+", "-", ">", "<", "*", "==", "concat", "toString", "log") 
  def evaluate(term: Term)(using evalCtx: Map[String, BoundedTerm], callingStack: List[String], termMap: MutMap[Term, BoundedTerm]): Unit =
    def getRes(term: Term): BoundedTerm = termMap.getOrElse(term, throw MonomorphError(s"Bounds for ${term} not found during eval."))
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
          else evalCtx.getOrElse(name, monoer.findVar(name)))
        term
      // case Lam(lhs, rhs) => throw MonomorphError("Should not encounter lambda during evaluation process")
      case App(lhs@Var(name), rhs) if builtInOps.contains(name) => 
        evaluate(rhs)
        termMap.addOne(term, extractFuncArgs(rhs).map(getRes).fold(BoundedTerm())(_ ++ _))
      case App(lhs@NuNew(cls), args) =>
        (cls, args) match {
          case (v: Var, args: Tup) =>
            evaluate(args)
            termMap.addOne(term, BoundedTerm(monoer.createObjValue(v.name, extractFuncArgs(args).map(getRes))))
          case _ => ???
        }
      case App(lhs, rhs) => 
        evaluate(lhs)
        evaluate(rhs)
        termMap.addOne(term, getRes(lhs).getValue.map{ 
          case FuncVal(name, prm, ctx) =>
              debug.writeLine(s"Apply Function ${name}") 
              monoer.getFuncRetVal(name, Some(ctx.unzip._2 ++ extractFuncArgs(rhs).map(getRes)))
          case o: ObjVal => monoer.getFieldVal(o, "apply").asValue match
            case Some(FuncVal(name, prm, ctx)) => 
              monoer.getFuncRetVal(name, Some(ctx.unzip._2 ++ extractFuncArgs(rhs).map(getRes))) // Unzipping ctx gives implicit "this"
            case other => throw MonomorphError(s"Encountered unknown value ${other} when evaluating object application")
          case TypeVal(name) => 
            BoundedTerm(monoer.createObjValue(name, extractFuncArgs(rhs).map(getRes).toList))
          case l@LiteralVal(i) => BoundedTerm(l)
          case _ => utils.die
        }.fold(BoundedTerm())(_ ++ _))
      case New(Some((constructor, args)), body) => 
        evaluate(args)
        termMap.addOne(term, BoundedTerm(monoer.createObjValue(constructor.base.name, extractFuncArgs(args).map(getRes))))
      case Sel(receiver, fieldName) => 
        evaluate(receiver)
        termMap.addOne(term, getRes(receiver).getValue.map{
          case obj: ObjVal => 
            obj.fields.get(fieldName.name) match
              case Some(fld) => 
                debug.writeLine("direct select")
                fld
              case None => 
                debug.writeLine("other select")
                debug.indent()
                val res = monoer.getFieldVal(obj, fieldName.name).getValue.map {
                  case f@FuncVal(name, None, ctx) => 
                    debug.writeLine(s"got paramless func ${f}")
                    monoer.getFuncRetVal(name, Some(ctx.unzip._2))
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
          evaluate(rhs)
          evaluate(body)(using evalCtx + (name -> getRes(rhs)))
          termMap.addOne(term, getRes(body))
        else ??? //TODO: letrec
      case Blk(stmts) => 
        stmts.map{
          case t: Term => evaluate(t)
          case other => throw MonomorphError(s"Encountered unlifted non-term ${other} in block ")
        }
        termMap.addOne(term, {
          if stmts.length == 0 
          then BoundedTerm(LiteralVal(UnitLit(false)))
          else stmts.reverse.head match 
            case t: Term => getRes(t)
            case _ => utils.die
        })
      case If(body, alternate) => 
        val res = body match
          case IfThen(condition, consequent) => 
            evaluate(consequent)
            alternate.map(alt => evaluate(alt))
            evaluate(condition)
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
        evaluate(t)
        termMap.addOne(term, getRes(t))
      case Tup(fields) => 
        fields.map{
          case (name, Fld(flags, value)) => evaluate(value)
        }
        termMap.addOne(term, BoundedTerm(monoer.createTupVal(fields.map{case (name, Fld(flags, value)) => getRes(value)})))
      case Bra(rcd, t) => 
        evaluate(t)
        termMap.addOne(term, getRes(t))
      // case _: Bind => ???
      // case _: Test => ???
      // case With(term, Rcd(fields)) => ???
      // case CaseOf(term, cases) => ???     
      // case Subs(array, index) => ???
      // case Assign(lhs, rhs) => ???
      // case New(None, body) => ???
      // case Rcd(fields) => ???
      case _ => utils.die
    debug.outdent()
    debug.writeLine(s"╙Result ${getRes(term).getValue.map(_.toString).toList}:")

  def defunctionalize(term: Term)(using termMap: MutMap[Term, BoundedTerm]): Term = {
    def getRes(term: Term): BoundedTerm = termMap.getOrElse(term, throw MonomorphError(s"Bounds for ${term} not found during defunc."))
    // TODO: Change to use basic pattern match instead of UCS
    def valSetToBranches(vals: List[MonoVal], acc: List[Either[IfBody,Statement]] = List(Left(IfElse(Var("error")))))(using field: Var, args: Option[List[Term]]): List[Either[IfBody,Statement]] = 
      debug.writeLine(s"Expanding ${vals}")
      vals match
      case Nil => acc
      case head :: next => head match
        case o@ObjVal(name, params, fields) =>
          val selValue = monoer.getFieldVal(o, field.name)
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
                      val lambdaMemFunc = monoer.getFieldVal(o, "apply").asValue.get.asInstanceOf[FuncVal]
                      val caseVarNm: Var = Var(s"obj$$${o.name}")
                      Right(NuFunDef(Some(false), Var("obj"), None, Nil, Left(Var(o.name)))(None, None, None, None, None, false, Nil)) :: 
                        List[Either[IfBody,Statement]](Left(IfThen(Var(o.name), App(Var(lambdaMemFunc.name), toTuple(caseVarNm :: a)))))
                    })
                  IfOpApp(scrut, Var("is"), IfBlock(branches))
                case None => 
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
            case _ => utils.die
          }
          valSetToBranches(next, Left(branchCase) :: acc)
        // case t@TupVal(fields) =>
        //   val selValue = fields.getOrElse(field, throw MonomorphError(s"Invalid field selection ${field} from Tuple"))
        case _ => utils.die


    val ret = term match
      case x: (Lit | Var) => x
      case App(sel@Sel(receiver, field), args) => 
        debug.writeLine(s"Specializing ${term}")
        debug.indent()
        val nuReceiver = defunctionalize(receiver)
        val nuArgs = defunctionalize(args)
        val ifBlockLines = valSetToBranches(getRes(receiver).getValue.toList)(using field, Some(extractFuncArgs(nuArgs)))
        val ifBlk = IfBlock(ifBlockLines)
        val res = Let(false, Var("obj"), nuReceiver,
            If(IfOpApp(Var("obj"), Var("is"), ifBlk), None))
        debug.writeLine(s"Result: ${res}")
        debug.outdent()
        res
      case App(op@Var(name), args) if builtInOps.contains(name) =>
          App(op, defunctionalize(args))
      case App(lhs@NuNew(cls), args) =>
        (cls, args) match {
          case (v: Var, args: Tup) =>
            App(lhs, defunctionalize(args))
          case _ => ???
        }
      case App(callee, args) => 
        if(getRes(callee).getValue.find(_.isInstanceOf[ObjVal]).isDefined)
          defunctionalize(App(Sel(callee, Var("apply")), args))
        else 
          App(defunctionalize(callee), defunctionalize(args))
      case Tup(fields) => Tup(fields.map{
        case (name, Fld(flags, value)) => (name, Fld(flags, defunctionalize(value)))})
      case If(IfThen(expr, rhs), els) => If(IfThen(defunctionalize(expr), defunctionalize(rhs)), els.map(defunctionalize))
      case New(Some((constructor, args)), body) => New(Some((constructor, defunctionalize(args))), body)
      case Sel(receiver, fieldName) => 
        val nuReceiver = defunctionalize(receiver)
        if (getRes(receiver).getValue.forall(_.isInstanceOf[ObjVal]))
        then
          debug.writeLine(s"Specializing ${term}")
          debug.indent()
          val ifBlockLines = valSetToBranches(getRes(receiver).getValue.toList.sortWith((x, y) => (x.toString > y.toString)))(using fieldName, None)
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
          case t: Term => defunctionalize(t)
          case other => other
        })
      case Bra(false, term) => Bra(false, defunctionalize(term))
      case _ => throw MonomorphError(s"Cannot Defunctionalize ${term}")
    ret
  }
}
