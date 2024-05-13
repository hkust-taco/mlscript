package mlscript
package compiler
package polydef

import mlscript.utils.*, shorthands.*
import scala.collection.mutable
import java.util.IdentityHashMap
import scala.collection.JavaConverters._

type TypeVar
type TermId = Uid[Term]
type TypeVarId = Uid[TypeVar]
type Cnstr = ProdStrat -> ConsStrat


enum ProdStrat(using val euid: TermId) {
  case NoProd()(using TermId) extends ProdStrat
  case ProdObj(ctor: Option[Var], fields: Ls[Var -> ProdStrat])(using TermId) extends ProdStrat, ProdObjImpl
  case ProdPrim(name: String)(using TermId) extends ProdStrat
  case ProdFun(lhs: ConsStrat, rhs: ProdStrat)(using TermId) extends ProdStrat
  case ProdVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId) extends ProdStrat
  case ProdTup(fields: Ls[ProdStrat])(using TermId) extends ProdStrat
}
enum ConsStrat(using val euid: TermId) {
  case NoCons()(using TermId) extends ConsStrat
  case ConsObj(name: Option[Var], fields: Ls[Var -> ConsStrat])(using TermId) extends ConsStrat, ConsObjImpl
  case ConsPrim(name: String)(using TermId) extends ConsStrat
  case ConsFun(lhs: ProdStrat, rhs: ConsStrat)(using TermId) extends ConsStrat
  case ConsVar(uid: TypeVarId, name: String)(boundary: Option[Var] = None)(using TermId) extends ConsStrat
  case ConsTup(fields: Ls[ConsStrat])(using TermId) extends ConsStrat
}
import ProdStrat.*, ConsStrat.*

trait ConsObjImpl { self: ConsObj =>
  var selectionSource: Set[ProdStrat] = Set()
}

trait ProdObjImpl { self: ProdObj =>
  var objDestination: Set[ConsStrat] = Set()
}

class Polydef(debug: Debug) {
  
  extension (t: Term) {
    def uid = termMap.getOrElse(t, {
      val id = euid.nextUid
      termMap.addOne((t, euid.nextUid))
      id
    })
  }

  var log: Str => Unit = (s) => ()
  var constraints: Ls[Cnstr] = Nil
  val termMap = new IdentityHashMap[Term, TermId]().asScala
  val varsName = mutable.Map.empty[TypeVarId, Str]
  val vuid = Uid.TypeVar.State()
  val euid = Uid.Term.State()
  val noExprId = euid.nextUid

  def freshVar(n: String)(using TermId): ((ProdVar), (ConsVar)) =
    val vid = vuid.nextUid
    val pv = ProdVar(vid, n)()
    val cv = ConsVar(vid, n)()
    varsName += vid -> n
    log(s"fresh var '$n")
    (pv, cv)
  def freshVar(n: Var)(using TermId): ((ProdVar), (ConsVar)) =
   freshVar(n.name)

  def apply(p: TypingUnit)(using ctx: Map[Var, ProdVar] = Map()): (Ls[Var -> ProdStrat], ProdStrat) = 
    // if constraints.nonEmpty then return Nil
    val vars: Map[Var, ProdVar] = p.rawEntities.collect { 
      case fun: NuFunDef =>
        fun.nme -> freshVar(fun.name)(using noExprId)._1
    }.toMap
    val constructorPrototypes: Map[Var, Cnstr] = p.rawEntities.collect { 
      case ty: NuTypeDef =>
        ty.nameVar -> freshVar(ty.nameVar)(using noExprId)
    }.toMap
    val fullCtx = ctx ++ vars ++ constructorPrototypes.map((v, s) => (v, s._1.asInstanceOf[ProdVar]))
    val constructors: Map[Var, ProdObj] = p.rawEntities.collect { 
      case ty: NuTypeDef =>
        debug.writeLine(s"Completing type info for class ${ty.nameVar} with ctors ${constructorPrototypes.map((v, s) => (v, s._1))}")
        given TermId = noExprId
        val argTup = ty.params.get
        val (pList, cList) = argTup.fields.map{
          case (Some(v), Fld(flags, _)) if flags.genGetter =>
            val fldVar = freshVar(s"${argTup.uid}_${v.name}")(using noExprId)
            ((v, fldVar._1), (v, fldVar._2))
          case (Some(v), Fld(flags, _)) if !flags.genGetter => 
            debug.writeLine(s"Non val ${v} class parameter is not supported.")
            ??? // Unsupported
          case other =>
            debug.writeLine(s"${other} class parameter is not supported.")
            ??? // Unsupported
        }.unzip
        val bodyStrats = apply(ty.body)(using fullCtx ++ pList.toMap) // TODO: Add additional ctx for class arguments, i.e. class X(num: Int)
        constrain(ProdFun(ConsTup(cList.map(_._2)),ProdObj(Some(ty.nameVar), bodyStrats._1 ++ pList)), constructorPrototypes(ty.nameVar)._2)
        ty.nameVar -> ProdObj(Some(ty.nameVar), bodyStrats._1)
    }.toMap
    val tys = p.rawEntities.flatMap{
      case f: NuFunDef => {
        f.rhs match 
          case Left(value) => 
            val p = process(value)(using fullCtx)
            val v = vars(f.nme)
            constrain(p, ConsVar(v.uid, v.name)()(using noExprId))
            Some(p)
          case Right(value) => None
      }
      case t: Term => {
        val topLevelProd = process(t)(using fullCtx)
        //constrain(topLevelProd, NoCons()(using noExprId))
        Some(topLevelProd)
      }
      case other => {
        debug.writeLine(s"Skipping ${other}")
        None
      }
    }
    (vars.toList, tys.lastOption.getOrElse(ProdPrim("unit")(using noExprId)))

  val termToProdType = mutable.Map.empty[TermId, ProdStrat]
  val selTermToType = mutable.Map.empty[TermId, ConsObj]
  //val ObjCreatorToType = mutable.Map.empty[TermId, ProdObj]

  def builtinOps: Map[Var, ProdFun] = {
    given TermId = noExprId
    Map(
      (Var("+") -> ProdFun(ConsTup(List(ConsPrim("Int"),ConsPrim("Int"))), ProdPrim("Int"))),
      (Var("-") -> ProdFun(ConsTup(List(ConsPrim("Int"),ConsPrim("Int"))), ProdPrim("Int"))),
      (Var("*") -> ProdFun(ConsTup(List(ConsPrim("Int"),ConsPrim("Int"))), ProdPrim("Int"))),
      (Var("==") -> ProdFun(ConsTup(List(ConsPrim("Int"),ConsPrim("Int"))), ProdPrim("Bool"))),
      (Var("concat") -> ProdFun(ConsTup(List(ConsPrim("String"))), ProdFun(ConsTup(List(ConsPrim("String"))), ProdPrim("String")))),
      (Var("toString") -> ProdFun(ConsTup(List(ConsPrim("Int"))), ProdPrim("String")))
    )
  }

  def process(t: Term)(using ctx: Map[Var, ProdVar]): ProdStrat = 
    debug.writeLine(s"Processing term ${t} under")
    debug.indent()
    debug.writeLine(s"${ctx}")
    debug.outdent()
    val res: ProdStrat = t match
      case IntLit(_) => ProdPrim("Int")(using t.uid)
      case DecLit(_) => ??? // floating point numbers as integers type
      case StrLit(_) => ProdPrim("String")(using t.uid)
      case Var("true") | Var("false") => ProdPrim("Bool")(using t.uid)
      case v @ Var(id) if builtinOps.contains(v) =>
        builtinOps(v)
      case v @ Var(id) =>// if varCtx(id).isDef then {
        ctx(v).copy()(Some(v))(using t.uid)
      //} else ctx(r).s.copy()(None)(using t.uid)
      case App(func, arg) => 
        //debug.writeLine(s"${summon[Map[Var, ProdStrat]]}")
        val funcRes = process(func)
        val argRes = process(arg)
        funcRes match 
          case _ =>
            val sv = freshVar(s"${t.uid}_callres")(using t.uid)
            constrain(funcRes, ConsFun(argRes, sv._2)(using noExprId))
            sv._1
      case Lam(t @ Tup(args), body) =>
        val mapping = args.map{
          case (None, Fld(_, v: Var)) =>
            (v, freshVar(s"${t.uid}_${v.name}")(using noExprId))
          case other => 
            debug.writeLine(s"${other}")
            ??? // Unsupported
        }
        ProdFun(ConsTup(mapping.map(_._2._2))(using t.uid),
          process(body)(using ctx ++ mapping.map((i, s) => (i, s._1))))(using t.uid)
      case If(IfThen(scrut, thenn), S(elze)) =>
        constrain(process(scrut), ConsPrim("Bool")(using noExprId))
        val res = freshVar(s"${t.uid}_ifres")(using t.uid)
        constrain(process(thenn), res._2)
        constrain(process(elze), res._2)
        res._1
      case If(_) => ??? // Desugar first (resolved by pretyper OR moving post-process point)
      case Tup(fields) =>
        val mapping = fields.map{
          case (None, Fld(_, fieldTerm: Term)) =>
            process(fieldTerm)
          case _ => ??? // Unsupported
        }
        ProdTup(mapping)(using t.uid)
      case Sel(receiver, fieldName) =>
        val selRes = freshVar(s"${t.uid}_selres")(using t.uid)
        val selector = ConsObj(None, List(fieldName -> selRes._2))(using t.uid)
        constrain(process(receiver), selector)
        selTermToType += (t.uid -> selector.asInstanceOf[ConsObj])
        selRes._1
      case Bra(true, t) =>
        process(t)
      case Rcd(fields) =>
        ProdObj(None, fields.map{
          case (v, Fld(_, t)) => (v -> process(t))
        })(using t.uid)
      case Blk(stmts) => 
        apply(TypingUnit(stmts))._2

    registerTermToType(t, res)
  
  val constraintCache = mutable.Set.empty[(ProdStrat, ConsStrat)]
  val upperBounds = mutable.Map.empty[TypeVarId, Ls[ConsStrat]].withDefaultValue(Nil)
  val lowerBounds = mutable.Map.empty[TypeVarId, Ls[ProdStrat]].withDefaultValue(Nil)

  def constrain(prod: ProdStrat, cons: ConsStrat): Unit = {
    debug.writeLine(s"constraining ${prod} -> ${cons}")
    if (constraintCache.contains(prod -> cons)) return () else constraintCache += (prod -> cons)
    
    (prod, cons) match
        case (ProdPrim(n), NoCons()) =>
          ()
        case (ProdPrim(p1), ConsPrim(p2)) if p1 == p2 => ()
        case (ProdVar(v, pn), ConsVar(w, cn))
          if v === w => ()
        case (pv@ProdVar(v, _), _) =>
          cons match {
            case c: ConsObj if lowerBounds(v).isEmpty =>
              c.selectionSource = c.selectionSource + pv
            case _ => ()
          }
          upperBounds += v -> (cons :: upperBounds(v))
          lowerBounds(v).foreach(lb_strat => constrain(lb_strat, cons))
        case (_, cv@ConsVar(v, _)) =>
          prod match {
            case p: ProdObj if upperBounds(v).isEmpty =>
              p.objDestination = p.objDestination + cv
            case _ => ()
          }
          lowerBounds += v -> (prod :: lowerBounds(v))
          upperBounds(v).foreach(ub_strat => constrain(prod, ub_strat))
        case (ProdFun(lhs1, rhs1), ConsFun(lhs2, rhs2)) =>
          constrain(lhs2, lhs1)
          constrain(rhs1, rhs2)
        case (ProdTup(fields1), ConsTup(fields2)) =>
          (fields1 zip fields2).map((p, c) =>
            constrain(p, c)
          )
        case (pv@ProdObj(nme1, fields1), cv@ConsObj(nme2, fields2)) =>
          nme2 match 
            case Some(name) if name != nme1 => ???
            case _ => ()
          fields2.map((key, res2) => {
            fields1.find(_._1 == key) match 
              case None => ???
              case Some((_, res1)) => 
                cv.selectionSource = cv.selectionSource + pv
                pv.objDestination = pv.objDestination + cv
                constrain(res1, res2)
          })
  }

  // TODO: remove redundancy between selToObjTypes and selTermToType
  lazy val selToObjTypes: Map[TermId, Set[ProdObj]] = selTermToType.map((termId, cons) =>
    (termId, cons.selectionSource.flatMap{
        case p:ProdObj => Some(p)
        case other => 
          debug.writeLine(s"${other}")
          None
      }
    )
  ).toMap

  def rewriteTerm(t: Term): Term = 
    def objSetToMatchBranches(receiver: Var, fieldName: Var, objSet: List[ProdObj], acc: CaseBranches = NoCases): CaseBranches =
      objSet match 
        case Nil => acc
        case ProdObj(Some(v), _) :: rest => 
          objSetToMatchBranches(receiver, fieldName, rest, Case(v, Sel(receiver, fieldName), acc))
    t match
      case IntLit(_) => t
      case StrLit(_) => t
      case Var(_) => t
      case App(func, arg) => 
        App(rewriteTerm(func), rewriteTerm(arg))
      case Lam(t @ Tup(args), body) =>
        Lam(rewriteTerm(t), rewriteTerm(body))
      case If(IfThen(scrut, thenn), S(elze)) =>
        If(IfThen(rewriteTerm(scrut), rewriteTerm(thenn)), S(rewriteTerm(elze)))
      case If(_) => ??? // Desugar first (resolved by pretyper OR moving post-process point)
      case Tup(fields) =>
        Tup(fields.map{
          case (None, Fld(flags, fieldTerm: Term)) =>
            (None, Fld(flags, rewriteTerm(fieldTerm)))
          case _ => ??? // Unsupported
        })
      case Sel(receiver, fieldName) =>
        val letName = Var(s"selRes$$${t.uid}")
        Let(false, letName, rewriteTerm(receiver),
          CaseOf(letName, objSetToMatchBranches(letName, fieldName, selToObjTypes(t.uid).toList))
        )
      case Bra(true, t) =>
        Bra(true, rewriteTerm(t))
      case Rcd(fields) =>
        Rcd(fields.map{
          case (v, Fld(flags, t)) => (v, Fld(flags, rewriteTerm(t)))
        })
      case Blk(stmts) => 
        Blk(rewriteStatements(stmts))
    
  def rewriteStatements(stmts: List[Statement]): List[Statement] =
    stmts.map{
      case ty: NuTypeDef => 
        ty.copy(body = rewriteProgram(ty.body))(ty.declareLoc, ty.abstractLoc, ty.annotations)
      case f: NuFunDef => 
        f.copy(rhs = f.rhs match
          case Left(t) => Left(rewriteTerm(t))
          case Right(_) => f.rhs
        )(f.declareLoc, f.virtualLoc, f.mutLoc, f.signature, f.outer, f.genField, f.annotations)
      case t: Term => 
        rewriteTerm(t)
    }
  def rewriteProgram(t: TypingUnit): TypingUnit = 
    TypingUnit(rewriteStatements(t.rawEntities))

  private def registerTermToType(t: Term, s: ProdStrat) = {
    termToProdType.get(t.uid) match {
      case None => {
        termToProdType += t.uid -> s
        s
      }
      case Some(value) =>
        lastWords(s"${t} registered two prod strategies:\n already has ${value}, but got ${s}")
    }
  }
}