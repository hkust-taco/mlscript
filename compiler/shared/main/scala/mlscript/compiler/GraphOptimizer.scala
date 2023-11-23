package mlscript.compiler

import mlscript.*
import mlscript.compiler.*
import mlscript.utils.*
import shorthands.*

import scala.annotation.tailrec
import scala.collection.immutable.*
import scala.collection.mutable.{HashMap => MutHMap}
import scala.collection.mutable.{HashSet => MutHSet, Set => MutSet}
import scala.collection.mutable.MultiMap

final case class GraphOptimizingError(message: String) extends Exception(message)

class GraphOptimizer:
  private type Ctx = Map[Str, Name]
  private type ClassCtx = Map[Str, ClassInfo]
  private type FieldCtx = Map[Str, (Str, ClassInfo)]
  private type FnCtx = Set[Str]
  private type OpCtx = (Unit, Set[Str])
  
  import GOExpr._
  import GONode._

  private val counter = MutHMap[Str, Int]()
  private def gensym(s: Str = "x") = {
    val count = counter.getOrElse(s, 0)
    val ts = s.split("%")(0)
    val tmp = s"$s%$count"
    counter.update(s, count + 1)
    Name(tmp)
  }

  private var fid = 0
  private def genfid() = {
    val tmp = fid
    fid += 1
    tmp
  }

  private var cid = 0
  private def gencid() = {
    val tmp = cid
    cid += 1
    tmp
  }

  private final val ref = x => Ref(x)
  final val result = x => Result(x)
  private final val sresult = (x: TrivialExpr) => Result(List(x))
  private final val unexpected_node = (x: GONode) => throw GraphOptimizingError(s"unsupported node $x")
  private final val unexpected_term = (x: Term) => throw GraphOptimizingError(s"unsupported term $x")

  private def buildBinding
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (name: Str, e: Term, body: Term)
    (k: GONode => GONode): GONode =
    buildResultFromTerm(e) {
      case Result((r: Ref) :: Nil) =>
        given Ctx = ctx + (name -> r.name)
        buildResultFromTerm(body)(k)
      case Result((lit: Literal) :: Nil) =>
        val v = gensym()
        given Ctx = ctx + (name -> v)
        LetExpr(v,
          lit,
          buildResultFromTerm(body)(k))
      case node @ _ => node |> unexpected_node
    }

  private def buildResultFromTup
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (tup: Tup)(k: GONode => GONode): GONode =
    tup match
      case Tup(N -> Fld(FldFlags.empty, x) :: xs) => buildResultFromTerm(x) {
        case Result(x :: Nil) =>
          buildResultFromTup(Tup(xs)) {
            case Result(xs) => x :: xs |> result |> k
            case node @ _ => node |> unexpected_node
          }
        case node @ _ => node |> unexpected_node
      }

      case Tup(Nil) => Nil |> result |> k

  private def bindingPatternVariables
    (scrut: Str, tup: Tup, cls: ClassInfo, rhs: Term): Term =
    val params = tup.fields.map {
      case N -> Fld(FldFlags.empty, Var(name)) => name
      case _ => throw GraphOptimizingError("unsupported field")
    }
    val fields = cls.fields
    val tm = params.zip(fields).foldLeft(rhs) {
      case (tm, (param, field)) => 
        Let(false, Var(param), Sel(Var(scrut), Var(field)), tm)
    }

    tm

  private def buildResultFromTerm
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (tm: Term)(k: GONode => GONode): GONode =
    val res = tm match
      case lit: Lit => Literal(lit) |> sresult |> k
      case v @ Var(name) =>
        if (name.isCapitalized)
          val v = gensym()
          LetExpr(v,
            CtorApp(clsctx(name), Nil),
            v |> ref |> sresult |> k)
        else
          ctx.get(name) match {
            case Some(x) => x |> ref |> sresult |> k
            case _ => throw GraphOptimizingError(s"unknown name $name in $ctx")
          }

      case Lam(Tup(fields), body) =>
        val xs = fields map {
          case N -> Fld(FldFlags.empty, Var(x)) => Name(x)
          case fld @ _ => throw GraphOptimizingError(s"not supported tuple field $fld")
        }
        val bindings = xs map {
          case x @ Name(str) => str -> x
        }
        val v = gensym()
        given Ctx = ctx ++ bindings 
        LetExpr(v,
          Lambda(xs, buildResultFromTerm(body){ x => x }),
          v |> ref |> sresult |> k)
  
      case App(
        App(Var(name), Tup((_ -> Fld(_, e1)) :: Nil)), 
        Tup((_ -> Fld(_, e2)) :: Nil)) if opctx._2.contains(name) =>
        buildResultFromTerm(e1) {
          case Result(v1 :: Nil) =>
            buildResultFromTerm(e2) {
              case Result(v2 :: Nil) =>
                val v = gensym()
                LetExpr(v,
                  BasicOp(name, List(v1, v2)),
                  v |> ref |> sresult |> k)
              case node @ _ => node |> unexpected_node
            }
          case node @ _ => node |> unexpected_node
        }
        
      case App(Var(name), xs @ Tup(_)) if name.isCapitalized =>
        buildResultFromTerm(xs) {
          case Result(args) => 
            val v = gensym()
            LetExpr(v,
              CtorApp(clsctx(name), args),
              v |> ref |> sresult |> k)
          case node @ _ => node |> unexpected_node
        }

      case App(f, xs @ Tup(_)) =>
        buildResultFromTerm(f) {
        case Result(Ref(f) :: Nil) if fnctx.contains(f.str) => buildResultFromTerm(xs) {
          case Result(args) =>
            val v = gensym()
            LetCall(List(v), GODefRef(Right(f.str)), args, v |> ref |> sresult |> k)
          case node @ _ => node |> unexpected_node
        }
        case Result(Ref(f) :: Nil) => buildResultFromTerm(xs) {
          case Result(args) =>
            val v = gensym()
            LetExpr(v,
              Apply(f, args),
              v |> ref |> sresult |> k)
          case node @ _ => node |> unexpected_node
        }
        case node @ _ => node |> unexpected_node
      }

      case Let(false, Var(name), rhs, body) => 
        buildBinding(name, rhs, body)(k)

      case If(IfThen(cond, tru), Some(fls)) => 
        buildResultFromTerm(cond) {
          case Result(Ref(cond) :: Nil) => 
            val jp = gensym("j")
            val tru2 = buildResultFromTerm(tru) {
              case Result(xs) => Jump(GODefRef(Right(jp.str)), xs)
              case node @ _ => node |> unexpected_node
            }
            val fls2 = buildResultFromTerm(fls) {
              case Result(xs) => Jump(GODefRef(Right(jp.str)), xs)
              case node @ _ => node |> unexpected_node
            }
            val res = gensym()
            LetJoin(jp,
              Ls(res),
              res |> ref |> sresult |> k,
              Case(cond, Ls((clsctx("True"), tru2), (clsctx("False"), fls2))))
          case node @ _ => node |> unexpected_node
        }
        
      case If(IfOpApp(lhs, Var("is"), IfBlock(lines)), N)
        if lines forall {
          case L(IfThen(App(Var(ctor), Tup((N -> Fld(FldFlags.empty, _: Var)) :: _)), _)) => ctor.isCapitalized
          case L(IfThen(Var(ctor), _)) => ctor.isCapitalized || ctor == "_"
          case _ => false
        }
        => buildResultFromTerm(lhs) {
          case Result(Ref(scrut) :: Nil) =>
            val jp = gensym("j")
            val cases: Ls[(ClassInfo, GONode)] = lines map {
              case L(IfThen(App(Var(ctor), params: Tup), rhs)) =>
                clsctx(ctor) -> {
                  // need this because we have built terms (selections in case arms) containing names that are not in the original term
                  given Ctx = ctx + (scrut.str -> scrut) 
                  buildResultFromTerm(
                    bindingPatternVariables(scrut.str, params, clsctx(ctor), rhs)) {
                      case Result(xs) => Jump(GODefRef(Right(jp.str)), xs)
                      case node @ _ => node |> unexpected_node
                    }
                }
              case L(IfThen(Var(ctor), rhs)) =>
                clsctx(ctor) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(GODefRef(Right(jp.str)), xs)
                  case node @ _ => node |> unexpected_node
                }
              case _ => throw GraphOptimizingError(s"not supported UCS")
            }
            val res = gensym()
            LetJoin(jp,
              Ls(res),
              res |> ref |> sresult |> k, 
              Case(scrut, cases)  
            )
          case node @ _ => node |> unexpected_node
        }

      case Bra(false, tm) => buildResultFromTerm(tm)(k)

      case Blk((tm: Term) :: Nil) => buildResultFromTerm(tm)(k)
      
      case Blk((tm: Term) :: xs) => buildBinding("_", tm, Blk(xs))(k)

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: Nil) =>
        buildBinding(name, tm, Var(name))(k)

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: xs) =>
        buildBinding(name, tm, Blk(xs))(k)

      case Sel(tm @ Var(name), Var(fld)) =>
        buildResultFromTerm(tm) {
          case Result(Ref(res) :: Nil) =>
            val v = gensym()
            val cls = fldctx(fld)._2
            LetExpr(v,
              Select(res, cls, fld),
              v |> ref |> sresult |> k) 
          case node @ _ => node |> unexpected_node
        }

      case tup: Tup => buildResultFromTup(tup)(k)

      case term => term |> unexpected_term
    
    res

  private def buildDefFromNuFunDef
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (nfd: Statement): GODef = nfd match
    case NuFunDef(_, Var(name), None, Nil, L(Lam(Tup(fields), body))) =>
      val strs = fields map {
          case N -> Fld(FldFlags.empty, Var(x)) => x
          case _ => throw GraphOptimizingError("unsupported field") 
        }
      val names = strs.map { x => gensym(x) }
      given Ctx = ctx ++ strs.zip(names)
      GODef(
        genfid(),
        name,
        false,
        names,
        1,
        buildResultFromTerm(body) { x => x }
      )
    case _ => throw GraphOptimizingError("unsupported NuFunDef")

  private def getClassInfo(ntd: Statement): ClassInfo = ntd match
    case NuTypeDef(Cls, TypeName(name), Nil, S(Tup(args)), N, N, Nil, N, N, TypingUnit(Nil)) =>
      ClassInfo(gencid(),
        name, 
        args map {
          case N -> Fld(FldFlags.empty, Var(name)) => name
          case _ => throw GraphOptimizingError("unsupported field")
        }
      )
    case NuTypeDef(Cls, TypeName(name), Nil, N, N, N, Nil, N, N, TypingUnit(Nil)) =>
      ClassInfo(gencid(),
        name,
        Ls(),
      )
    case x @ _ => throw GraphOptimizingError(f"unsupported NuTypeDef $x")

  private def checkDuplicateField(ctx: Set[Str], cls: ClassInfo): Set[Str] =
    val u = cls.fields.toSet intersect ctx
    if (u.nonEmpty)
      throw GraphOptimizingError(f"duplicate class field $u")
    cls.fields.toSet union ctx

  private def getDefinitionName(nfd: Statement): Str = nfd match
    case NuFunDef(_, Var(name), _, _, _) => name
    case _ => throw GraphOptimizingError("unsupported NuFunDef")

  def buildGraph(unit: TypingUnit): GOProgram = unit match
    case TypingUnit(entities) =>
      val grouped = entities groupBy {
        case ntd: NuTypeDef => 0
        case nfd: NuFunDef => 1
        case tm: Term => 2
        case _ => throw GraphOptimizingError("unsupported entity")
      }

      import scala.collection.mutable.{ HashSet => MutHSet }

      val ops = Set("+", "-", "*", "/")
      val cls = grouped.getOrElse(0, Nil).map(getClassInfo)
      
      val init: Set[Str] = Set.empty
      cls.foldLeft(init) {
        case (ctx, cls) => checkDuplicateField(ctx, cls)
      }

      val clsinfo = cls.toSet
      val clsctx: ClassCtx = cls.map{ case ClassInfo(_, name, _) => name }.zip(cls).toMap
      val fldctx: FieldCtx = cls.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      val namestrs = grouped.getOrElse(1, Nil).map(getDefinitionName)
      val fnctx = namestrs.toSet
      var ctx = namestrs.zip(namestrs.map(x => Name(x))).toMap
      ctx = ctx ++ ops.map { op => (op, Name(op)) }.toList

      given Ctx = ctx
      given ClassCtx = clsctx
      given FieldCtx = fldctx
      given FnCtx = fnctx
      given OpCtx = ((), ops)
      val defs: Set[GODef] = grouped.getOrElse(1, Nil).map(buildDefFromNuFunDef).toSet
     
      val terms: Ls[Term] = grouped.getOrElse(2, Nil).map( {
        case tm: Term => tm
        case _ => ??? /* unreachable */
      })

      val main = buildResultFromTerm (terms match {
        case x :: Nil => x
        case _ => throw GraphOptimizingError("only one term is allowed in the top level scope")
      }) { k => k }
      
      fixCrossReferences(main, defs)
      validate(main, defs, false)
      GOProgram(clsinfo, defs, main)

  private class FixCrossReferences(defs: Set[GODef]) extends GOIterator:
    override def iterate(x: LetCall) = x match
      case LetCall(resultNames, defnref, args, body) =>
        val target = defnref.defn match {
          case Left(defn) => defs.find{_.getName == defn.name}.get
          case Right(name) => defs.find{_.getName == name}.get
        }
        defnref.defn = Left(target)
        body.accept_iterator(this)
    override def iterate(x: Jump) = x match
      case Jump(defnref, _) =>
        // maybe not promoted yet
        defnref.defn match {
          case Left(defn) => defs.find{_.getName == defn.name}.map{x => defnref.defn = Left(x)}
          case Right(name) => defs.find{_.getName == name}.map{x => defnref.defn = Left(x)}
        }

  private def fixCrossReferences(entry: GONode, defs: Set[GODef]): Unit  =
    val it = FixCrossReferences(defs)
    entry.accept_iterator(it)
    defs.foreach(_.body.accept_iterator(it))


  // --------------------------------

  import Elim._
  import Intro._

  private def appendCtx(ctx: Ctx, x: String, y: Name) = {
    ctx.get(y.str) match {
      case Some(z) => ctx + (x -> z)
      case None => ctx + (x -> y)
    }
  }

  private def tryGetDefn(r: GODefRef) = {
    r.defn.swap.toOption
  }

  private def used(using v: String, ctx: Ctx)(name: String) =
    name == v || ctx.get(name).contains(v)

  private class EliminationAnalysis extends GOIterator:
    val elims = new MutHMap[Str, MutSet[Elim]] with MultiMap[Str, Elim]
    override def iterate_name_use(x: Name) =
      elims.addBinding(x.str, EDirect)
    override def iterate(x: Case) = x match
      case Case(x, cases) =>
        x.accept_use_iterator(this)
        elims.addBinding(x.str, EDestruct)
        cases foreach { (cls, arm) => arm.accept_iterator(this) }
    override def iterate(x: Select) = x match
      case Select(x, cls, field) =>
        elims.addBinding(x.str, ESelect(field))
    override def iterate(x: Jump) = x match
      case Jump(defnref, args) => 
        args.foreach(_.accept_iterator(this))
        val defn = defnref.expectDefn
        args.zip(defn.activeParams).foreach {
          case (Ref(Name(x)), ys) => ys.foreach { y => elims.addBinding(x, y) }
          case _ => 
        }
    override def iterate(x: LetCall) = x match
      case LetCall(xs, defnref, args, body) =>
        xs.foreach(_.accept_def_iterator(this))
        args.foreach(_.accept_iterator(this))
        val defn = defnref.expectDefn 
        args.zip(defn.activeParams).foreach {
          case (Ref(Name(x)), ys) => ys.foreach { y => elims.addBinding(x, y) }
          case _ => 
        }
        body.accept_iterator(this)

    override def iterate(x: GOProgram) =
      var changed = true
      while (changed)
        changed = false
        x.defs.foreach { defn =>
          val old = defn.activeParams
          elims.clear()
          defn.accept_iterator(this)
          defn.activeParams = defn.params.map {
            param => elims.get(param.str) match {
              case Some(elims) => elims.toSet
              case None => Set()
            }
          }
          changed |= (old != defn.activeParams)
        }

  private object IntroductionAnalysis extends GOIterator:
    def getIntro(node: GONode, intros: Map[Str, Intro]): Ls[Opt[Intro]] = node match
      case Case(scrut, cases) => 
        val cases_intros = cases.map { case (cls, node) => getIntro(node, intros) }
        if (cases_intros.toSet.size > 1)
          cases_intros.head.map { _ => None }
        else
          cases_intros.head
      case Jump(defnref, args) =>
        val jpdef = defnref.expectDefn
        val intros2 = jpdef.params.zip(args)
          .filter{ (_, arg) => getIntro(arg, intros).isDefined }
          .map{ case (param, arg) => param.str -> getIntro(arg, intros).get }
        getIntro(jpdef.body, intros2.toMap)
      case LetCall(resultNames, defnref, args, body) =>
        val defn = defnref.expectDefn
        val intros2 = defn.activeResults.zip(resultNames).foldLeft(intros) { 
          case (intros, (Some(i), name)) => intros + (name.str -> i)
          case (intros, _) => intros
        }
        getIntro(body, intros2)
      case LetExpr(name, expr, body) => 
        val intros2 = getIntro(expr, intros).map { x => intros + (name.str -> x) }.getOrElse(intros)
        getIntro(body, intros2)
      case LetJoin(joinName, params, rhs, body) =>
        throw GraphOptimizingError(f"join points after promotion: $node")
      case Result(res) => 
        res.map { x => getIntro(x, intros) }

    def getIntro(expr: TrivialExpr, intros: Map[Str, Intro]) = expr match 
      case Literal(lit) => None
      case Ref(name) => intros.get(name.str)

    def getIntro(expr: GOExpr, intros: Map[Str, Intro]): Opt[Intro] = expr match 
      case CtorApp(cls, args) => Some(ICtor(cls.ident))
      case Lambda(name, body) => Some(ILam(name.length))
      case _ => None

    def getIntro(expr: TrivialExpr): Opt[Intro] = getIntro(expr, Map.empty)
    def getIntro(expr: GOExpr): Opt[Intro] = getIntro(expr, Map.empty)
    def getIntro(node: GONode): Ls[Opt[Intro]] = getIntro(node, Map.empty)

    override def iterate(x: GOProgram) =
      var changed = true
      while (changed)
        changed = false
        x.defs.foreach { 
          defn =>
            val old = defn.activeResults
            defn.activeResults = getIntro(defn.body, Map.empty)
            changed |= old != defn.activeResults
        }

  private def freeVarAnalysis(using ctx: Set[Str])(expr: GOExpr, fv: Set[Str], fj: Set[Str]): (Set[Str], Set[Str]) = expr match {
    case Ref(Name(s)) => (if (ctx.contains(s)) fv else fv + s, fj)
    case Literal(_) => (fv, fj)
    case CtorApp(_, args) => (fv ++ args.flatMap {
      case Ref(Name(s)) if !ctx.contains(s) => Some(s)
      case _ => None
    }, fj)
    case Select(Name(x), cls, _) => (if (ctx.contains(x)) fv else fv + x, fj) 
    case BasicOp(_, args) => (fv ++ args.flatMap {
      case Ref(Name(s)) if !ctx.contains(s) => Some(s)
      case _ => None
    }, fj)
    case Lambda(params, body) =>
      val params2 = params.map { case Name(x) => x }
      freeVarAnalysis(using ctx ++ params2)(body, fv -- params2, fj -- params2)
    case Apply(Name(f), args) =>
      val fv2 = if (ctx.contains(f)) fv else fv + f
      val fv3 = fv2 ++ args.flatMap {
        case Ref(Name(s)) if !ctx.contains(s) => Some(s)
        case _ => None
      }
      (fv3, fj)
    }

  private def freeVarAnalysis(using ctx: Set[Str])(body: GONode, fv: Set[Str], fj: Set[Str]): (Set[Str], Set[Str])
    = body match {
    case Result(xs) => (fv ++ xs.flatMap {
      case Ref(Name(s)) if !ctx.contains(s) => Some(s)
      case _ => None
    }, fj)
    case Jump(defnref, _) =>
      val defn = defnref.expectDefn
      val params = defn.params map { case Name(x) => x }
      freeVarAnalysis(using ctx ++ params)(defn.body, fv -- params, fj -- params)
    case Case(Name(scrut), cases) => 
      val fv2 = if (ctx.contains(scrut)) fv else fv + scrut
      cases.foldLeft((fv2, fj)) {
        case ((fv, fj), (cls, e)) =>
          freeVarAnalysis(using ctx)(e, fv, fj)
      }
    case LetExpr(Name(x), e1, e2) =>
      val (fv2, fj2) = freeVarAnalysis(using ctx)(e1, fv, fj)
      freeVarAnalysis(using ctx + x)(e2, fv2 - x, fj2 - x)
    case LetJoin(Name(jp), xs, e1, e2) =>
      val params = xs map { case Name(x) => x }
      val (fv2, fj2) = freeVarAnalysis(using ctx ++ params)(e1, fv -- params, fj -- params)
      freeVarAnalysis(using ctx + jp)(e2, fv2 - jp, fj2 - jp)
    case LetCall(xs, defn, as, e) =>
      val results = xs map { case Name(x) => x }
      freeVarAnalysis(using ctx ++ results)(e, fv -- results, fj -- results)
  }

  private type RawSplitRemap = Set[((Str, Str), ClassInfo, Str, Ls[Str])]
  private type RawSplitPreRemap = Set[((Str, Str), Str, Ls[Str])]
  
  private def splitFunctionWhenDestructImpl(using classes: Set[ClassInfo],
                                                  params: Ls[Name], resultNum: Int, isjp: Bool)
  (accu: GONode => GONode, body: GONode, name: Str, target: Name):
  (RawSplitRemap, RawSplitPreRemap, Set[GODef], Set[GODef]) = {
    body match {
    case Result(_xs) => (Set.empty, Set.empty, Set.empty, Set.empty)
    case Jump(_jp, _xs) => (Set.empty, Set.empty, Set.empty, Set.empty)
    case Case(scrut, cases) if scrut == target =>
      val armfv = cases.map {
        case (cls, body) =>
          val (fv, _) = freeVarAnalysis(using Set.empty)(body, Set.empty, Set.empty)
          fv
      }

      val allfv: Set[Str] = armfv.foldLeft(Set.empty)((x, y) => x ++ y)
      val allfv_list = allfv.toList
      var retvals: Ls[TrivialExpr] = allfv_list.map{x => Ref(Name(x))}

    
      val new_predef = if (retvals.nonEmpty) {
        val new_body = accu(Result(retvals))
        
        val isTrivial = new_body match { 
          case Result(xs) => (xs == retvals && allfv.size <= params.length)
          case _ => false
        }

        val new_predef_name = gensym(name + "$P")
        val new_predef = GODef(
          genfid(),
          new_predef_name.str,
          false,
          params,
          allfv.size,
          accu(Result(retvals)))
        new_predef.isTrivial = isTrivial
        Some(new_predef)
      } else {
        None
      }

      cases.zip(armfv).foldLeft(
        (Set.empty, 
         new_predef.map { x => ((name, target.str), x.name, allfv_list) }.toSet,
         new_predef.toSet,
         Set.empty)) {
        case ((remap, preremap, predefs, defs), ((cls, body), fv)) =>
          val new_name = gensym(name + "$D")
          val new_params_list = fv.toList
          val new_params = new_params_list.map{Name(_)}
          val new_def = GODef(
            genfid(),
            new_name.str,
            isjp,
            new_params,
            resultNum,
            body)
          (remap + (((name, target.str), cls, new_name.str, new_params_list)), preremap, predefs, defs + new_def)
      }
    case Case(scrut, cases) => (Set.empty, Set.empty, Set.empty, Set.empty)
    case LetExpr(x, e1, e2) =>
      splitFunctionWhenDestructImpl(n => accu(LetExpr(x, e1, n)), e2, name, target)
    case LetJoin(jp, xs, e1, e2) =>
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defn, as, e) =>
      splitFunctionWhenDestructImpl(n => accu(LetCall(xs, defn, as, n)), e, name, target)
    }
  }

  private def splitFunctionWhenDestruct(using classes: Set[ClassInfo])(f: GODef, target: Name):
    (RawSplitRemap, RawSplitPreRemap, Set[GODef], Set[GODef]) = 
    splitFunctionWhenDestructImpl(using classes, f.params, f.resultNum, f.isjp)(x => x, f.body, f.name, target)
  

  private def findToBeSplitted(using intros: Map[Str, Intro], defs: Set[GODef])
                              (node: GONode): Set[(Str, Str)] =
    node match {
    case Result(_) => Set()
    case Jump(jp, xs) =>
      val defn = defs.find{jp.getName == _.name}.get
      val r = xs.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap {
        case ((Some(ICtor(_)), paramElim), Name(param)) if paramElim.contains(EDestruct) =>
          Some((defn.name, param))
        case x @ _ =>
          None
      }.toSet
      r
    case Case(scrut, cases) => cases.foldLeft(Set()) {
      case (accu, (cls, e)) => accu ++ findToBeSplitted(e)
    }
    case LetExpr(x, e1, e2) =>
      val intros2 = IntroductionAnalysis.getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      findToBeSplitted(using intros2, defs)(e2)
    case LetJoin(jp, xs, e1, e2) => findToBeSplitted(e1) ++ findToBeSplitted(e2)
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.expectDefn
      val intros2 = defn.activeResults.zip(xs).foldLeft(intros) { 
        case (intros, (Some(i), name)) => intros + (name.str -> i)
        case (intros, _) => intros
      }
      if (defn.activeParams.size != defn.params.size)
        throw GraphOptimizingError(f"${defn.name} has unmatched activeParams and params")
      as.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap {
        case ((Some(ICtor(_)), paramElim), Name(param)) if paramElim.contains(EDestruct) =>
          Some((defn.name, param))
        case x @ _ =>
          None
      }.toSet ++ findToBeSplitted(using intros2, defs)(e)
    }

  private def findToBeSplitted(defs: Set[GODef]): Map[Str, Set[Str]] = {
    defs.foldLeft(Map.empty){
      case (accu, defn) => 
        val tmp = findToBeSplitted(using Map(), defs)(defn.body)
        accu ++ tmp.groupMap(_._1)(_._2)
    }
  }

  private def substSplittedFunction(using sctx: Map[(Str, Str), Map[Str, (Str, Ls[Str])]],
                                          sctx2: Map[(Str, Str), (Str, Ls[Str])],
                                          intros: Map[Str, Intro])
                                   (node: GONode): GONode = node match {
    case Result(_) => node
    case Jump(defnref, as) => 
      val defn = defnref.expectDefn
      
      val candidates = as.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap { 
        case ((Some(ICtor(c)), paramElim), Name(param))
        if paramElim.contains(EDestruct) =>
          val pair = (defn.getName, param)
          if (sctx.contains(pair))
            Some((pair, c))
          else
            None
        case x @ _ =>
          None
      }

      if (candidates.nonEmpty)
        val (pair, ctor) = candidates.head
        val (new_f, new_params) = sctx(pair)(ctor)

        sctx2.get(pair) match 
          case Some((pre_f, retvals)) => 
            val new_names = retvals.map { _ => gensym() }
            val namemap = retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              Jump(GODefRef(Right(new_f)), new_params.map{x => Ref(namemap(x))}))
          case None => Jump(defnref, as) 
      else
        Jump(defnref, as)
    
    case Case(scrut, cases) => Case(scrut, cases.map {
      (cls, e) => (cls, substSplittedFunction(e))
    })
    case LetExpr(x, e1, e2) =>
      val intros2 = IntroductionAnalysis.getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      LetExpr(x, e1, substSplittedFunction(using sctx, sctx2, intros2)(e2))
    case LetJoin(jp, xs, e1, e2) => 
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.expectDefn
      val intros2 = defn.activeResults.zip(xs).foldLeft(intros) { 
        case (intros, (Some(i), name)) => intros + (name.str -> i)
        case (intros, _) => intros
      }
      if (defn.activeParams.size != defn.params.size)
        throw GraphOptimizingError(f"${defn.name} has unmatched activeParams and params")

      val candidates = as.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap { 
        case ((Some(ICtor(c)), paramElim), Name(param))
        if paramElim.contains(EDestruct) =>
          val pair = (defn.getName, param)
          if (sctx.contains(pair))
            Some((pair, c))
          else
            None
        case x @ _ =>
          None
      }

      if (candidates.nonEmpty)
        val (pair, ctor) = candidates.head
        val (new_f, new_params) = sctx(pair)(ctor)

        sctx2.get(pair) match 
          case Some((pre_f, retvals)) => 
            val new_names = retvals.map { _ => gensym() }
            val namemap = retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              LetCall(xs, GODefRef(Right(new_f)), new_params.map{x => Ref(namemap(x))},
                substSplittedFunction(using sctx, sctx2, intros2)(e)))

          case None => LetCall(xs, GODefRef(Right(new_f)), as, substSplittedFunction(using sctx, sctx2, intros2)(e))
      else
        LetCall(xs, defnref, as, substSplittedFunction(using sctx, sctx2, intros2)(e))
  }

  private def substSplittedFunctions(using sctx: Map[(Str, Str), Map[Str, (Str, Ls[Str])]],
                                           sctx2: Map[(Str, Str), (Str, Ls[Str])])
                                    (defs: Set[GODef]): Set[GODef] = {
    defs.map(defn => 
      val new_body = substSplittedFunction(using sctx, sctx2, Map.empty)(defn.body)
      GODef(
        defn.id,
        defn.name,
        defn.isjp, 
        defn.params,
        defn.resultNum,
        new_body,
    )) 
  }

  def splitFunction(prog: GOProgram): GOProgram = {
    val classes = prog.classes
    val defs = prog.defs
    val main = prog.main
    val workset: Map[Str, Set[Str]] = findToBeSplitted(defs)
    var rawremap: RawSplitRemap = Set.empty
    var rawpreremap: RawSplitPreRemap = Set.empty
    var predefs: Set[GODef] = Set.empty
    val newdefs = defs.flatMap {
      case defn if workset.contains(defn.name) => workset(defn.name).flatMap {
        param => 
          val (r, pr, p, d) = splitFunctionWhenDestruct(using classes)(defn, Name(param))
          rawremap = rawremap ++ r
          rawpreremap = rawpreremap ++ pr
          predefs = predefs ++ p
          d
      }
      case _ => Ls()
    }
    val remap = rawremap.groupMap(_._1){x => (x._2, x._3, x._4)}.map {
      case (k, v) => (k, v.groupMap(_._1)(x => (x._2, x._3)).map {
        case (k2, v2) => (k2.ident, v2.head)
      })
    }
    val preremap = rawpreremap.groupMap(_._1){x => (x._2, x._3)}.map {
      case (k, v) => (k, v.head)
    }
    val defs2 = substSplittedFunctions(using remap, preremap)(defs) ++ newdefs ++ predefs
    fixCrossReferences(main, defs2)
    validate(main, defs2)
    GOProgram(classes, defs2, main)
  }

  private def findToBeReplaced(using intros: Map[Str, Intro])
                              (defn: GONode): Set[(Str, (Str, Ls[Str]))] = defn match {
    case Result(_) => Set()
    case Jump(defnref, as) =>
      val defn = defnref.expectDefn
      as.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap {
        case ((Some(ICtor(_)), paramElim), Name(param)) if paramElim.exists(isESelect)
          && !paramElim.contains(EDirect) =>
          Some(defn.name, (param, paramElim.filter(isESelect).toList.map {
            case ESelect(x) => x
            case _ => ??? // unreachable
          }))
        case ((intro, elims), Name(param)) =>
          None
      }.toSet
    case Case(scrut, cases) => cases.foldLeft(Set()) {
      case (accu, (cls, e)) => accu ++ findToBeReplaced(e)
    }
    case LetExpr(x, e1, e2) =>
      val intros2 = IntroductionAnalysis.getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      findToBeReplaced(using intros2)(e2)
    case LetJoin(jp, xs, e1, e2) => findToBeReplaced(e1) ++ findToBeReplaced(e2)
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.expectDefn
      val intros2 = defn.activeResults.zip(xs).foldLeft(intros) { 
        case (intros, (Some(i), name)) => intros + (name.str -> i)
        case (intros, _) => intros
      }
      as.map {
        case Ref(Name(s)) => intros.get(s)
        case _ => None
      }.zip(defn.activeParams).zip(defn.params).flatMap {
        case ((Some(ICtor(_)), paramElim), Name(param)) if paramElim.exists(isESelect)
          && !paramElim.contains(EDirect) =>
          Some(defn.name, (param, paramElim.filter(isESelect).toList.map {
            case ESelect(x) => x
            case _ => ??? // unreachable
          }))
        case ((intro, elims), Name(param)) =>
          None
      }.toSet ++ findToBeReplaced(using intros2)(e)
  }

  private def findToBeReplaced(prog: GOProgram): Map[Str, Set[(Str, Ls[Str])]] = {
    prog.defs.foldLeft(Map.empty) {
      (accu, defn) => 
        accu ++ findToBeReplaced(using Map())(defn.body).groupMap(_._1)(_._2)  
    }
  }

  private def repScalarName(target: Str, field: Str) = {
    Name(s"${target}_$field")
  }

  private def replaceScalarArgumentImpl(body: GONode, target: Str): GONode = body match {
    case Result(_xs) => body
    case Jump(_jp, _xs) => body
    case Case(scrut, cases) => Case(scrut, cases map {
      (cls, e) => (cls, replaceScalarArgumentImpl(e, target))
    })
    case LetExpr(x, Select(y,  cls, field), e2) if y.str == target =>
      LetExpr(x, Ref(repScalarName(target, field)), replaceScalarArgumentImpl(e2, target))  
    case LetExpr(x, e1, e2) =>
      LetExpr(x, e1, replaceScalarArgumentImpl(e2, target))
    case LetJoin(jp, xs, e1, e2) =>
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defn, as, e) =>
      LetCall(xs, defn, as, replaceScalarArgumentImpl(e, target))
  }

  private def isESelect(elim: Elim) = elim match {
    case ESelect(_) => true
    case _ => false
  }

  private def targetReplacedScalarNames(targets: Map[Str, Set[Str]]) =
    targets.flatMap { (k, fields) => fields.map { x => repScalarName(k, x) } }

  private def newParamsForRepScalarArgs(params: Ls[Name], targets: Map[Str, Set[Str]]) =
    params.filter(x => !targets.contains(x.str)) ++ targetReplacedScalarNames(targets)

  private enum ParamSubst:
    case ParamKeep
    case ParamFieldOf(orig: Str, field: Str)

  import ParamSubst._

  private def revMapForRepScalarArgs(params: Ls[Name], targets: Map[Str, Set[Str]]) =
    params.flatMap { 
      case x if targets.contains(x.str) => None
      case x => Some(x.str -> ParamKeep)
    }.toMap ++ targets.flatMap {
      (k, fields) => fields.map { x => repScalarName(k, x).str -> ParamFieldOf(k, x) }
    }.toMap

  private def replaceScalarArguments(new_name: Str, defn: GODef, targets: Map[Str, Set[Str]]): GODef = {
    val new_params = newParamsForRepScalarArgs(defn.params, targets) 
    val new_body = targets.foldLeft(defn.body) {
      case (body, (target, _)) => replaceScalarArgumentImpl(body, target)
    }
    
    GODef(
      genfid(),
      new_name,
      defn.isjp, 
      new_params,
      defn.resultNum,
      new_body,
    )
  }

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private def substCallOfRepScalarArg(using namemap: Map[Str, Str], fldctx: FieldCtx, workset: Map[Str, Map[Str, Set[Str]]], sctx: Map[(Str, Str), Str])
                                     (node: GONode) : GONode = node match {
    case Result(_) => node
    case Jump(defnref, as) => 
      val defn = defnref.expectDefn
      if (namemap.contains(defn.name)) {
        val new_name = namemap(defn.name)
        if (!workset.contains(defn.name))
          throw GraphOptimizingError(f"name map contains ${defn.name} -> $new_name but workset doesn't")
        val targets = workset(defn.name)
        val rev_map: Map[Str, ParamSubst] = revMapForRepScalarArgs(defn.params, targets)
        val new_params = newParamsForRepScalarArgs(defn.params, targets)
        val old_map: Map[Str, TrivialExpr] = defn.params.map(_.str).zip(as).toMap

        var rbind: Map[(Str, Str), Str] = Map.empty
        val new_bindings: Ls[(Name, (Str, Str))] = new_params.flatMap {
          param => rev_map(param.str) match {
            case ParamKeep => None
            case ParamFieldOf(orig, str) =>
              val orig_arg = expectTexprIsRef(old_map(orig)).str
              sctx.get((orig_arg, str)) match {
                case Some(x) => None
                case None =>
                  val v = gensym()
                  rbind = rbind + ((orig_arg, str) -> v.str)
                  Some(v -> (orig_arg, str))
              }
          }
        }

        val new_sctx = sctx ++ rbind

        val new_args: Ls[TrivialExpr] = new_params.map {
          param => rev_map(param.str) match {
            case ParamKeep => old_map(param.str)
            case ParamFieldOf(orig, str) =>
              val orig_arg = expectTexprIsRef(old_map(orig)).str
              new_sctx.get((orig_arg, str)) match {
              case Some(x) => Ref(Name(x))
              case None => ???
            }
          }
        }

        val new_node = Jump(GODefRef(Right(new_name)), new_args)

        val final_node = new_bindings.foldRight(new_node) {
          case ((x, (y, field)), node) => LetExpr(x, Select(Name(y), fldctx(field)._2, field), node)
        }

        final_node
      } else node
    case Case(scrut, cases) => Case(scrut, cases.map {
      (cls, e) => (cls, substCallOfRepScalarArg(e))
    })
    case LetExpr(x, e1, e2) =>
      LetExpr(x, e1, substCallOfRepScalarArg(e2))
    case LetJoin(jp, xs, e1, e2) => 
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.expectDefn
      if (namemap.contains(defn.name)) {
        val new_name = namemap(defn.name)
        if (!workset.contains(defn.name))
          throw GraphOptimizingError(f"name map contains ${defn.name} -> $new_name but workset doesn't")
        val targets = workset(defn.name)
        val rev_map: Map[Str, ParamSubst] = revMapForRepScalarArgs(defn.params, targets)
        val new_params = newParamsForRepScalarArgs(defn.params, targets)
        val old_map: Map[Str, TrivialExpr] = defn.params.map(_.str).zip(as).toMap

        var rbind: Map[(Str, Str), Str] = Map.empty
        val new_bindings: Ls[(Name, (Str, Str))] = new_params.flatMap {
          param => rev_map(param.str) match {
            case ParamKeep => None
            case ParamFieldOf(orig, str) =>
              val orig_arg = expectTexprIsRef(old_map(orig)).str
              sctx.get((orig_arg, str)) match {
                case Some(x) => None
                case None =>
                  val v = gensym()
                  rbind = rbind + ((orig_arg, str) -> v.str)
                  Some(v -> (orig_arg, str))
              }
          }
        }

        val new_sctx = sctx ++ rbind

        val new_args: Ls[TrivialExpr] = new_params.map {
          param => rev_map(param.str) match {
            case ParamKeep => old_map(param.str)
            case ParamFieldOf(orig, str) =>
              val orig_arg = expectTexprIsRef(old_map(orig)).str
              new_sctx.get((orig_arg, str)) match {
              case Some(x) => Ref(Name(x))
              case None => ???
            }
          }
        }

        val new_node = LetCall(xs, GODefRef(Right(new_name)), new_args, substCallOfRepScalarArg(using namemap, fldctx, workset, new_sctx)(e))

        val final_node = new_bindings.foldRight(new_node) {
          case ((x, (y, field)), node) => LetExpr(x, Select(Name(y), fldctx(field)._2, field), node)
        }

        final_node
      } else node
  }

  private def substCallOfRepScalarArgOnDef(using namemap: Map[Str, Str], fldctx: FieldCtx, workset: Map[Str, Map[Str, Set[Str]]])(defn: GODef) =
    GODef(
      defn.id,
      defn.name,
      defn.isjp, 
      defn.params,
      defn.resultNum,
      substCallOfRepScalarArg(using namemap, fldctx, workset, Map.empty)(defn.body),
    )

  def replaceScalar(prog: GOProgram): GOProgram = {
    val classes = prog.classes
    val defs: Set[GODef] = prog.defs
    val main = prog.main
    val init: Set[GODef] = Set()
    val rawworkset: Map[Str, Set[(Str, Ls[Str])]] = findToBeReplaced(prog)
    val workset: Map[Str, Map[Str, Set[Str]]] = rawworkset.map { 
      case (defname, s) => (defname, s.flatMap { (param, fields) => fields.map { x => (param, x) }}.groupMap(_._1)(_._2))
    }
    val namemap = defs.flatMap {
      // case defn if defn.isjp => None
      case defn if workset.contains(defn.name) => Some(defn.name -> gensym(defn.name + "$S").str)
      case _ => None
    }.toMap

    val defs2 = defs.flatMap {
      // case defn if defn.isjp => None
      case defn =>
        workset.get(defn.name).map {
          targets => replaceScalarArguments(namemap(defn.name), defn, targets)
        }
    }

    val cls = prog.classes
    val clsctx: ClassCtx = cls.map{ case ClassInfo(_, name, _) => name }.zip(cls).toMap
    val fldctx: FieldCtx = cls.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
    val new_defs = defs.map {
      defn => substCallOfRepScalarArgOnDef(using namemap, fldctx, workset)(defn)
    }

    val defs3 = new_defs ++ defs2
    fixCrossReferences(main, defs3)
    validate(main, defs3)
    GOProgram(classes, defs3, main)
  }

  private class TrivialBindingSimplification extends GOTrivialExprVisitor, GOVisitor:
    var rctx: Map[Str, TrivialExpr] = Map.empty
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(x => { rctx = Map.empty; x.accept_visitor(this)})
      fixCrossReferences(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)
    override def visit(node: LetExpr) = node match
      case LetExpr(x, Ref(Name(z)), e2) if rctx.contains(z) =>
        rctx = rctx + (x.str -> rctx(z))
        e2.accept_visitor(this)
      case LetExpr(x, y @ Ref(Name(_)), e2) =>
        rctx = rctx + (x.str -> y)
        e2.accept_visitor(this)
      case LetExpr(x, y @ Literal(_), e2) =>
        rctx = rctx + (x.str -> y)
        e2.accept_visitor(this)
      case LetExpr(x, e1, e2) =>
        LetExpr(x, e1.accept_visitor(this), e2.accept_visitor(this))
    override def visit(y: Ref) = y match
      case Ref(Name(x)) if rctx.contains(x) =>
        rctx(x)
      case _ => y
    override def visit_name_use(z: Name) =
      val Name(x) = z
      rctx.get(x) match 
        case Some(Ref(yy @ Name(y))) => yy
        case _ => z


  private class SelectSimplification extends GOVisitor:
    var cctx: Map[Str, Map[Str, TrivialExpr]] = Map.empty
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.accept_visitor(this)})
      fixCrossReferences(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)
    override def visit(node: LetExpr) = node match
      case LetExpr(x, sel @ Select(y, cls, field), e2) if cctx.contains(y.str) =>
        cctx.get(y.str) match
          case Some(m) =>
            m.get(field) match 
              case Some(v) =>
                LetExpr(x, v.to_expr, e2.accept_visitor(this)) 
              case None => 
                LetExpr(x, sel, e2.accept_visitor(this))
          case None => LetExpr(x, sel, e2.accept_visitor(this))
      case LetExpr(x, y @ CtorApp(cls, args), e2) =>
        val m = cls.fields.zip(args).toMap
        cctx = cctx + (x.str -> m)
        LetExpr(x, y, e2.accept_visitor(this))
      case LetExpr(x, e1, e2) =>
        LetExpr(x, e1.accept_visitor(this), e2.accept_visitor(this))

  private def argsToStrs(args: Ls[TrivialExpr]) = {
    args.flatMap {
      case Ref(x) => Some(x.str)
      case _ => None
    }
  }

  private class UsefulnessAnalysis extends GOIterator:
    val uses = MutHMap[Name, Int]() 
    override def iterate_name_use(x: Name) =
      uses.update(x, uses.getOrElse(x, 0) + 1)
    override def iterate(x: GOProgram) =
      val defs = GODefRevPreOrdering.ordered(x.main, x.defs)
      defs.foreach(_.accept_iterator(this))

  private class DeadCodeElimination extends GOVisitor:
    val ua = UsefulnessAnalysis()
    override def visit(y: LetExpr) = y match
      case LetExpr(x, e1, e2) =>
        ua.uses.get(x) match
          case Some(_) =>
            LetExpr(x, e1, e2.accept_visitor(this)) 
          case None =>
            e2.accept_visitor(this)

    override def visit(x: GOProgram) =
      x.accept_iterator(ua)
      val defs = GODefRevPreOrdering.ordered(x.main, x.defs)
      val new_defs = defs.map(_.accept_visitor(this)).toSet
      fixCrossReferences(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

  private class RemoveTrivialCallAndJump extends GOVisitor:
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(_.accept_visitor(this))
      fixCrossReferences(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)
    override def visit(x: Jump) = x match
      case Jump(defnref, xs) =>
        tryGetDefn(defnref) match {
          case Some(defn) =>
            val parammap = defn.params.zip(xs).toMap
            val trivial = defn.body match {
              case Result(ys) => Some(ys)
              case _ => None
            }
            if (trivial == None) return x

            val retvals = trivial.get
            
            val ys = retvals.map { retval => retval match
              case Literal(lit) => retval
              case Ref(x) if parammap.contains(x) => parammap(x)
              case _ => retval
            }

            Result(ys)
          case _ => x
        }

    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        val trivial = defn.body match {
          case Result(ys) => Some(ys)
          case _ => None
        }
        if (trivial == None)
          return LetCall(xs, defnref, as, e.accept_visitor(this))

        val retvals = trivial.get
        val parammap = defn.params.zip(as).toMap

        if (retvals.length != xs.length)
          throw GraphOptimizingError("inconsistent results number")
        
        val init = e.accept_visitor(this) 

        xs.zip(retvals).foldRight(init){
          case ((name, retval), node) =>
            retval match {
              case Literal(lit) => LetExpr(name, retval.to_expr , node)
              case Ref(x) if parammap.contains(x) =>
                LetExpr(name, parammap(x).to_expr, node)
              case _ =>
                LetExpr(name, retval.to_expr, node)
            }
        }

  private class RemoveDeadDefn() extends GOVisitor:
    override def visit(x: GOProgram) =
      val defs = x.defs
      val entry = x.main
      var visited = GODefRevPostOrdering.ordered_names(entry, defs).toSet
      val new_defs = defs.filter(x => visited.contains(x.name))
      defs.foreach {
        case x if new_defs.find{_.name == x.name} == None => // println(s"${x.name} removed")
        case _ =>
      }
      fixCrossReferences(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

  def simplifyProgram(prog: GOProgram): GOProgram = {
    var changed = true
    var s = prog
    while (changed) {
      val ss = SelectSimplification()
      val tbs = TrivialBindingSimplification()
      val rtcj = RemoveTrivialCallAndJump()
      val dce = DeadCodeElimination()
      val rdd = RemoveDeadDefn()
      val s0 = s.accept_visitor(ss)
      val s1 = s0.accept_visitor(tbs)
      val s2 = s1.accept_visitor(rtcj)
      val s3 = s2.accept_visitor(dce)
      val s4 = s3.accept_visitor(rdd)
      val sf = s4
      validate(sf.main, sf.defs)
      changed = s.defs != sf.defs
      s = sf
    }
    s
  }

  private class PromoteJoinPoints extends GOIterator, GOVisitor:
    var accu: Ls[GODef] = Nil
    override def iterate(x: LetJoin) = x match
      case LetJoin(Name(jp), xs, e1, e2) => 
        val new_def = GODef(
          genfid(), jp,
          true, xs, 1,
          e1,
        )
        e1.accept_iterator(this)
        accu = new_def :: accu
        e2.accept_iterator(this)
    override def visit(x: LetJoin) = x match
      case LetJoin(Name(jp), xs, e1, e2) => e2.accept_visitor(this)
    override def visit(x: GOProgram) = {
      val classes = x.classes
      val defs = x.defs
      val main = x.main

      defs.foreach(_.body.accept_iterator(this))

      val defs2 = defs ++ accu
      val defs3 = defs2.map(_.accept_visitor(this)) 

      fixCrossReferences(main, defs3)
      validate(main, defs3)
      GOProgram(classes, defs3, main)
    }

  def promoteJoinPoints(prog: GOProgram): GOProgram =
    prog.accept_visitor(PromoteJoinPoints())

  private class DefRefInSet(defs: Set[GODef]) extends GOIterator:
    override def iterate(x: LetCall) = x match
      case LetCall(res, defnref, args, body) =>
        tryGetDefn(defnref) match {
          case Some(real_defn) => if (!defs.exists(_ eq real_defn)) throw GraphOptimizingError("ref is not in the set")
          case _ =>
        }
        body.accept_iterator(this)

  private object ParamsArgsAreConsistent extends GOIterator:
    override def iterate(x: LetCall) = x match
      case LetCall(res, defnref, args, body) => 
        tryGetDefn(defnref) match {
          case Some(real_defn) =>
            if (real_defn.params.length != args.length) 
              val x = real_defn.params.length
              val y = args.length
              throw GraphOptimizingError(s"inconsistent arguments($y) and parameters($x) number in a call to ${real_defn.name}")
          case _ =>
        }
    override def iterate(x: Jump) = x match
      case Jump(defnref, xs) => 
        tryGetDefn(defnref) match {
          case Some(jdef) =>
            val x = xs.length
            val y = jdef.params.length
            if (x != y)
              throw GraphOptimizingError(s"inconsistent arguments($x) and parameters($y) number in a jump to ${jdef.getName}")
          case _ =>
        }

  private class NoVarShadowing extends GOIterator:
    val ctx = MutSet[Str]()
    override def iterate_param(x: Name) =
      if (ctx(x.str))
        throw GraphOptimizingError(s"parameter shadows $x")
      else
        ctx += x.str
    override def iterate_name_def(x: Name) = 
      if (ctx(x.str))
        throw GraphOptimizingError(s"name def shadows $x")
      else
        ctx += x.str

  private def ensureDefRefInSet(defs: Set[GODef]): Unit =
    val it = DefRefInSet(defs)
    defs.foreach { _.body.accept_iterator(it) }

  private def ensureParamsArgsConsistent(defs: Set[GODef]): Unit =
    val it = ParamsArgsAreConsistent
    defs.foreach { _.body.accept_iterator(it) }
  
  private def ensureVarNoShadowing(entry: GONode, defs: Set[GODef]): Unit =
    val it = NoVarShadowing()
    val defs2 = GODefRevPostOrdering.ordered(entry, defs)
    defs2.foreach { _.body.accept_iterator(it) }

  private def validate(entry: GONode, defs: Set[GODef], cross_ref_is_ok: Bool = true): Unit =
    ensureDefRefInSet(defs)
    ensureParamsArgsConsistent(defs)
    if (cross_ref_is_ok)
       ensureVarNoShadowing(entry, defs)

  def activeAnalyze(prog: GOProgram): GOProgram =
    prog.accept_iterator(EliminationAnalysis())
    prog.accept_iterator(IntroductionAnalysis)
    prog

  def optimize(prog: GOProgram): GOProgram = {
    val g1 = simplifyProgram(prog)
    val g2 = activeAnalyze(g1)

    val g3 = splitFunction(g2)
    
    val g4 = simplifyProgram(g3)
    val g5 = activeAnalyze(g4)
    
    val g6 = replaceScalar(g5)
    
    val g7 = simplifyProgram(g6)
    val g8 = activeAnalyze(g7)
    g8
  }
