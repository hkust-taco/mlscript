package mlscript.compiler

import mlscript.*
import mlscript.compiler.*
import mlscript.utils.*
import shorthands.*

import scala.annotation.tailrec
import scala.collection.immutable.*
final case class GraphOptimizingError(message: String) extends Exception(message)

class GraphOptimizer:
  private type Ctx = Map[Str, Name]
  private type ClassCtx = Map[Str, ClassInfo]
  private type FieldCtx = Map[Str, (Str, ClassInfo)]
  private type FnCtx = Set[Str]
  private type OpCtx = (Unit, Set[Str])
  
  import GOExpr._
  import Node._

  var count = 0
  private def gensym(s: Str = "x") = {
    val tmp = s"$s$count"
    count += 1
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
  private final val unexpected_node = (x: Node) => throw GraphOptimizingError(s"unsupported node $x")
  private final val unexpected_term = (x: Term) => throw GraphOptimizingError(s"unsupported term $x")

  private def buildBinding
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (name: Str, e: Term, body: Term)
    (k: Node => Node): Node =
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
    (tup: Tup)(k: Node => Node): Node =
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
    (tm: Term)(k: Node => Node): Node =
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
              case Result(xs) => Jump(jp, xs)
              case node @ _ => node |> unexpected_node
            }
            val fls2 = buildResultFromTerm(fls) {
              case Result(xs) => Jump(jp, xs)
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
            val cases: Ls[(ClassInfo, Node)] = lines map {
              case L(IfThen(App(Var(ctor), params: Tup), rhs)) =>
                clsctx(ctor) -> {
                  // need this because we have built terms (selections in case arms) containing names that are not in the original term
                  given Ctx = ctx + (scrut.str -> scrut) 
                  buildResultFromTerm(
                    bindingPatternVariables(scrut.str, params, clsctx(ctor), rhs)) {
                      case Result(xs) => Jump(jp, xs)
                      case node @ _ => node |> unexpected_node
                    }
                }
              case L(IfThen(Var(ctor), rhs)) =>
                clsctx(ctor) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(jp, xs)
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

  private def fixNode(using defs: Set[GODef])(node: Node): Unit = node match {
    case Case(_, cases) => cases.foreach { case (cls, node) => (cls, fixNode(node)) }
    case lc @ LetCall(resultNames, defnref, args, body) =>
      val target = defnref.defn match {
        case Left(defn) => defs.find{_.getName == defn.name}.get
        case Right(name) => defs.find{_.getName == name}.get
      }
      defnref.defn = Left(target)
      fixNode(body)
    case LetExpr(name, expr, body) => fixNode(body)
    case LetJoin(joinName, params, rhs, body) => fixNode(body)
    case Result(_) =>
    case Jump(_, _) =>
  }

  private def fixGODef(using defs: Set[GODef]): Unit =
    defs.foreach { defn => 
      fixNode(using defs)(defn.body)
    }

  private def buildDefFromNuFunDef
    (using ctx: Ctx, clsctx: ClassCtx, fldctx: FieldCtx, fnctx: FnCtx, opctx: OpCtx)
    (nfd: Statement): GODef = nfd match
    case NuFunDef(_, Var(name), None, Nil, L(Lam(Tup(fields), body))) =>
      val strs = fields map {
          case N -> Fld(FldFlags.empty, Var(x)) => x
          case _ => throw GraphOptimizingError("unsupported field") 
        }
      val names = strs.map { x => Name(x) }
      given Ctx = ctx ++ strs.zip(strs.map { x => Name(x) })
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

      val ops = Set("+", "-")
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
      
      fixGODef(using defs)
      validate(defs)
      GOProgram(clsinfo, defs, main)

  // --------------------------------

  import Elim._
  import Intro._

  private type JpCtx = Map[Str, GODef]

  private def appendCtx(ctx: Ctx, x: String, y: Name) = {
    ctx.get(y.str) match {
      case Some(z) => ctx + (x -> z)
      case None => ctx + (x -> y)
    }
  }

  private def used(using v: String, ctx: Ctx)(name: String) =
    name == v || ctx.get(name).contains(v)

  private def getElims(using v: String, ctx: Ctx, jpctx: JpCtx)(exprs: Ls[TrivialExpr], uses: Set[Elim]): Set[Elim] =
    exprs.foldLeft(uses)((uses, expr) => getElim(expr, uses))

  private def getElim(using v: String, ctx: Ctx, jpctx: JpCtx)(expr: TrivialExpr, uses: Set[Elim]): Set[Elim] = expr match {
    case Literal(lit) => uses
    case Ref(name) => if (name.str == v || ctx.get(name.str).contains(v)) uses + EDirect else uses
  }

  private def getElim(using v: String, ctx: Ctx, jpctx: JpCtx)(expr: GOExpr, uses: Set[Elim]): Set[Elim] = expr match {
    case Apply(name, args) => args.foldLeft(
        if (used(name.str)) uses + EApp(args.length) else uses
      )((uses, expr) => getElim(expr, uses))
    case BasicOp(name, args) => getElims(args, uses)
    case CtorApp(name, args) => getElims(args, uses)
    case Lambda(name, body) => getElim(body, uses)
    case Literal(lit) => uses
    case Ref(name) => if (used(name.str)) uses + EDirect else uses
    case Select(name, cls, field) => if (used(name.str)) uses + ESelect(field) else uses
  }

  private def bindArguments(ctx: Ctx, args: Ls[TrivialExpr], params: Ls[Name]): Ctx =
    args.zip(params).foldLeft(ctx) {
      case (ctx, (Ref(n1), n2)) => ctx + (n1.str -> n2)
      case _ => ctx
    }

  private def getElim(using v: String, ctx: Ctx, jpctx: JpCtx)(node: Node, uses: Set[Elim]): Set[Elim] = node match {
    case Case(scrut, cases) if used(scrut.str) =>
      cases.foldLeft(uses)((uses, arm) => getElim(arm._2, uses + EDestruct + EDirect))
    case Case(scrut, cases) =>
      cases.foldLeft(uses)((uses, arm) => getElim(arm._2, uses))
    case Jump(joinName, args) => 
      val elims = getElims(args, uses)
      val jp = jpctx(joinName.str)
      val new_ctx = bindArguments(ctx, args, jp.params)
      elims ++ getElim(using v, new_ctx, jpctx)(jp.body, uses)
    case LetCall(resultNames, defn, args, body) =>
      val elims = getElims(args, uses)
      val defn2 = defn.defn match {
        case Left(x) => x
        case Right(_) => throw GraphOptimizingError("only get the name of definition")
      }
      val backward_elims = args.zip(defn2.activeParams).flatMap {
        case (Ref(Name(x)), ys) if x == v => Some(ys)
        case _ => None
      }
      getElim(body, backward_elims.foldLeft(elims)((x, y) => x ++ y))
    case LetExpr(name, Ref(y), body) => 
      given Ctx = appendCtx(ctx, name.str, y)
      getElim(body, uses)
    case LetExpr(name, expr, body) => getElim(body, getElim(expr, uses))
    case LetJoin(joinName, params, rhs, body) => getElim(body, getElim(rhs, uses))
    case Result(res) => getElims(res, uses)
  }


  private def getIntro(defn: GODef): Ls[Opt[Intro]] =
    defn.activeResults

  private def getIntro(using jpctx: JpCtx)(node: Node, intros: Map[Str, Intro]): Ls[Opt[Intro]] = node match {
    case Case(scrut, cases) => 
      val cases_intros = cases.map { case (cls, node) => getIntro(node, intros) }
      if (cases_intros.toSet.size > 1)
        cases_intros.head.map { _ => None }
      else
        cases_intros.head
    case Jump(joinName, args) =>
      val jpdef = jpctx(joinName.str)
      val params = jpdef.params
      val node = jpdef.body
      val intros2 = params.zip(args).filter{
        case (_, arg) => getIntro(arg, intros).isDefined
      }.map{
        case (param, arg) => 
          val kv = param.str -> getIntro(arg, intros).get
          kv
      }
      getIntro(node, intros2.toMap)
    case LetCall(resultNames, defnref, args, body) =>
      val defn = defnref.defn match {
        case Left(value) => value
        case Right(value) => throw GraphOptimizingError("only get the name of definition")
      }
      val intros2 = getIntro(defn).zip(resultNames).foldLeft(intros) { 
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
  }

  private def getIntro(expr: TrivialExpr, intros: Map[Str, Intro]) = expr match {
    case Literal(lit) => None
    case Ref(name) => intros.get(name.str)
  }

  private def getIntro(expr: GOExpr, intros: Map[Str, Intro]): Opt[Intro] = expr match {
    case CtorApp(cls, args) => Some(ICtor(cls.ident))
    case Lambda(name, body) => Some(ILam(name.length))
    case _ => None
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

  private def freeVarAnalysis(using ctx: Set[Str])(body: Node, fv: Set[Str], fj: Set[Str]): (Set[Str], Set[Str])
    = body match {
    case Result(xs) => (fv ++ xs.flatMap {
      case Ref(Name(s)) if !ctx.contains(s) => Some(s)
      case _ => None
    }, fj)
    case Jump(Name(jp), _) =>
      (fv, if (ctx.contains(jp)) fj else fj + jp )
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
  
  private def splitFunctionWhenDestructImpl(using jpctx: JpCtx, classes: Set[ClassInfo],
                                                  params: Ls[Name], resultNum: Int)
  (accu: Node => Node, body: Node, name: Str, target: Name):
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
        val new_predef_name = gensym(name + "@pre@")
        val new_predef = GODef(
          genfid(),
          new_predef_name.str,
          false,
          params,
          allfv.size,
          accu(Result(retvals)))
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
          val new_name = gensym(name + "@destruct@")
          val new_params_list = fv.toList
          val new_params = new_params_list.map{Name(_)}
          val new_def = GODef(
            genfid(),
            new_name.str,
            false,
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
    splitFunctionWhenDestructImpl(using Map(), classes, f.params, f.resultNum)(x => x, f.body, f.name, target)
  

  private def findToBeSplitted(using intros: Map[Str, Intro])
                              (node: Node): Set[(Str, Str)] =
    node match {
    case Result(_) => Set()
    case Jump(_jp, _xs) => Set()
    case Case(scrut, cases) => cases.foldLeft(Set()) {
      case (accu, (cls, e)) => accu ++ findToBeSplitted(e)
    }
    case LetExpr(x, e1, e2) =>
      val intros2 = getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      findToBeSplitted(using intros2)(e2)
    case LetJoin(jp, xs, e1, e2) => findToBeSplitted(e1) ++ findToBeSplitted(e2)
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.defn match {
          case Left(value) => value
          case Right(value) => throw GraphOptimizingError("only has the name of definition")
        }
      val intros2 = getIntro(defn).zip(xs).foldLeft(intros) { 
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
      }.toSet ++ findToBeSplitted(using intros2)(e)
    }

  private def findToBeSplitted(defs: Set[GODef]): Map[Str, Set[Str]] = {
    defs.foldLeft(Map.empty){
      case (accu, defn) => 
        val tmp = findToBeSplitted(using Map())(defn.body)
        accu ++ tmp.groupMap(_._1)(_._2)
    }
  }

  private def substSplittedFunction(using sctx: Map[(Str, Str), Map[Str, (Str, Ls[Str])]],
                                          sctx2: Map[(Str, Str), (Str, Ls[Str])],
                                          intros: Map[Str, Intro])
                                   (node: Node): Node = node match {
    case Result(_) => node
    case Jump(_, _) => node
    case Case(scrut, cases) => Case(scrut, cases.map {
      (cls, e) => (cls, substSplittedFunction(e))
    })
    case LetExpr(x, e1, e2) =>
      val intros2 = getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      LetExpr(x, e1, substSplittedFunction(using sctx, sctx2, intros2)(e2))
    case LetJoin(jp, xs, e1, e2) => 
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.defn match {
          case Left(value) => value
          case Right(value) => throw GraphOptimizingError("only has the name of definition")
      }

      val intros2 = getIntro(defn).zip(xs).foldLeft(intros) { 
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
    fixGODef(using defs2)
    validate(defs2)
    GOProgram(classes, defs2, main)
  }

  private def findToBeReplaced(using intros: Map[Str, Intro])
                              (defn: Node): Set[(Str, (Str, Ls[Str]))] = defn match {
    case Result(_) => Set()
    case Jump(_jp, _xs) => Set() // resultNum: fix it
    case Case(scrut, cases) => cases.foldLeft(Set()) {
      case (accu, (cls, e)) => accu ++ findToBeReplaced(e)
    }
    case LetExpr(x, e1, e2) =>
      val intros2 = getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
      findToBeReplaced(using intros2)(e2)
    case LetJoin(jp, xs, e1, e2) => findToBeReplaced(e1) ++ findToBeReplaced(e2)
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.defn match {
          case Left(value) => value
          case Right(value) => throw GraphOptimizingError("only has the name of definition")
      }
      val intros2 = getIntro(defn).zip(xs).foldLeft(intros) { 
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

  private def replaceScalarArgumentImpl(using jpctx: JpCtx)(body: Node, target: Str): Node = body match {
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
      case (body, (target, _)) => replaceScalarArgumentImpl(using Map())(body, target)
    }
    
    GODef(
      genfid(),
      new_name,
      false, 
      new_params,
      1,
      new_body,
    )
  }

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private def substCallOfRepScalarArg(using namemap: Map[Str, Str], fldctx: FieldCtx, workset: Map[Str, Map[Str, Set[Str]]], sctx: Map[(Str, Str), Str])
                                     (node: Node) : Node = node match {
    case Result(_) => node
    case Jump(_jp, _xs) => node
    case Case(scrut, cases) => Case(scrut, cases.map {
      (cls, e) => (cls, substCallOfRepScalarArg(e))
    })
    case LetExpr(x, e1, e2) =>
      LetExpr(x, e1, substCallOfRepScalarArg(e2))
    case LetJoin(jp, xs, e1, e2) => 
      throw GraphOptimizingError("join points after promotion")
    case LetCall(xs, defnref, as, e) =>
      val defn = defnref.defn match {
          case Left(value) => value
          case Right(value) => throw GraphOptimizingError("only has the name of definition")
      }
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
      case defn if workset.contains(defn.name) => Some(defn.name -> gensym(defn.name + "@select@").str)
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
    fixGODef(using defs3)
    validate(defs3)
    GOProgram(classes, defs3, main)
  }

  private def simplifyTrivialBinding(using rctx: Map[Str, TrivialExpr])(name: Name): Name =
    val Name(x) = name
    rctx.get(x).map { 
      case Ref(yy @ Name(y)) => yy
      case _ => name
    }.getOrElse(name)

  private def simplifyTrivialBindingOfTexpr(using rctx: Map[Str, TrivialExpr])(expr: TrivialExpr): TrivialExpr = expr match {
    case Ref(Name(x)) if rctx.contains(x) => rctx(x)
    case _ => expr
  }

  private def simplifyTrivialBinding(using rctx: Map[Str, TrivialExpr])(expr: GOExpr): GOExpr = expr match {
    case Apply(name, args) => Apply(simplifyTrivialBinding(name), args map simplifyTrivialBindingOfTexpr)
    case BasicOp(name, args) => BasicOp(name, args map simplifyTrivialBindingOfTexpr)
    case CtorApp(name, args) => CtorApp(name, args map simplifyTrivialBindingOfTexpr)
    case Lambda(name, body) => Lambda(name, simplifyTrivialBinding(body))
    case Select(name, cls, field) => Select(simplifyTrivialBinding(name), cls, field) 
    case Ref(Name(x)) if rctx.contains(x) => rctx(x) match {
      case x: GOExpr => x
    }
    case _ => expr
  }

  private def simplifyTrivialBinding(using rctx: Map[Str, TrivialExpr])(node: Node): Node = node match {
    case Result(xs) => Result(xs map simplifyTrivialBindingOfTexpr)
    case Jump(jp, xs) => Jump(simplifyTrivialBinding(jp), xs map simplifyTrivialBindingOfTexpr )
    case Case(scrut, cases) => Case(simplifyTrivialBinding(scrut), cases map {
      (cls, e) => (cls, simplifyTrivialBinding(e))
    })
    case LetExpr(x, Ref(Name(z)), e2) if rctx.contains(z) =>
      val rctx2 = rctx + (x.str -> rctx(z))
      simplifyTrivialBinding(using rctx2)(e2)
    case LetExpr(x, y @ Ref(Name(_)), e2) =>
      val rctx2 = rctx + (x.str -> y)
      simplifyTrivialBinding(using rctx2)(e2)
    case LetExpr(x, y @ Literal(_), e2) =>
      val rctx2 = rctx + (x.str -> y)
      simplifyTrivialBinding(using rctx2)(e2)
    case LetExpr(x, e1, e2) =>
      LetExpr(x, simplifyTrivialBinding(e1), simplifyTrivialBinding(e2))
    case LetJoin(jp, xs, e1, e2) =>
      LetJoin(jp, xs, simplifyTrivialBinding(e1), simplifyTrivialBinding(e2))
    case LetCall(xs, defn, as, e) =>
      LetCall(xs, defn, as map simplifyTrivialBindingOfTexpr, simplifyTrivialBinding(e))
  }

  private def toExpr(expr: TrivialExpr): GOExpr = expr match {
    case x: Ref => x
    case x: Literal => x
  }

  private def simplifySel(using cctx: Map[Str, Map[Str, TrivialExpr]])(node: Node): Node =
    node match {
    case Result(xs) => Result(xs)
    case Jump(jp, xs) => Jump(jp, xs)
    case Case(scrut, cases) => Case(scrut, cases map {
      (cls, e) => (cls, simplifySel(e))
    })
    case LetExpr(x, Select(y, cls, field), e2) if cctx.contains(y.str) =>
      val m = cctx(y.str)
      LetExpr(x, toExpr(m(field)), simplifySel(e2))
    case LetExpr(x, y @ CtorApp(cls, args), e2) =>
      val m = cls.fields.zip(args).toMap
      val cctx2 = cctx + (x.str -> m)
      LetExpr(x, y, simplifySel(using cctx2)(e2))
    case LetExpr(x, e1, e2) =>
      LetExpr(x, e1, simplifySel(e2))
    case LetJoin(jp, xs, e1, e2) =>
      LetJoin(jp, xs, simplifySel(e1), simplifySel(e2))
    case LetCall(xs, defn, as, e) =>
      LetCall(xs, defn, as, simplifySel(e))
  }

  private def argsToStrs(args: Ls[TrivialExpr]) = {
    args.flatMap {
      case Ref(x) => Some(x.str)
      case _ => None
    }
  }

  private def collectDeadBindings(node: Node, dead: Set[Str]): Set[Str] = node match {
    case Result(xs) => dead -- argsToStrs(xs)
    case Jump(_, xs) => dead -- argsToStrs(xs)
    case Case(scrut, cases) => cases.foldLeft(dead - scrut.str) {
      case (dead, (cls, e)) => collectDeadBindings(e, dead)
    }
    case LetExpr(x, e1, e2) =>
      val (fv, fj) = freeVarAnalysis(using Set.empty)(e1, Set.empty, Set.empty)
      collectDeadBindings(e2, dead -- fv + x.str)
    case LetJoin(_, _, _, _) =>
      throw GraphOptimizingError("nested join points after promotion")
    case LetCall(xs, defn, as, e) =>
      collectDeadBindings(e, dead -- argsToStrs(as) ++ xs.map(_.str))
  }

  private def removeDeadBindings(using dead: Set[Str])(node: Node): Node = node match {
    case Result(xs) => node
    case Jump(_, xs) => node
    case Case(scrut, cases) => Case(scrut, cases.map {
      (cls, e) => (cls, removeDeadBindings(e))
    })
    case LetExpr(x, _, e) if dead.contains(x.str) =>
      removeDeadBindings(e)
    case LetExpr(x, e1, e2) => LetExpr(x, e1, removeDeadBindings(e2))
    case LetJoin(_, _, _, _) =>
      throw GraphOptimizingError("nested join points after promotion")
    case LetCall(xs, defn, as, e) =>
      LetCall(xs, defn, as, removeDeadBindings(e))
  }

  private def simplify(defn: GODef) = {
    val simplified = simplifyTrivialBinding(using Map.empty)(simplifySel(using Map.empty)(defn.body))
    val dead = collectDeadBindings(simplified, Set.empty)
    val dced = removeDeadBindings(using dead)(simplified)
    GODef(
      defn.id,
      defn.name,
      defn.isjp, 
      defn.params,
      defn.resultNum,
      dced,
    )
  }

  def simplifyProgram(prog: GOProgram): GOProgram = {
    var changed = true
    var defs = prog.defs
    while (changed) {
      val new_defs = defs.map(simplify)
      fixGODef(using new_defs)
      validate(new_defs)
      changed = defs != new_defs
      defs = new_defs
    }
    GOProgram(prog.classes, defs, prog.main) 
  }

  def promoteJoinPoints(using accu: Ls[GODef])(node: Node): Ls[GODef] = node match {
    case Result(_) => accu
    case Jump(_jp, _xs) => accu
    case Case(scrut, cases) => cases.foldLeft(accu) {
        case (accu, (cls, e)) => promoteJoinPoints(using accu)(e)
      }
    case LetExpr(_x, _e1, e2) => promoteJoinPoints(e2)
    case LetJoin(Name(jp), xs, e1, e2) => 
      val new_def = GODef(
        genfid(), jp,
        true, xs, 1,
        e1,
      )
      val accu2 = promoteJoinPoints(e1)
      val accu3 = new_def :: accu2
      promoteJoinPoints(using accu3)(e2)
    case LetCall(_xs, _defnref, _as, e) =>
      promoteJoinPoints(e)
  }

  private def removeNestedJoinPoints(node: Node): Node = node match {
    case Result(_) | Jump(_, _) => node
    case Case(scrut, cases) => Case(scrut,
      cases map { (cls, e) => (cls, removeNestedJoinPoints(e)) })
    case LetExpr(x, e1, e2) => LetExpr(x, e1, removeNestedJoinPoints(e2))
    case LetJoin(jp, _, _, e2) => removeNestedJoinPoints(e2)
    case LetCall(xs, defnref, as, e) => LetCall(xs, defnref, as, removeNestedJoinPoints(e))
  }

  def promoteJoinPoints(prog: GOProgram): GOProgram = {
    val classes = prog.classes
    val defs = prog.defs
    val main = prog.main

    val init: Ls[GODef] = Ls()
    val new_defs = defs.foldLeft(init) {
      (accu, godef) => promoteJoinPoints(using accu)(godef.body)
    }

    val defs2 = defs ++ new_defs
    defs2 foreach {
      defn => defn.body = removeNestedJoinPoints(defn.body) 
    }

    fixGODef(using defs2)
    validate(defs2)
    GOProgram(classes, defs2, main)
  }

  private def ensureDefRefInSet(using defs: Set[GODef])(node: Node): Unit = node match {
    case Case(_, cases) => cases.foreach { case (cls, node) => (cls, ensureDefRefInSet(node)) }
    case LetCall(resultNames, defnref, args, body) =>
      defnref.defn match {
        case Left(real_defn) => if (!defs.exists(_ eq real_defn)) throw GraphOptimizingError("ref is not in the set")
        case Right(_) =>
      }
      ensureDefRefInSet(body)
    case LetExpr(name, expr, body) => ensureDefRefInSet(body)
    case LetJoin(joinName, params, rhs, body) => ensureDefRefInSet(body)
    case Result(_) =>
    case Jump(_, _) =>
  }

  private def ensureDefRefInSet(defs: Set[GODef]): Unit = {
    defs.foreach { defn => ensureDefRefInSet(using defs)(defn.body) }
  }

  private def ensureParamsArgsConsistent(using defs: Set[GODef])(node: Node): Unit = node match {
    case Case(_, cases) => cases.foreach { case (cls, node) => (cls, ensureParamsArgsConsistent(node)) }
    case LetCall(resultNames, defnref, args, body) =>
      defnref.defn match {
        case Left(real_defn) =>
          if (real_defn.params.length != args.length) 
            val x = real_defn.params.length
            val y = args.length
            throw GraphOptimizingError(s"inconsistent arguments($y) and parameters($x) number in a call to ${real_defn.name}")
        case Right(_) =>
      }
      ensureParamsArgsConsistent(body)
    case LetExpr(name, expr, body) => ensureParamsArgsConsistent(body)
    case LetJoin(joinName, params, rhs, body) => ensureParamsArgsConsistent(body)
    case Result(_) =>
    case Jump(Name(jp), xs) => 
      val jdef = defs.find{_.getName == jp}
      if (jdef.isEmpty) return
      val x = xs.length
      val y = defs.find{_.getName == jp}.get.params.length
      if (x != y)
        throw GraphOptimizingError(s"inconsistent arguments($x) and parameters($y) number in a jump to ${jp}")
  }

  private def ensureParamsArgsConsistent(defs: Set[GODef]): Unit = {
    defs.foreach { defn => ensureParamsArgsConsistent(using defs)(defn.body) }
  }

  private def validate(defs: Set[GODef]): Unit = {
    ensureDefRefInSet(defs)
    ensureParamsArgsConsistent(defs)
  }

  def activeAnalyze(prog: GOProgram): GOProgram = {
    val classes = prog.classes
    val old_defs = prog.defs
    val main = prog.main

    val defs = old_defs.map {
      defn => GODef(defn.id, defn.name, defn.isjp, defn.params, defn.resultNum, defn.body)
    }
  
    fixGODef(using defs)
    validate(defs)

    var changed = true
    val jpctx = defs.flatMap {
      case godef if godef.isjp => Some(godef.name -> godef)
      case _ => None
    }.toMap

    while (changed) {
      defs.foreach {
        case godef =>
          val intros = getIntro(using jpctx)(godef.body, Map.empty)
          val elims = godef.params.map { case Name(s) => getElim(using s, Map.empty, jpctx)(godef.body, Set.empty) }
          if (elims == godef.activeParams && intros == godef.activeResults)
            changed = false
          else
            godef.activeParams = elims
            godef.activeResults = intros
      }
    }

    fixGODef(using defs)
    validate(defs)
    GOProgram(classes, defs, main)
  }

  def optimize(prog: GOProgram): GOProgram = {
    val g1 = simplifyProgram(prog)
    val g2 = activeAnalyze(g1)

    val g3 = splitFunction(g2)
    
    val g4 = simplifyProgram(g3)
    val g5 = activeAnalyze(g4)
    
    val g6 = replaceScalar(g5)
    
    val g7 = simplifyProgram(g6)
    val g8 = activeAnalyze(g7)
    g7
  }
