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
    val n = s.lastIndexOf('%')
    val (ts, suffix) = s.splitAt(if n == -1 then s.length() else n)
    var x = if suffix.stripPrefix("%").forall(_.isDigit) then ts else s
    val count = counter.getOrElse(x, 0)
    val tmp = s"$x%$count"
    counter.update(x, count + 1)
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
        jpdef.activeResults
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

  private class FreeVarAnalysis:
    val visited = MutHSet[Str]()
    private def f(using defined: Set[Str])(defn: GODef, fv: Set[Str]): Set[Str] =
      val defined2 = defn.params.foldLeft(defined)((acc, param) => acc + param.str)
      f(using defined2)(defn.body, fv)
    private def f(using defined: Set[Str])(expr: GOExpr, fv: Set[Str]): Set[Str] = expr match
      case Ref(name) => if (defined.contains(name.str)) fv else fv + name.str
      case Literal(lit) => fv
      case CtorApp(name, args) => args.foldLeft(fv)((acc, arg) => f(using defined)(arg.to_expr, acc))
      case Select(name, cls, field) => if (defined.contains(name.str)) fv else fv + name.str
      case BasicOp(name, args) => args.foldLeft(fv)((acc, arg) => f(using defined)(arg.to_expr, acc))
      case Lambda(name, body) => ???
      case Apply(name, args) =>
        val fv2 = if (defined.contains(name.str)) fv else fv + name.str
        args.foldLeft(fv2)((acc, arg) => f(using defined)(arg.to_expr, acc))
    private def f(using defined: Set[Str])(node: GONode, fv: Set[Str]): Set[Str] = node match
      case Result(res) => res.foldLeft(fv)((acc, arg) => f(using defined)(arg.to_expr, acc))
      case Jump(defnref, args) =>
        val defn = defnref.expectDefn
        val defined2 = defn.params.foldLeft(defined)((acc, param) => acc + param.str)
        var fv2 = args.foldLeft(fv)((acc, arg) => f(using defined2)(arg.to_expr, acc))
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          fv2 = f(using defined2)(defn, fv2)
        fv2
      case Case(scrut, cases) =>
        val fv2 = if (defined.contains(scrut.str)) fv else fv + scrut.str
        cases.foldLeft(fv2) {
          case (acc, (cls, body)) => f(using defined)(body, acc)
        }
      case LetExpr(name, expr, body) =>
        val fv2 = f(using defined)(expr, fv)
        val defined2 = defined + name.str
        f(using defined2)(body, fv2)
      case LetJoin(joinName, params, rhs, body) =>
        throw GraphOptimizingError(f"join points after promotion: $node")
      case LetCall(resultNames, defnref, args, body) =>
        var fv2 = args.foldLeft(fv)((acc, arg) => f(using defined)(arg.to_expr, acc))
        val defined2 = resultNames.foldLeft(defined)((acc, name) => acc + name.str)
        val defn = defnref.expectDefn
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          fv2 = f(using defined2)(defn, fv2)
        f(using defined2)(body, fv2)

    def run(node: GONode) = f(using Set.empty)(node, Set.empty)
  
  private class FunctionSplitting(worklist: Map[Str, Set[Str]]) extends GOIterator:
    val pre_map = MutHMap[(Str, Str), (Str, Ls[Str])]()
    val post_map = MutHMap[(Str, Str), MutHMap[Str, (Str, Ls[Str])]]()
    val pre_defs = MutHSet[GODef]()
    val post_defs = MutHSet[GODef]()
    val derived_defs = MutHMap[Str, MutHSet[Str]]()

    private def split(defn: GODef, node: GONode, accu: GONode => GONode, targets: Set[Str]): Unit = node match
      case Result(res) => 
        
      case Jump(defn, args) =>
      case Case(scrut, cases) if targets.contains(scrut.str) =>
        val arm_fv = cases.map(x => FreeVarAnalysis().run(x._2))
        val all_fv = arm_fv.reduce(_ ++ _)
        val all_fv_list = all_fv.toList
        val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

        if (fv_retvals.nonEmpty)
          val pre_body = accu(Result(fv_retvals))
          val pre_name = gensym(defn.name + "$P")
          val pre_defn = GODef(
            genfid(),
            pre_name.str,
            false,
            defn.params,
            all_fv.size,
            pre_body)
          pre_map.update((defn.name, scrut.str), (pre_name.str, all_fv_list))
          pre_defs.add(pre_defn)
          derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += pre_name.str
        
        
        cases.zip(arm_fv).foreach {
          case ((cls, body), fv) =>
            val post_name = gensym(defn.name + "$D")
            val post_params_list = fv.toList
            val post_params = post_params_list.map(Name(_))
            val new_defn = GODef(
              genfid(),
              post_name.str,
              true,
              post_params,
              defn.resultNum,
              body)
            post_map
              .getOrElseUpdate((defn.name, scrut.str), MutHMap.empty)
              .update(cls.ident, (post_name.str, post_params_list))
            post_defs.add(new_defn)
            derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += post_name.str
        }
      case Case(scrut, cases) =>
      case LetExpr(name, expr, body) =>
        split(defn, body, n => accu(LetExpr(name, expr, n)), targets)
      case LetJoin(joinName, params, rhs, body) =>
        throw GraphOptimizingError("join points after promotion")
      case LetCall(xs, defnref, args, body) =>
        split(defn, body, n => accu(LetCall(xs, defnref, args, n)), targets)
    
    override def iterate(x: GODef): Unit =
      split(x, x.body, n => n, worklist.getOrElse(x.name, Set.empty))

  private class SpittingTargetAnalysis extends GOIterator:
    private val targets = MutHMap[Str, MutHSet[Str]]()
    private var intros = Map.empty[Str, Intro]

    def run(x: GOProgram): Map[Str, Set[Str]] =
      x.accept_iterator(this)
      targets.map { (k, v) => k -> v.toSet }.toMap
    
    private def addTarget(name: Str, target: Str) =
      targets.getOrElseUpdate(name, MutHSet.empty) += target
    
    private def checkTargets(name: Str, intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name], active: Ls[Set[Elim]]) =
      args.map { 
        case x: Ref => intros.get(x.name.str)
        case _ => None
      }.zip(params).zip(active).foreach {
        case ((Some(ICtor(cls)), Name(param)), elim) if elim.contains(EDestruct) =>
         addTarget(name, param)
        case _ =>
      }

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)

    override def iterate(x: Jump): Unit = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)

    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        intros = defn.activeResults.zip(xs).foldLeft(intros) { 
          case (intros, (Some(i), name)) => intros + (name.str -> i)
          case (intros, _) => intros
        }
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)
        e.accept_iterator(this)

  private class SpittingCallSiteReplacement(
    pre_map: Map[(Str, Str), (Str, Ls[Str])],
    post_map: Map[(Str, Str), Map[Str, (Str, Ls[Str])]],
    derived_map: Map[Str, Set[Str]],
    pre_def: Set[GODef],
    post_def: Set[GODef],
  ) extends GOVisitor:
    var intros = Map.empty[Str, Intro]

    override def visit(x: LetExpr) = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        LetExpr(x, e1, e2.accept_visitor(this))
    
    private def getFirstPossibleSpitting(name: Str, intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name], active: Ls[Set[Elim]]): Opt[(Str, Str, Str)] =
      args.map { 
        case x: Ref => intros.get(x.name.str)
        case _ => None
      }.zip(params).zip(active).foreach {
        case ((Some(ICtor(cls)), Name(param)), elim) if elim.contains(EDestruct) =>
         val pair = (name, param)
         if (pre_map.contains(pair))
           return Some((name, param, cls))
        case _ =>
      }
      return None
    
    override def visit(x: Jump) = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        val (name, param, cls) = getFirstPossibleSpitting(defn.name, intros, as, defn.params, defn.activeParams) match {
          case Some(x) => x
          case None => return x
        }
        val (post_f, post_params) = post_map((name, param))(cls)
        pre_map.get((name, param)) match {
          case Some((pre_f, pre_retvals)) =>
            val new_names = pre_retvals.map { _ => gensym() }
            val names_map = pre_retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              Jump(GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}))
          case None => Jump(GODefRef(Right(post_f)), as)
        }
    
    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        intros = defn.activeResults.zip(xs).foldLeft(intros) { 
          case (intros, (Some(i), name)) => intros + (name.str -> i)
          case (intros, _) => intros
        }
        val (name, param, cls) = getFirstPossibleSpitting(defn.name, intros, as, defn.params, defn.activeParams) match {
          case Some(x) => x
          case None => return x
        }
        val (post_f, post_params) = post_map((name, param))(cls)
        pre_map.get((name, param)) match {
          case Some((pre_f, pre_retvals)) =>
            val new_names = pre_retvals.map { _ => gensym() }
            val names_map = pre_retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              LetCall(xs, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
                e.accept_visitor(this)))
          case None => LetCall(xs, GODefRef(Right(post_f)), as, e.accept_visitor(this))
        }
    override def visit(x: GOProgram) =
      GOProgram(
        x.classes,
        (x.defs ++ pre_def ++ post_def).map(_.accept_visitor(this)),
        x.main.accept_visitor(this)
      )

  private object Splitting extends GOVisitor:
    override def visit(x: GOProgram) =
      val worklist = SpittingTargetAnalysis().run(x)
      val fs = FunctionSplitting(worklist)
      x.accept_iterator(fs)
      val pre_map = fs.pre_map.toMap
      val post_map = fs.post_map.map { (k, v) => k -> v.toMap }.toMap
      val derived_map = fs.derived_defs.map { (k, v) => k -> v.toSet }.toMap
      val scsr = SpittingCallSiteReplacement(pre_map, post_map, derived_map, fs.pre_defs.toSet, fs.post_defs.toSet)
      val y = x.accept_visitor(scsr)
      fixCrossReferences(y.main, y.defs)
      validate(y.main, y.defs)
      y

  def splitFunction(prog: GOProgram) = prog.accept_visitor(Splitting)

  private class ScalarReplacementTargetAnalysis extends GOIterator:
    val ctx = MutHMap[Str, MutHMap[Str, Set[Str]]]()
    var intros = Map.empty[Str, Intro]

    private def addTarget(name: Str, field: Str, target: Str) =
      ctx.getOrElseUpdate(name, MutHMap()).updateWith(target) {
        case Some(xs) => Some(xs + field)
        case None => Some(Set(field))
      }
    
    private def checkTargets(name: Str, intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name], active: Ls[Set[Elim]]) =
      args.map { 
        case x: Ref => intros.get(x.name.str)
        case _ => None
      }.zip(params).zip(active).foreach {
        case ((Some(ICtor(cls)), Name(param)), elim) if elim.exists(isESelect) && !elim.contains(EDirect) =>
          elim.foreach {
            case ESelect(field) => addTarget(name, field, param)
            case _ =>
          }
        case _ =>
      }

    override def iterate(x: Jump): Unit = x match
      case Jump(defnref, args) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, args, defn.params, defn.activeParams)

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)
    
    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        intros = defn.activeResults.zip(xs).foldLeft(intros) { 
          case (intros, (Some(i), name)) => intros + (name.str -> i)
          case (intros, _) => intros
        }
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)
        e.accept_iterator(this)
    
    override def iterate(x: GODef): Unit =
      intros = Map.empty
      x.body.accept_iterator(this)

  private enum ParamSubst:
    case ParamKeep
    case ParamFieldOf(orig: Str, field: Str)

  import ParamSubst._

  private def isESelect(elim: Elim) = elim match
    case ESelect(_) => true
    case _ => false

  private def fieldParamName(name: Str, field: Str) = Name(name + "_" + field)

  private def fieldParamNames(targets: Map[Str, Set[Str]]) =
    targets.flatMap { (k, fields) => fields.map { x => fieldParamName(k, x) } }

  private def paramSubstMap(params: Ls[Name], targets: Map[Str, Set[Str]]) =
    params.flatMap { 
      case x if targets.contains(x.str) => None
      case x => Some(x.str -> ParamKeep)
    }.toMap ++ targets.flatMap {
      (k, fields) => fields.map { x => fieldParamName(k, x).str -> ParamFieldOf(k, x) }
    }.toMap


  private def newParams(params: Ls[Name], targets: Map[Str, Set[Str]]) =
      params.filter(x => !targets.contains(x.str)) ++ fieldParamNames(targets)
  
  private class SelectionReplacement(target_params: Set[Str]) extends GOVisitor:
    override def visit(x: LetExpr) = x match
      case LetExpr(x, Select(y,  cls, field), e2) if target_params.contains(y.str) =>
        LetExpr(x, Ref(fieldParamName(y.str, field)), e2.accept_visitor(this))  
      case LetExpr(x, e1, e2) =>
        LetExpr(x.accept_def_visitor(this), e1.accept_visitor(this), e2.accept_visitor(this))

  private class SRNewDefinitionBuilder(new_name: Str, old_defn: GODef, targets: Map[Str, Set[Str]]) extends GOVisitor:
    var new_defines = Ls[GODef]()
    
    override def visit(x: GODef) =
      val new_params = newParams(x.params, targets) 
      GODef(
        genfid(),
        new_name,
        x.isjp, 
        new_params,
        x.resultNum,
        x.body.accept_visitor(SelectionReplacement(targets.keySet)),
      )

  private class SRCallSiteReplacement(defnNewName: Map[Str, Str], classOfField: FieldCtx, scalarReplaceTargets: Map[Str, Map[Str, Set[Str]]]) extends GOVisitor:
    private def susbtCallsite(defn: GODef, as: Ls[TrivialExpr], f: (Str, Ls[TrivialExpr]) => GONode) =
      val new_name = defnNewName(defn.name)
      val targets = scalarReplaceTargets(defn.name)
      val param_subst = paramSubstMap(defn.params, targets)
      val new_params = newParams(defn.params, targets)
      val argMap = defn.params.map(_.str).zip(as).toMap

      val sel_ctx = MutHMap[(Str, Str), Str]()

      val letlist = new_params.flatMap {
        param => param_subst(param.str) match {
          case ParamKeep => None
          case ParamFieldOf(orig, field) =>
            val orig_arg = expectTexprIsRef(argMap(orig)).str
            val new_var = gensym()
            sel_ctx.addOne((orig_arg, field) -> new_var.str)
            Some((new_var, orig_arg, field))
        }
      }

      val new_args: Ls[TrivialExpr] = new_params.map {
        param => param_subst(param.str) match {
          case ParamKeep => argMap(param.str)
          case ParamFieldOf(orig, str) =>
            val orig_arg = expectTexprIsRef(argMap(orig)).str
            val x  = sel_ctx.get((orig_arg, str)).get
            Ref(Name(x))
        }
      }
      
      val new_node = f(new_name, new_args)
      letlist.foldRight(new_node) { case ((x, y, field), node) => LetExpr(x, Select(Name(y), classOfField(field)._2, field), node) }

    override def visit(x: Jump) = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        if (scalarReplaceTargets.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => Jump(GODefRef(Right(x)), y))
        else
          Jump(defnref, as)


    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        if (scalarReplaceTargets.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => LetCall(xs, GODefRef(Right(x)), y, e.accept_visitor(this)))
        else
          LetCall(xs, defnref, as, e.accept_visitor(this))
  

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private class ScalarReplacement extends GOVisitor:
    override def visit(x: GOProgram) =
      val classes = x.classes
      val defs = x.defs
      val main = x.main
      val srta = ScalarReplacementTargetAnalysis()
      defs.foreach(_.accept_iterator(srta))
      val workset: Map[Str, Map[Str, Set[Str]]] = srta.ctx.map {
        case (name, m) => (name, m.toMap)
      }.toMap

      val namemap = defs.flatMap {
        case defn if workset.contains(defn.name) => Some(defn.name -> gensym(defn.name + "$S").str)
        case _ => None
      }.toMap
      
      val srDefs = defs.flatMap {
        defn => workset.get(defn.name).map {
            targets => defn.accept_visitor(SRNewDefinitionBuilder(namemap(defn.name), defn, targets))
      }}

      val clsctx: ClassCtx = classes.map{ case ClassInfo(_, name, _) => name }.zip(classes).toMap
      val fldctx: FieldCtx = classes.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      val srcsp = SRCallSiteReplacement(namemap, fldctx, workset)
      val new_defs = defs.map(_.accept_visitor(srcsp)) ++ srDefs
      fixCrossReferences(main, new_defs)
      validate(main, new_defs)
      GOProgram(classes, new_defs, main)
 
  def replaceScalar(prog: GOProgram): GOProgram =
    prog.accept_visitor(ScalarReplacement())  

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

  private class SelectionSimplification extends GOVisitor:
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

    private def param_to_arg(param: TrivialExpr, map: Map[Name, TrivialExpr]): TrivialExpr = param match
      case Ref(x) if map.contains(x) => map(x)
      case x: Ref => x
      case x: Literal => x

    private def params_to_args(params: Ls[TrivialExpr], map: Map[Name, TrivialExpr]): Ls[TrivialExpr] =
      params.map(param_to_arg(_, map))
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(_.accept_visitor(this))
      fixCrossReferences(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)
    
    override def visit(x: Jump) = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn 
        val parammap = defn.params.zip(as).toMap
        defn.body match
          case Result(ys) =>
            Result(params_to_args(ys, parammap))
          case Jump(defnref, as) =>
            Jump(defnref, params_to_args(as, parammap))
          case _ => x

    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        val parammap = defn.params.zip(as).toMap
        defn.body match
          case Result(ys) =>
            val init = e.accept_visitor(this) 
            xs.zip(ys).foldRight(init) {
              case ((name, retval), node) =>
                LetExpr(name, param_to_arg(retval, parammap).to_expr, node)
            }
          case _ => LetCall(xs, defnref, as, e.accept_visitor(this))  
    

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
      val ss = SelectionSimplification()
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
        defnref.getDefn match {
          case Some(real_defn) => if (!defs.exists(_ eq real_defn)) throw GraphOptimizingError("ref is not in the set")
          case _ =>
        }
        body.accept_iterator(this)

  private object ParamsArgsAreConsistent extends GOIterator:
    override def iterate(x: LetCall) = x match
      case LetCall(res, defnref, args, body) => 
        defnref.getDefn match {
          case Some(real_defn) =>
            if (real_defn.params.length != args.length) 
              val x = real_defn.params.length
              val y = args.length
              throw GraphOptimizingError(s"inconsistent arguments($y) and parameters($x) number in a call to ${real_defn.name}")
          case _ =>
        }
    override def iterate(x: Jump) = x match
      case Jump(defnref, xs) => 
        defnref.getDefn match {
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
