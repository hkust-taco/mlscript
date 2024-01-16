package mlscript.compiler.optimizer

import mlscript.*
import mlscript.compiler.*
import mlscript.utils.*
import shorthands.*

import scala.annotation.tailrec
import scala.collection.immutable.*
import scala.collection.mutable.{HashMap => MutHMap}
import scala.collection.mutable.{HashSet => MutHSet, Set => MutSet}
import scala.collection.mutable.{MultiMap, Queue}

final case class GraphOptimizingError(message: String) extends Exception(message)

class GraphOptimizer(fresh: Fresh, fn_uid: FreshInt, class_uid: FreshInt, verbose: Bool = false):
  import GOExpr._
  import GONode._
  import Elim._
  import Intro._

  private type ClassCtx = Map[Str, ClassInfo]
  private type FieldCtx = Map[Str, (Str, ClassInfo)]
  
  private class EliminationImpl extends GOIterator:
    protected val elims = MutHMap[Str, MutSet[Elim]]()
    protected val defcount = MutHMap[Str, Int]()
    protected val visited = MutHSet[Str]()

    protected def addElim(x: Name, elim: Elim) =
      if (defcount.getOrElse(x.str, 0) <= 1)
        elims.getOrElseUpdate(x.str, MutHSet.empty) += elim
    
    protected def addBackwardElim(x: Name, elim: Elim) =
      if (defcount.getOrElse(x.str, 0) <= 1)
        val elim2 = elim match
          case EDestruct => EIndirectDestruct
          case _ => elim
        elims.getOrElseUpdate(x.str, MutHSet.empty) += elim2  

  private class DestructAnalysis:
    private def f(node: GONode): Opt[Name] = node match
      case Result(res) => None
      case Jump(defn, args) => None
      case Case(scrut, cases) => Some(scrut)
      case LetExpr(name, expr, body) => f(body)
      case LetCall(names, defn, args, body) => f(body)
    
    def isDestructed(node: GONode, name: Name) =
      f(node).contains(name)

    def firstDestructed(node: GONode) =
      f(node)

  private class EliminationAnalysis extends EliminationImpl:
    override def iterate_param(x: Name): Unit = 
      defcount.update(x.str, defcount.getOrElse(x.str, 0) + 1)
    override def iterate_name_def(x: Name) =
      defcount.update(x.str, defcount.getOrElse(x.str, 0) + 1)
    override def iterate_name_use(x: Name) =
      addElim(x, EDirect)
    override def iterate(x: Case) = x match
      case Case(x, cases) =>
        x.accept_use_iterator(this)
        addElim(x, EDestruct)
        cases foreach { (cls, arm) => arm.accept_iterator(this) }
    override def iterate(x: Select) = x match
      case Select(x, cls, field) =>
        addElim(x, ESelect(field))
    override def iterate(x: Jump) = x match
      case Jump(defnref, args) => 
        args.foreach(_.accept_iterator(this))
        val defn = defnref.expectDefn
        args.zip(defn.activeParams).foreach {
          case (Ref(x), ys) => ys.foreach { y => addBackwardElim(x, y) }
          case _ => 
        }
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          defn.accept_iterator(this)
    override def iterate(x: LetCall) = x match
      case LetCall(xs, defnref, args, body) =>
        xs.foreach(_.accept_def_iterator(this))
        args.foreach(_.accept_iterator(this))
        val defn = defnref.expectDefn 
        args.zip(defn.activeParams).foreach {
          case (Ref(x), ys) => ys.foreach { y => addBackwardElim(x, y) }
          case _ =>
        }
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          defn.accept_iterator(this)
        body.accept_iterator(this)

    override def iterate(x: GOProgram) =
      var changed = true
      while (changed)
        changed = false
        x.defs.foreach { defn =>
          val old = defn.activeParams
          elims.clear()
          visited.clear()
          defcount.clear()
          defn.accept_iterator(this)
          defn.activeParams = defn.params.map {
            param =>
              val e = elims.get(param.str) match {
                case Some(elims) => 
                  elims.toSet
                case None => Set()
              }
              e
          }
          changed |= (old != defn.activeParams)
        }
      elims.clear()
      visited.clear()
      defcount.clear()
      x.main.accept_iterator(this)

  private object IntroductionAnalysis extends GOIterator:
    private def combine_intros(xs: Ls[Ls[Opt[Intro]]]): Ls[Opt[Intro]] =
      val xst = xs.transpose
      // if (xst.exists(x => x.exists(_ != x.head)))
        xst.map {
          ys =>
            val z = ys.flatMap {
              case None => Set()
              case Some(IMix(i)) => i
              case Some(i) => Set(i)
            }.toSet
            if z.nonEmpty then Some(IMix(z)) else None
        }
      // else
      //   xs.head
    def getIntro(node: GONode, intros: Map[Str, Intro]): Ls[Opt[Intro]] = node match
      case Case(scrut, cases) => 
        val cases_intros = cases.map {
          (cls, node) => getIntro(node, intros + (scrut.str -> ICtor(cls.ident)))
        }
        combine_intros(cases_intros)
      case Jump(defnref, args) =>
        val jpdef = defnref.expectDefn
        jpdef.activeInputs = updateInputInfo(jpdef, intros, args)
        jpdef.activeResults
      case LetCall(resultNames, defnref, args, body) =>
        val defn = defnref.expectDefn
        val intros2 = updateIntroInfo(defn, intros, resultNames)
        defn.activeInputs = updateInputInfo(defn, intros, args)
        getIntro(body, intros2)
      case LetExpr(name, expr, body) => 
        val intros2 = getIntro(expr, intros) match
          case None => intros
          case Some(x) =>
            intros + (name.str -> x)
        getIntro(body, intros2)
      case Result(res) => 
        res.map { x => getIntro(x, intros) }

    def getIntro(expr: TrivialExpr, intros: Map[Str, Intro]) = expr match 
      case Literal(lit) => None
      case Ref(name) => intros.get(name.str)

    def getIntro(expr: GOExpr, intros: Map[Str, Intro]): Opt[Intro] = expr match 
      case CtorApp(cls, args) => Some(ICtor(cls.ident))
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
            defn.activeResults =
              getIntro(defn.body,
                defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params))
                  .getOrElse(Map.empty))
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
      case LetCall(resultNames, defnref, args, body) =>
        var fv2 = args.foldLeft(fv)((acc, arg) => f(using defined)(arg.to_expr, acc))
        val defined2 = resultNames.foldLeft(defined)((acc, name) => acc + name.str)
        val defn = defnref.expectDefn
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          fv2 = f(using defined2)(defn, fv2)
        f(using defined2)(body, fv2)

    def run(node: GONode) = f(using Set.empty)(node, Set.empty)

  private class DestructSite(val name: Str, val scrut: Str)
  private class CallSite(val name: Str, callee: Str, val number: Int)
  private case class PreFunction(val name: Str, val retvals: Ls[Str])
  private case class PostFunction(val name: Str, val params: Ls[Str])

  private object SplitResult:
    def case_from_mutable(
      pre_map: MutHMap[DestructSite, PreFunction],
      post_map: MutHMap[DestructSite, MutHMap[ClassInfo, PostFunction]]
    ): CaseSplitResult = 
      CaseSplitResult(pre_map.toMap, post_map.map { (k, v) => (k, v.toMap) }.toMap)
    def call_from_mutable(
      pre_map: MutHMap[CallSite, PreFunction],
      post_map: MutHMap[CallSite, PostFunction],
    ): CallSplitResult =
      CallSplitResult(pre_map.toMap, post_map.toMap)
  
  private class CallSplitResult(
    val pre_map: Map[CallSite, PreFunction],
    val post_map: Map[CallSite, PostFunction],
  )

  private class CaseSplitResult(
    val pre_map: Map[DestructSite, PreFunction],
    val post_map: Map[DestructSite, Map[ClassInfo, PostFunction]],
  )

  private class CallSplittingTarget(val fun: Map[Str, Set[CallSite]])

  private class FunctionCallSplitting(targets: CallSplittingTarget) extends GOIterator:
    val pre_map = MutHMap[CallSite, PreFunction]()
    val post_map = MutHMap[CallSite, PostFunction]()
    val pre_defs = MutHSet[GODef]()
    val post_defs = MutHSet[GODef]()
    val derived_defs = MutHMap[Str, MutHSet[Str]]()

    private def split(defn: GODef, node: GONode, accu: GONode => GONode, 
                      targets: Set[CallSite], call_count: Map[Str, Int]): Unit = node match
      case Result(res) =>
      case Jump(defn, args) =>
      case Case(scrut, cases) =>
      case LetExpr(name, expr, body) =>
        split(defn, body, n => accu(LetExpr(name, expr, n)), targets, call_count)
      case LetCall(xs, defnref, args, body) =>
        val cs = CallSite(defn.name, defnref.getName, call_count.getOrElse(defnref.getName, -1))
        if targets.contains(cs) then
          val all_fv = FreeVarAnalysis().run(body)
          val all_fv_list = all_fv.toList
          val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

          val pre_body = accu(Result(fv_retvals))
          val pre_name = fresh.make(defn.name + "$X")
          val pre_defn = GODef(
            fn_uid.make,
            pre_name.str,
            false,
            defn.params,
            all_fv.size,
            None,
            pre_body)
          pre_map.update(cs, PreFunction(pre_name.str, all_fv_list))
          pre_defs.add(pre_defn)
          derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += pre_name.str
          
          val post_name = fresh.make(defn.name + "$Y")
          val post_params_list = all_fv.toList
          val post_params = post_params_list.map(Name(_))
          val new_defn = GODef(
            fn_uid.make,
            post_name.str,
            false,
            post_params,
            defn.resultNum,
            None,
            body)
          post_map.update(cs, PostFunction(post_name.str, post_params_list))
          post_defs.add(new_defn)
          derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += post_name.str
        else
          val call_count2 = call_count.updated(defn.getName, call_count.getOrElse(defn.getName, -1) + 1)
          split(defn, body, n => accu(LetCall(xs, defnref, args, n)), targets, call_count2)
      
    override def iterate(x: GODef): Unit =
      if targets.fun.contains(x.name) then
        split(x, x.body, n => n, targets.fun(x.name), Map.empty)

  private class FunctionCaseSplitting(targets: CaseSplittingTarget) extends GOIterator:
    val worklist = targets.combine
    val pre_map = MutHMap[DestructSite, PreFunction]()
    val post_map = MutHMap[DestructSite, MutHMap[ClassInfo, PostFunction]]()
    val pre_defs = MutHSet[GODef]()
    val post_defs = MutHSet[GODef]()
    val derived_defs = MutHMap[Str, MutHSet[Str]]()

    private def split(defn: GODef, node: GONode, accu: GONode => GONode): Unit = node match
      case Result(res) => 
      case Jump(defn, args) =>
      case Case(scrut, cases) =>
        val arm_fv = cases.map(x => FreeVarAnalysis().run(x._2))
        val all_fv = arm_fv.reduce(_ ++ _) + scrut.str
        val all_fv_list = all_fv.toList
        val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

        val ds = DestructSite(defn.name, scrut.str)

        val pre_body = accu(Result(fv_retvals))
        val pre_name = fresh.make(defn.name + "$P")
        val pre_defn = GODef(
          fn_uid.make,
          pre_name.str,
          false,
          defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(ds, PreFunction(pre_name.str, all_fv_list))
        pre_defs.add(pre_defn)
        derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += pre_name.str
        
        cases.zip(arm_fv).foreach {
          case ((cls, body), fv) =>
            val post_name = fresh.make(defn.name + "$D")
            val post_params_list = fv.toList
            val post_params = post_params_list.map(Name(_))
            val new_defn = GODef(
              fn_uid.make,
              post_name.str,
              false,
              post_params,
              defn.resultNum,
              None,
              body)
            post_map
              .getOrElseUpdate(ds, MutHMap.empty)
              .update(cls, PostFunction(post_name.str, post_params_list))
            post_defs.add(new_defn)
            derived_defs.getOrElseUpdate(defn.name, MutHSet.empty) += post_name.str
        }
      case LetExpr(name, expr, body) =>
        split(defn, body, n => accu(LetExpr(name, expr, n)))
      case LetCall(xs, defnref, args, body) =>
        split(defn, body, n => accu(LetCall(xs, defnref, args, n)))
    
    override def iterate(x: GODef): Unit =
      if worklist.contains(x.name) then
        split(x, x.body, n => n)
  
  private def bindIntroInfo(intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name]) =
    args.zip(params).foldLeft(intros) {
      case (accu, (Ref(Name(arg)), Name(param))) if intros.contains(arg) => accu + (param -> intros(arg))
      case (accu, _) => accu
    }
  
  private def updateIntroInfo(defn: GODef, intros: Map[Str, Intro], xs: Ls[Name]) =
    defn.activeResults.zip(xs).foldLeft(intros) { 
      case (intros, (Some(i), name)) =>
        intros + (name.str -> i)
      case (intros, _) => intros
    }

  private def updateIntroInfoAndMaintainMixingIntros(out: MutHMap[Str, Str], defn: GODef, intros: Map[Str, Intro], xs: Ls[Name]) =
    defn.activeResults.zip(xs).foldLeft(intros) { 
      case (intros, (Some(i @ IMix(_)), name)) =>
        out += (name.str -> defn.name)
        intros + (name.str -> i)
      case (intros, (Some(i), name)) => 
        intros + (name.str -> i)
      case (intros, _) => intros
    }
    

  private def bindIntroInfoUsingInput(intros: Map[Str, Intro], input: Ls[Opt[Intro]], params: Ls[Name]) =
    input.zip(params).foldLeft(intros) {
      case (accu, (Some(i), param)) => 
        accu + (param.str -> i)
      case (accu, _) => accu
    }
  
  private def updateInputInfo(defn: GODef, intros: Map[Str, Intro], args: Ls[TrivialExpr]) =
    var all_none = true
    val ls = args.map {
      case Ref(Name(arg)) if intros.contains(arg) => all_none = false; Some(intros(arg))
      case _ => None
    }
    if all_none then defn.activeInputs else defn.activeInputs + ls

  

  private class CaseSplittingTarget(val direct: Set[Str], val indirect: Set[Str], val mixing: Set[Str]):
    def combine = direct ++ indirect ++ mixing

  private class SplittingTargetAnalysis extends GOIterator:
    private val split_defn_params_map = MutHSet[Str]()
    private val indir_defn_params_map = MutHSet[Str]()
    private val mixing_defn_results = MutHSet[Str]()
    private val name_defn_map = MutHMap[Str, Str]()

    private var cur_defn: Opt[GODef] = None
    
    private var intros = Map.empty[Str, Intro]
    private val visited = MutHSet[Str]()

    def run(x: GOProgram) =
      x.accept_iterator(this)
      CaseSplittingTarget(
        split_defn_params_map.toSet,
        indir_defn_params_map.toSet,
        mixing_defn_results.toSet)
    
    private def addSplitTarget(name: Str) =
      split_defn_params_map += name

    private def addIndirTarget(name: Str) =
      indir_defn_params_map += name
  
    private def addMixingTarget(callee_name: Str) =
      mixing_defn_results += callee_name
    
    private def checkTargets(name: Str, intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name], active: Ls[Set[Elim]]) =
      args.map { 
        case Ref(x) => (Some(x), intros.get(x.str))
        case _ => (None, None)
      }.zip(params).zip(active).foreach {
        case (((_, Some(ICtor(cls))), param), elim) if elim.contains(EDestruct) =>
          addSplitTarget(name)
        case (((_, Some(ICtor(cls))), param), elim) if elim.contains(EIndirectDestruct) =>
          addIndirTarget(name)
        case (((Some(arg), Some(IMix(_))), param), elim) if elim.contains(EDestruct) || elim.contains(EIndirectDestruct) =>
          name_defn_map.get(arg.str) match
            case Some(defn_name) => addMixingTarget(defn_name)
            case None =>
        case _ =>
      }

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)

    override def iterate(x: Case): Unit = x match
      case Case(x, cases) =>
        intros.get(x.str) match
          case Some(IMix(_))  => name_defn_map.get(x.str) match
            case Some(defn_name) => addMixingTarget(defn_name)
            case None =>
          case _ =>
        cases foreach {
          (cls, arm) => 
          intros = intros + (x.str -> ICtor(cls.ident))
          arm.accept_iterator(this)
        }

    override def iterate(x: Jump): Unit = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)
        val intros2 = intros
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          intros = bindIntroInfo(intros2, as, defn.params)
          defn.body.accept_iterator(this)
        intros = intros2

    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)
        val intros2 = updateIntroInfoAndMaintainMixingIntros(name_defn_map, defn, intros, xs)
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          intros = bindIntroInfo(intros2, as, defn.params)
          defn.body.accept_iterator(this)
        intros = intros2
        e.accept_iterator(this)

    override def iterate(x: GODef): Unit =
      visited.clear()
      name_defn_map.clear()
      cur_defn = Some(x)
      intros = x.specialized.map(bindIntroInfoUsingInput(Map.empty, _, x.params)).getOrElse(Map.empty)
      x.body.accept_iterator(this)
    
    override def iterate(x: GOProgram): Unit =
      x.defs.foreach(_.accept_iterator(this))

  private def recBoundaryMatched(producer: Opt[Int], consumer: Opt[Int]) =
    (producer, consumer) match
      case (Some(_), _) => false
      case _ => true

  private class LocalSplittingCallSiteReplacement(
    clsctx: ClassCtx,
    case_split_result: CaseSplitResult,
  ) extends GOVisitor:
    var intros = Map.empty[Str, Intro]
    private var cur_defn: Opt[GODef] = None
    var changed = false

    private def pre_map = case_split_result.pre_map
    private def post_map = case_split_result.post_map

    override def visit(x: LetExpr) = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        LetExpr(x, e1, e2.accept_visitor(this))
    
    private def getFirstDestructedSplitting(
      defn: GODef, intros: Map[Str, Intro], args: Ls[TrivialExpr]): Opt[(DestructSite, ClassInfo)] =
      def f(target: Name): Opt[ClassInfo] = 
        val cls = args.map {
          case Ref(x) => intros.get(x.str)
          case _ => None
        }.zip(defn.params).foreach {
          case (Some(ICtor(cls)), param) if param == target =>
            return Some(clsctx(cls))
          case _ =>
        }
        None
      for {
        param <- DestructAnalysis().firstDestructed(defn.body)
        ds = DestructSite(defn.name, param.str)
        _ <- post_map.get(ds)
        cls <- f(param)
      } yield (ds, cls)
    
    override def visit(x: Jump) = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        val (ds, cls) = getFirstDestructedSplitting(defn, intros, as) match {
          case None =>
            return x
          case Some(_) if !recBoundaryMatched(defnref.expectDefn.recBoundary, cur_defn.get.recBoundary) =>
            return x
          case Some(x) => x
        }
        changed = true
        val PostFunction(post_f, post_params) = post_map(ds)(cls)
        pre_map.get(ds) match {
          case Some(PreFunction(pre_f, pre_retvals)) =>
            val new_names = pre_retvals.map { _ => fresh.make }
            val names_map = pre_retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              Jump(GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}))
          case None => Jump(GODefRef(Right(post_f)), post_params.map(x => Ref(Name(x))))
        }
    
    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        val (ds, cls) = getFirstDestructedSplitting(defn, intros, as) match {
          case None =>
            // a critical mistake was made here
            intros = updateIntroInfo(defn, intros, xs)
            return LetCall(xs, defnref, as, e.accept_visitor(this))
          case Some(_) if !recBoundaryMatched(defnref.expectDefn.recBoundary, cur_defn.get.recBoundary) =>
            intros = updateIntroInfo(defn, intros, xs)
            return LetCall(xs, defnref, as, e.accept_visitor(this))
          case Some(x) => x
        }
        changed = true
        intros = updateIntroInfo(defn, intros, xs)
        val PostFunction(post_f, post_params) = post_map(ds)(cls)
        pre_map.get(ds) match {
          case Some(PreFunction(pre_f, pre_retvals)) =>
            val new_names = pre_retvals.map { _ => fresh.make }
            val names_map = pre_retvals.zip(new_names).toMap
            LetCall(new_names, GODefRef(Right(pre_f)), as,
              LetCall(xs, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
                e.accept_visitor(this)))
          case None => LetCall(xs, GODefRef(Right(post_f)), post_params.map(x => Ref(Name(x))), e.accept_visitor(this))
        }

    override def visit(x: Case) = x match
      case Case(x, cases) =>
        Case(x,
          cases map {
            (cls, arm) => 
              intros = intros + (x.str -> ICtor(cls.ident))
              (cls, arm.accept_visitor(this))
          })

    override def visit(x: GODef) =
      intros = x.specialized.map(bindIntroInfoUsingInput(Map.empty, _, x.params)).getOrElse(Map.empty)
      cur_defn = Some(x)
      val new_def = GODef(
        x.id,
        x.name,
        x.isjp,
        x.params,
        x.resultNum,
        x.specialized,
        x.body.accept_visitor(this)
      )
      cur_defn = None
      new_def

    override def visit(x: GOProgram) =
      val defs = x.defs.map(_.accept_visitor(this))
      val main = x.main.accept_visitor(this)
      relink(main, defs)
      validate(main, defs)
      GOProgram(
        x.classes,
        defs, main
      )

  private class LocalMixingSplittingCallSiteReplacement(
    cls_ctx: Map[Str, ClassInfo],
    case_split_result: CaseSplitResult,
  ) extends GOVisitor:
    var intros = Map.empty[Str, Intro]
    val defs = MutHSet[GODef]()
    var changed = false
    private var cur_defn: Opt[GODef] = None
    private val name_defn_map = MutHMap[Str, Str]()

    private def pre_map = case_split_result.pre_map
    private def post_map = case_split_result.post_map

    private def getFirstDestructedSplitting(defn: GODef, intros: Map[Str, Intro]): Opt[Str] =
      for {
        param <- DestructAnalysis().firstDestructed(defn.body)
        ds = DestructSite(defn.name, param.str)
        _ <- post_map.get(ds)
      } yield param.str

    override def visit(x: LetExpr) = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        LetExpr(x, e1, e2.accept_visitor(this))
    
    override def visit(x: LetCall) = x match
      case LetCall(xs @ Ls(x), defnref, as, e) =>
        val defn = defnref.expectDefn
        intros = updateIntroInfoAndMaintainMixingIntros(name_defn_map, defn, intros, xs)
        intros.get(x.str) match
          case Some(IMix(_)) =>
            val defn_name = defn.getName
            val can_split = for {
              scrut <- getFirstDestructedSplitting(defn, intros)
              pair = DestructSite(defn_name, scrut)
              PreFunction(pre_f, pre_retvals) <- pre_map.get(pair)
              cases <- post_map.get(pair)
            } yield (scrut, pre_f, pre_retvals, cases)

            can_split match
              case None => 
                LetCall(xs, defnref, as, e.accept_visitor(this))
              case Some(_) if !recBoundaryMatched(defnref.expectDefn.recBoundary, cur_defn.get.recBoundary) =>
                LetCall(xs, defnref, as, e.accept_visitor(this))
              case Some((scrut, pre_f, pre_retvals, cases)) =>
                changed = true
                var scrut_new_name: Opt[Name] = None
                val new_names = pre_retvals.map { retval => 
                  val name = fresh.make
                  if (scrut == retval) scrut_new_name = Some(name)
                  name
                }
                val names_map = pre_retvals.zip(new_names).toMap

                val fv = FreeVarAnalysis().run(e)
                val fv_list = fv.toList

                val new_jp_name = fresh.make(cur_defn.get.getName + "$M")
                val new_jp = GODef(
                  fn_uid.make,
                  new_jp_name.str,
                  true,
                  fv_list.map(Name(_)),
                  1,
                  None,
                  e,
                )

                defs += new_jp

                val new_cases = cases.map {
                  case (cls, PostFunction(post_f, post_params)) =>
                    val new_names_2 = xs.map { _ => fresh.make }
                    val names_map_2 = xs.map(_.str).zip(new_names_2).toMap
                    (cls, 
                      LetCall(new_names_2, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
                      Jump(GODefRef(Right(new_jp.name)), fv_list.map{x => Ref(names_map_2.getOrElse(x, Name(x)))})))
                }

                LetCall(new_names, GODefRef(Right(pre_f)), as,
                  Case(scrut_new_name.get, new_cases.toList))
          case _ => 
            LetCall(xs, defnref, as, e.accept_visitor(this)) 
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        intros = updateIntroInfoAndMaintainMixingIntros(name_defn_map, defn, intros, xs)
        LetCall(xs, defnref, as, e.accept_visitor(this))

    override def visit(x: Case) = x match
      case Case(x, cases) =>
        Case(x,
          cases map {
            (cls, arm) => 
              intros = intros + (x.str -> ICtor(cls.ident))
              (cls, arm.accept_visitor(this))
          })
    override def visit(x: GODef) =
      intros = x.specialized.map(bindIntroInfoUsingInput(Map.empty, _, x.params)).getOrElse(Map.empty)
      cur_defn = Some(x)
      val defn = GODef(
        x.id,
        x.name,
        x.isjp,
        x.params,
        x.resultNum,
        x.specialized,
        x.body.accept_visitor(this)
      )
      cur_defn = None
      defn

    override def visit(x: GOProgram) =
      var defs = x.defs.map(_.accept_visitor(this))
      val main = x.main
      defs ++= this.defs
      relink(main, defs)
      validate(main, defs)
      GOProgram(
        x.classes,
        defs, main
      )

  private object Splitting extends GOVisitor:
    override def visit(x: GOProgram) =
      val sta = SplittingTargetAnalysis()
      val targets = sta.run(x)
      val fs = FunctionCaseSplitting(targets)
      x.accept_iterator(fs)
      val case_split_result = SplitResult.case_from_mutable(fs.pre_map, fs.post_map)
      val pre_defs = fs.pre_defs.toSet
      val post_defs = fs.post_defs.toSet

      var y = GOProgram(x.classes, x.defs ++ pre_defs ++ post_defs, x.main)
      relink(y.main, y.defs)
      validate(y.main, y.defs)
      activeAnalyze(y)
      recBoundaryAnalyze(y)
      val clsctx: ClassCtx = y.classes.map{ case c @ ClassInfo(_, name, _) => (name, c) }.toMap
      var changed = true
      while (changed)
        val scsr = LocalSplittingCallSiteReplacement(clsctx, case_split_result)
        val mscsr = LocalMixingSplittingCallSiteReplacement(clsctx, case_split_result)
        y = y.accept_visitor(scsr)
        relink(y.main, y.defs)
        validate(y.main, y.defs)
        activeAnalyze(y)
        recBoundaryAnalyze(y)
        y = y.accept_visitor(mscsr)
        relink(y.main, y.defs)
        validate(y.main, y.defs)
        activeAnalyze(y)
        recBoundaryAnalyze(y)
        changed = scsr.changed | mscsr.changed
      y

  def splitFunction(prog: GOProgram) = prog.accept_visitor(Splitting)

  private class ScalarReplacementTargetAnalysis extends GOIterator:
    val ctx = MutHMap[Str, MutHMap[Str, Set[Str]]]()
    var name_map = Map[Str, Str]()
    private var intros = Map.empty[Str, Intro]
    private val visited = MutHSet[Str]()

    private def addTarget(name: Str, field: Str, target: Str) =
      ctx.getOrElseUpdate(name, MutHMap()).updateWith(target) {
        case Some(xs) => Some(xs + field)
        case None => Some(Set(field))
      }
    
    private def checkTargets(name: Str, intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name], active: Ls[Set[Elim]]) =
      args.map {
        case Ref(x) => intros.get(x.str)
        case _ => None
      }.zip(params).zip(active).foreach {
        case ((Some(ICtor(cls)), param), elim) if elim.exists(isESelect) && !elim.contains(EDirect) =>
          elim.foreach {
            case ESelect(field) => addTarget(name, field, param.str)
            case _ =>
          }
        case _ =>
      }

    override def iterate(x: Jump): Unit = x match
      case Jump(defnref, args) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, args, defn.params, defn.activeParams)
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          intros = bindIntroInfo(intros, args, defn.params)
          defn.body.accept_iterator(this)

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => Map(x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)
    
    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        checkTargets(defn.name, intros, as, defn.params, defn.activeParams)
        intros = updateIntroInfo(defn, intros, xs)
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          intros = bindIntroInfo(intros, as, defn.params)
          defn.body.accept_iterator(this)
        e.accept_iterator(this)

    override def iterate(x: Case) = x match
      case Case(x, cases) =>
        cases foreach {
          (cls, arm) => 
            intros = intros + (x.str -> ICtor(cls.ident))
            arm.accept_iterator(this)
        }
    
    override def iterate(x: GODef): Unit =
      intros = Map.empty
      visited.clear()
      x.body.accept_iterator(this)

    override def iterate(x: GOProgram): Unit =
      x.defs.foreach { x => x.accept_iterator(this) }
    
    def run(x: GOProgram) =
      x.accept_iterator(this)
      name_map = ctx.map { (k, _) => k -> fresh.make(k + "$S").str }.toMap
      ctx.map { (k, v) => k -> v.toMap }.toMap

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

  private class ScalarReplacementDefinitionBuilder(name_map: Map[Str, Str], defn_param_map: Map[Str, Map[Str, Set[Str]]]) extends GOIterator:
    var sr_defs = MutHSet[GODef]()
    override def iterate(x: GODef) =
      if (name_map.contains(x.name))
        val targets = defn_param_map(x.name)
        val new_params = newParams(x.params, targets)
        val new_name = name_map(x.name)
        val new_def = GODef(
          fn_uid.make,
          new_name,
          x.isjp, 
          new_params,
          x.resultNum,
          None,
          x.body.accept_visitor(SelectionReplacement(targets.keySet)),
        )
        sr_defs.add(new_def)

  private class ScalarReplacementCallSiteReplacement(defn_map: Map[Str, Str], defn_param_map: Map[Str, Map[Str, Set[Str]]]) extends GOVisitor:
    var fldctx = Map.empty[Str, (Str, ClassInfo)]
    private def susbtCallsite(defn: GODef, as: Ls[TrivialExpr], f: (Str, Ls[TrivialExpr]) => GONode) =
      val new_name = defn_map(defn.name)
      val targets = defn_param_map(defn.name)
      val param_subst = paramSubstMap(defn.params, targets)
      val new_params = newParams(defn.params, targets)
      val argMap = defn.params.map(_.str).zip(as).toMap

      val sel_ctx = MutHMap[(Name, Str), Name]()

      val letlist = new_params.flatMap {
        param => param_subst(param.str) match {
          case ParamKeep => None
          case ParamFieldOf(orig, field) =>
            val orig_arg = expectTexprIsRef(argMap(orig))
            val new_var = fresh.make
            sel_ctx.addOne((orig_arg, field) -> new_var)
            Some((new_var, orig_arg, field))
        }
      }

      val new_args: Ls[TrivialExpr] = new_params.map {
        param => param_subst(param.str) match {
          case ParamKeep => argMap(param.str)
          case ParamFieldOf(orig, str) =>
            val orig_arg = expectTexprIsRef(argMap(orig))
            val x = sel_ctx.get((orig_arg, str)).get
            Ref(x)
        }
      }
      
      val new_node = f(new_name, new_args)
      letlist.foldRight(new_node) { case ((x, y, field), node) => LetExpr(x, Select(y, fldctx(field)._2, field), node) }

    override def visit(x: Jump) = x match
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => Jump(GODefRef(Right(x)), y))
        else
          Jump(defnref, as)


    override def visit(x: LetCall) = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => LetCall(xs, GODefRef(Right(x)), y, e.accept_visitor(this)))
        else
          LetCall(xs, defnref, as, e.accept_visitor(this))
  
    override def visit(x: GOProgram) =
      val clsctx: ClassCtx = x.classes.map{ case c @ ClassInfo(_, name, _) => (name, c) }.toMap
      fldctx = x.classes.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      val y = GOProgram(x.classes, x.defs.map(_.accept_visitor(this)), x.main.accept_visitor(this))
      relink(y.main, y.defs)
      y

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private class ScalarReplacement extends GOVisitor:
    override def visit(x: GOProgram) =
      val srta = ScalarReplacementTargetAnalysis()
      val worklist = srta.run(x)
      val name_map = srta.name_map
      val srdb = ScalarReplacementDefinitionBuilder(name_map, worklist)
      
      x.accept_iterator(srdb)

      val new_defs = x.defs ++ srdb.sr_defs

      val srcsp = ScalarReplacementCallSiteReplacement(name_map, worklist)
      val y  = GOProgram(x.classes, new_defs, x.main)
      y.accept_visitor(srcsp)
 
  def replaceScalar(prog: GOProgram): GOProgram =
    prog.accept_visitor(ScalarReplacement())  

  private class TrivialBindingSimplification extends GOTrivialExprVisitor, GOVisitor:
    var rctx: Map[Str, TrivialExpr] = Map.empty
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(x => { rctx = Map.empty; x.accept_visitor(this)})
      relink(x.main, new_defs)
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
      relink(x.main, new_defs)
      validate(x.main, new_defs)
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

  private class DestructSimplification extends GOVisitor:
    var cctx: Map[Str, Str] = Map.empty
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.accept_visitor(this)})
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)
    override def visit(expr: LetExpr) = expr match
      case LetExpr(x, y @ CtorApp(cls, args), e2) =>
        cctx = cctx + (x.str -> cls.ident)
        LetExpr(x, y, e2.accept_visitor(this))
      case LetExpr(x, e1, e2) =>
        LetExpr(x, e1.accept_visitor(this), e2.accept_visitor(this))
    
    override def visit(x: Case) = x match
      case Case(scrut, cases) if cctx.contains(scrut.str) =>
        cctx.get(scrut.str) match
          case Some(cls) =>
            val arm = cases.find(_._1.ident == cls).get._2
            arm.accept_visitor(this)
          case None =>
            Case(scrut, cases map { (cls, arm) => (cls, arm.accept_visitor(this)) })
      case Case(scrut, cases) =>
        Case(scrut, cases map { (cls, arm) => (cls, arm.accept_visitor(this)) })

  private def argsToStrs(args: Ls[TrivialExpr]) = {
    args.flatMap {
      case Ref(x) => Some(x.str)
      case _ => None
    }
  }

  private class UsefulnessAnalysis extends GOIterator:
    val uses = MutHMap[(Name, Int), Int]()
    val defs = MutHMap[Name, Int]()
    override def iterate_name_def(x: Name) = 
      defs.update(x, defs.getOrElse(x, 0) + 1)
    override def iterate_param(x: Name) = 
      iterate_name_def(x)
    override def iterate_name_use(x: Name) =
      val key = (x, defs(x))
      uses.update(key, uses.getOrElse(key, 0) + 1)
    override def iterate(x: GOProgram) =
      val xdefs = GODefRevPostOrdering.ordered(x.main, x.defs)
      xdefs.foreach(_.accept_iterator(this))

  private class DeadCodeElimination extends GOVisitor:
    val ua = UsefulnessAnalysis()
    var cur_defn: Opt[GODef] = None
    val defs = MutHMap[Name, Int]()

    override def visit_name_def(x: Name) = 
      defs.update(x, defs.getOrElse(x, 0) + 1)
      x

    override def visit_param(x: Name) = 
      visit_name_def(x)

    override def visit(y: LetExpr) = y match
      case LetExpr(x, e1, e2) =>
        x.accept_def_visitor(this)
        e1.accept_visitor(this)
        ua.uses.get((x, defs(x))) match
          case Some(n) =>
            // if x.getElim.size == 0 then throw GraphOptimizingError(s"$x $n ${cur_defn.get}")
            LetExpr(x, e1, e2.accept_visitor(this)) 
          case None =>
            e2.accept_visitor(this)

    override def visit(x: GOProgram) =
      x.accept_iterator(ua)
      val defs = GODefRevPostOrdering.ordered(x.main, x.defs)
      val new_defs = defs.map { x =>
        cur_defn = Some(x)  
        x.accept_visitor(this)
      }.toSet
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

  private class RemoveTrivialCallAndJump extends GOVisitor:

    private def subst_let_expr(le: LetExpr, map: Map[Name, TrivialExpr]): (Ls[(Name, TrivialExpr)], LetExpr) =  
      var let_list = Ls[(Name, TrivialExpr)]()
      val new_expr = le.expr.map_name {
        x => map.get(x) match
          case None => x
          case Some(Ref(y)) => y
          case Some(other) =>
            val y = fresh.make
            let_list ::= y -> other 
            y
        
      }
      val kernel: LetExpr = LetExpr(le.name, new_expr, le.body)
      (let_list, kernel)

    private def subst_let_expr_to_node(le: LetExpr, map: Map[Name, TrivialExpr]): GONode =
      val (let_list, kernel) = subst_let_expr(le, map)
      let_list.foldLeft(kernel) {
        case (accu, (name, value)) => LetExpr(name, value.to_expr, accu)
      }

    private def param_to_arg(param: TrivialExpr, map: Map[Name, TrivialExpr]): TrivialExpr = param match
      case Ref(x) if map.contains(x) => map(x)
      case x: Ref => x
      case x: Literal => x

    private def params_to_args(params: Ls[TrivialExpr], map: Map[Name, TrivialExpr]): Ls[TrivialExpr] =
      params.map(param_to_arg(_, map))
    override def visit(x: GOProgram) =
      val new_defs = x.defs.map(_.accept_visitor(this))
      relink(x.main, new_defs)
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
          case le @ LetExpr(y, e1, Result(Ref(z) :: Nil)) if y == z =>
            subst_let_expr_to_node(le, parammap)
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
          case le @ LetExpr(y, e1, Result(Ref(z) :: Nil)) if y == z =>
            val (let_list, kernel) = subst_let_expr(le, parammap)
            let_list.foldLeft(
              LetExpr(kernel.name, kernel.expr,
                LetExpr(xs.head, Ref(kernel.name), e.accept_visitor(this)))) {
              case (accu, (name, value)) => LetExpr(name, value.to_expr, accu)
            }
          case _ => LetCall(xs, defnref, as, e.accept_visitor(this))  

  private object Identity extends GOVisitor:
    override def visit(x: GOProgram) = x
    override def visit(x: GODef) = x

  def simplifyProgram(prog: GOProgram): GOProgram = {
    var changed = true
    var s = prog
    while (changed) {
      val ds = DestructSimplification()
      val ss = SelectionSimplification()
      val tbs = TrivialBindingSimplification()
      val rtcj = RemoveTrivialCallAndJump()
      val dce = DeadCodeElimination()
      var sf = s
      sf = sf.accept_visitor(ds)
      activeAnalyze(sf)
      sf = sf.accept_visitor(ss)
      activeAnalyze(sf)
      sf = sf.accept_visitor(tbs)
      activeAnalyze(sf)
      sf = sf.accept_visitor(rtcj)
      activeAnalyze(sf)
      sf = sf.accept_visitor(dce)
      activeAnalyze(sf)
      validate(sf.main, sf.defs)
      changed = s.defs != sf.defs
      s = sf
    }
    s
  }

  def activeAnalyze(prog: GOProgram): GOProgram =
    prog.accept_iterator(EliminationAnalysis())
    prog.accept_iterator(IntroductionAnalysis)
    prog

  def optimize(prog: GOProgram): GOProgram = {
    var g = simplifyProgram(prog)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)

    g = splitFunction(g)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)

    g = simplifyProgram(g)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)
    
    g = replaceScalar(g)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)
    
    g = simplifyProgram(g)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)

    g
  }

  def recBoundaryAnalyze(prog: GOProgram): GOProgram =
    RecursiveBoundaryAnalysis.run(prog)
    prog

  private object RecursiveBoundaryAnalysis extends GOIterator:
    import GOExpr._
    import GONode._
    import Elim._
    import Intro._
    var count = 0
    def run(x: GOProgram, conservative: Bool = false) =
      val ca = CallAnalysis()
      val cg = ca.call_graph(x)
      val sccs = ca.scc()
      var scc_group = Map.empty[Str, Int]
      var scc_group_size = Map.empty[Int, Int]
      sccs.zipWithIndex.foreach { 
        (scc, i) => scc.foreach { 
          x => 
            scc_group += x -> i
            scc_group_size += i -> (scc_group_size.getOrElse(i, 0) + 1)
        }}
      x.defs.foreach { defn =>
        val group = scc_group(defn.name)
        val size = scc_group_size(group)
        defn.recBoundary = Some(group)
        if size == 1 && !cg.getOrElse(defn.name, Set.empty).contains(defn.name) then
          defn.recBoundary = None
      }

  private class CallAnalysis extends GOIterator:
    val cg = MutHMap[Str, MutHSet[Str]]()
    private var cur_defn: Opt[GODef] = None
    override def iterate(x: LetCall): Unit =
      if cur_defn.nonEmpty then
        cg.getOrElseUpdate(cur_defn.get.getName, MutHSet.empty) += x.defn.getName
        x.body.accept_iterator(this)
    override def iterate(x: Jump): Unit =
      if cur_defn.nonEmpty then
        cg.getOrElseUpdate(cur_defn.get.getName, MutHSet.empty) += x.defn.getName
    override def iterate(x: GODef): Unit =
      cur_defn = Some(x)
      x.body.accept_iterator(this)
      cur_defn = None

    def call_graph(x: GOProgram): Map[Str, Set[Str]] = 
      cg.clear()
      cg.addAll(x.defs.map(x => x.getName -> MutHSet.empty))
      x.accept_iterator(this)
      cg.map { (k, v) => k -> v.toSet }.toMap

    def scc(): List[Set[Str]] =
      var cur_index = 0
      var index = Map.empty[Str, Int]
      var low = Map.empty[Str, Int]
      var stack = Ls[Str]()
      var on_stack = Set.empty[Str]
      var sccs = Ls[Set[Str]]()

      def f(v: Str): Unit = {
        index += (v -> cur_index)
        low += (v -> cur_index)
        cur_index += 1
        stack ::= v
        on_stack += v

        cg.getOrElse(v, MutHSet.empty).foreach {
          w =>
            if (!index.contains(w)) {
              f(w)
              low += v -> low(v).min(low(w))
            } else if (on_stack.contains(w)) {
              low += v -> low(v).min(index(w))
            }
        }

        if (low(v) == index(v))
          val (scc, new_stack) = stack.splitAt(stack.indexOf(v) + 1)
          stack = new_stack
          scc.foreach { x => on_stack -= x }
          sccs ::= scc.toSet
      }

      cg.keys.foreach {
        x => if (!index.contains(x)) f(x)
      }
      
      sccs


  def copyParamsAndBuildMap(params: Ls[Name]) = 
    val new_params = params.map(_.copy)
    val map = params.zip(new_params).map((x, y) => (x.str, y)).toMap
    (new_params, map)

  private object DuplicateDefinition:
    import GONode._
    
    def run(x: GODef) =
      val (new_params, map) = copyParamsAndBuildMap(x.params)
      val y = GODef(
        fn_uid.make,
        fresh.make(x.name + "$C").str,
        x.isjp,
        new_params,
        x.resultNum,
        x.specialized,
        x.body.copy(map),
      )
      y