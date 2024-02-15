package mlscript.compiler.optimizer

import mlscript._
import mlscript.compiler.{Expr => ASTExpr}
import mlscript.compiler.ir._
import mlscript.utils._
import shorthands._

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.collection.mutable.{HashMap => MutHMap}
import scala.collection.mutable.{HashSet => MutHSet, Set => MutSet}
import scala.collection.mutable.{MultiMap, Queue}
import mlscript.compiler.ir.{Fresh, FreshInt}
import mlscript.compiler.ir.validate

final case class GraphOptimizingError(message: String) extends Exception(message)

class Optimizer(fresh: Fresh, fn_uid: FreshInt, class_uid: FreshInt, tag: FreshInt, verbose: Bool = false):
  import Expr._
  import Node._
  import Elim._
  import Intro._

  private var split_cache: Opt[NewSplittingResult] = None

  private def log(x: Any) = if verbose then println(x)

  private type ClassCtx = Map[Str, ClassInfo]

  private def make_class_ctx(classes: Set[ClassInfo]) = classes.map { case c @ ClassInfo(_, name, _) => (name, c) }.toMap

  private type FieldCtx = Map[Str, (Str, ClassInfo)]

  private class DestructAnalysis:
    private def f(node: Node): Opt[Name] = node match
      case Result(res) => None
      case Jump(defn, args) => None
      case Case(scrut, cases) => Some(scrut)
      case LetExpr(name, expr, body) => f(body)
      case LetCall(names, defn, args, body) => f(body)
    
    def isDestructed(node: Node, name: Name) =
      f(node).contains(name)

    def firstDestructed(node: Node) =
      f(node)
  
  private class NewEliminationAnalysis:
    private case class ElimEnv(
      val defcount: MutHMap[Str, Int],
      val elims: MutHMap[Str, MutHSet[ElimInfo]],
      val defn: Str,
      val visited: MutHSet[Str],
    )

    private def addElim(env: ElimEnv, x: Name, elim: Elim, loc: LocMarker) =
      if (env.defcount.getOrElse(x.str, 0) <= 1)
        env.elims.getOrElseUpdate(x.str, MutHSet.empty) += ElimInfo(elim, DefnLocMarker(env.defn, loc))
    
    private def addBackwardElim(env: ElimEnv, x: Name, elim: ElimInfo, loc: LocMarker) =
      if (env.defcount.getOrElse(x.str, 0) <= 1)
        for {
          elim2 <- elim match {
            // If a variable is destructed in the callee,
            // then it is also indirectly destructed by the call to the callee
            case ElimInfo(EDestruct, _) | ElimInfo(EIndirectDestruct, _) =>  Some(ElimInfo(EIndirectDestruct, DefnLocMarker(env.defn, loc)))
            case ElimInfo(EDirect, _) => None
            case _ => Some(elim)
          }
          _ = env.elims.getOrElseUpdate(x.str, MutHSet.empty).add(elim2)
        } yield ()

    private def addDef(env: ElimEnv, name: Name) = 
      env.defcount.update(name.str, env.defcount.getOrElse(name.str, 0) + 1)
    
    private def f(env: ElimEnv, x: Name, loc: LocMarker): Unit =
      addElim(env, x, EDirect, loc)
    
    private def f(env: ElimEnv, x: TrivialExpr, loc: LocMarker): Unit = x match
      case Ref(name) => f(env, name, loc)
      case _ =>

    private def f(env: ElimEnv, x: Expr, loc: LocMarker): Unit = x match
      case Ref(name) => f(env, name, loc)
      case Literal(lit) =>
      case CtorApp(name, args) => args.foreach(f(env, _, loc))
      case Select(name, cls, field) => addElim(env, name, ESelect(field), loc)
      case BasicOp(name, args) => args.foreach(f(env, _, loc))

    private def f(env: ElimEnv, x: Node): Unit = x match
      case Result(res) => res.foreach(f(env, _, x.loc_marker))
      case Jump(defnref, args) =>
        args.foreach(f(env, _, x.loc_marker))
        val defn = defnref.expectDefn
        val loc = x.loc_marker
        args.zip(defn.newActiveParams).foreach {
          case (Ref(x), ys) => ys.foreach { y => addBackwardElim(env, x, y, loc) }
          case _ =>
        }
        if (!env.visited.contains(defn.name))
          env.visited.add(defn.name)
          defn.params.foreach(addDef(env, _))
          f(env.copy(defn = defn.name), defn.body)
      case Case(scrut, cases) => 
        f(env, scrut, x.loc_marker)
        addElim(env, scrut, EDestruct, x.loc_marker)
        cases.foreach((cls, arm) => f(env, arm))
      case LetExpr(name, expr, body) =>
        f(env, expr, x.loc_marker)
        addDef(env, name)
        f(env, body)
      case LetCall(names, defnref, args, body) =>
        val loc = x.loc_marker
        args.foreach(f(env, _, loc))
        val defn = defnref.expectDefn
        args.zip(defn.newActiveParams).foreach {
          case (Ref(x), ys) => ys.foreach { y => addBackwardElim(env, x, y, loc) }
          case _ =>
        }
        if (!env.visited.contains(defn.name))
          env.visited.add(defn.name)
          defn.params.foreach(addDef(env, _))
          f(env.copy(defn = defn.name), defn.body)
        names.foreach(addDef(env, _))
        f(env, body)

    def run(x: Program) = 
      var changed = true
      while (changed)
        changed = false
        x.defs.foreach { defn =>
          val old = defn.newActiveParams
          val env = ElimEnv(MutHMap.empty, MutHMap.empty, defn.name, MutHSet.empty)
          defn.params.foreach(addDef(env, _))
          f(env, defn.body)
          defn.newActiveParams = defn.params.map {
            param =>
              env.elims.get(param.str).getOrElse(MutHSet.empty).toSortedSet
          }
          changed |= (old != defn.newActiveParams)
        }

  private object IntroductionAnalysis extends Iterator:
    private def combine_intros(xs: Ls[Ls[Opt[Intro]]]): Ls[Opt[Intro]] =
      val xst = xs.transpose
        xst.map {
          ys =>
            val z = ys.flatMap {
              case None => Set()
              case Some(IMix(i)) => i
              case Some(i) => Set(i)
            }.toSet
            if z.nonEmpty then Some(IMix(z)) else None
        }
    def getIntro(n: Int, node: Node, intros: Map[Str, Intro]): Ls[Opt[Intro]] = node match
      case Case(scrut, cases) => 
        val cases_intros = cases.map {
          (cls, node) =>
            val x = getIntro(n, node, intros + (scrut.str -> ICtor(cls.ident)))
            x
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
        getIntro(n, body, intros2)
      case LetExpr(name, expr, body) => 
        val intros2 = getIntro(expr, intros) match
          case None => intros
          case Some(x) =>
            intros + (name.str -> x)
        getIntro(n, body, intros2)
      case Result(res) => 
        res.map { x => getIntro(x, intros) }

    def getIntro(expr: TrivialExpr, intros: Map[Str, Intro]) = expr match 
      case Literal(lit) => None
      case Ref(name) => intros.get(name.str)

    def getIntro(expr: Expr, intros: Map[Str, Intro]): Opt[Intro] = expr match 
      case CtorApp(cls, args) => Some(ICtor(cls.ident))
      case _ => None

    def getIntro(expr: TrivialExpr): Opt[Intro] = getIntro(expr, Map.empty)
    def getIntro(expr: Expr): Opt[Intro] = getIntro(expr, Map.empty)
    def getIntro(n: Int, node: Node): Ls[Opt[Intro]] = getIntro(n, node, Map.empty)

    override def iterate(x: Program) =
      var changed = true
      while (changed)
        changed = false
        x.defs.foreach { 
          defn =>
            val old = defn.activeResults
            defn.activeResults =
              getIntro(defn.resultNum, defn.body,
                defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params))
                  .getOrElse(Map.empty))
            if defn.resultNum != defn.activeResults.length then throw GraphOptimizingError(s"Inconsistent result number for ${defn.name}")
            changed |= old != defn.activeResults
        }

  private case class PreFunction(val name: Str, val retvals: Ls[Str]):
    override def toString = s"Pre($name, [$retvals])"
  private case class PostFunction(val name: Str, val params: Ls[Str]):
    override def toString = s"Post($name, [$params])"

  private def bindIntroInfo(intros: Map[Str, Intro], args: Ls[TrivialExpr], params: Ls[Name]) =
    args.zip(params).foldLeft(intros) {
      case (accu, (Ref(Name(arg)), Name(param))) if intros.contains(arg) => accu + (param -> intros(arg))
      case (accu, _) => accu
    }
  
  private def updateIntroInfo(defn: Defn, intros: Map[Str, Intro], xs: Ls[Name]) =
    defn.activeResults.zip(xs).foldLeft(intros) { 
      case (intros, (Some(i), name)) =>
        intros + (name.str -> i)
      case (intros, _) => intros
    }

  private def updateIntroInfoAndMaintainMixingIntros(out: MutHMap[Str, Str], defn: Defn, intros: Map[Str, Intro], xs: Ls[Name]) =
    defn.activeResults.zip(xs).foldLeft(intros) { 
      case (intros, (Some(i @ IMix(_)), name)) =>
        out += (name.str -> defn.name)
        intros + (name.str -> i)
      case (intros, (Some(i), name)) => 
        intros + (name.str -> i)
      case (intros, _) => intros
    }

  private def updateIntroInfoAndMaintainMixingIntrosNew(out: MutHMap[Str, LocMarker], defn: Defn, loc: LocMarker, intros: Map[Str, Intro], xs: Ls[Name]) =
    defn.activeResults.zip(xs).foldLeft(intros) { 
      case (intros, (Some(i @ IMix(_)), name)) =>
        out += (name.str -> loc)
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
  
  private def updateInputInfo(defn: Defn, intros: Map[Str, Intro], args: Ls[TrivialExpr]) =
    var all_none = true
    val ls = args.map {
      case Ref(Name(arg)) if intros.contains(arg) => all_none = false; Some(intros(arg))
      case _ => None
    }
    if all_none then defn.activeInputs else defn.activeInputs + ls

  
  private class NewSplittingTarget(
    val mixing_producer: Map[LocMarker, Str],
    val mixing_consumer: Map[LocMarker, Str],
    val indirect_consumer: Map[LocMarker, IndirectConsumer],
    val known_case: Map[LocMarker, Str],
    val specialize: Map[LocMarker, WrapAndSpecialize],
  )

  private case class NewSplittingResult(
    val targets: NewSplittingTarget,
    val first_case: Map[Str, DefnLocMarker],
    val specialized_map: Map[Str, Str],
    val pre_map: Map[DefnLocMarker, PreFunction],
    val single_post_map: Map[DefnLocMarker, PostFunction],
    val mutli_post_map: Map[DefnLocMarker, Map[ClassInfo, PostFunction]],
    val pre_defs: Map[Str, Defn],
    val post_defs: Map[Str, Defn],
    val specialized_defs: Map[Str, Defn],
    val overwrite_defs: Map[Str, Defn],
  ):
    def all_defs = pre_defs.values ++ post_defs.values ++ specialized_defs.values
    def overwrite(defs: Set[Defn]) =
      defs.map(x => if overwrite_defs.contains(x.name) then overwrite_defs(x.name) else x)
    def into_cache(g: Program) =
      val new_pre_defs = pre_defs.flatMap((k, v) => g.defs.find(_.name == k).map(x => (k, x)))
      val new_post_defs = post_defs.flatMap((k, v) => g.defs.find(_.name == k).map(x => (k, x)))
      val new_specialized_defs = specialized_defs.flatMap((k, v) => g.defs.find(_.name == k).map(x => (k, x)))
      val new_pre_defs_names = new_pre_defs.keys.toSet
      val new_post_defs_names = new_post_defs.keys.toSet
      val new_specialized_defs_names = new_specialized_defs.keys.toSet
      val new_specialized_map = specialized_map.filter((k, v) => new_specialized_defs_names.contains(v))
      val new_pre_map = pre_map.filter((k, v) => new_pre_defs_names.contains(v.name))
      val new_single_post_map = single_post_map.filter((k, v) => new_post_defs_names.contains(v.name))
      val new_mutli_post_map = mutli_post_map.map { (k, v) => (k, v.filter((k, v) => new_post_defs_names.contains(v.name))) }
      val new_first_case = first_case.filter((k, v) => pre_map.contains(v))

      this.copy(
        first_case = new_first_case,
        pre_map = new_pre_map,
        single_post_map = new_single_post_map,
        mutli_post_map = new_mutli_post_map,
        pre_defs = new_pre_defs,
        post_defs = new_post_defs,
        overwrite_defs = Map.empty,
      )

  private enum IndirectSplitKind:
    case FirstCase        // a pre and multiple posts
    case JumpBeforeCase   // a pre
    case CallBeforeCase   // a pre and a post
    case AfterCase        // a pre and multiple posts

  private def get_indirect_split_kind(node: Node, loc: LocMarker): Opt[IndirectSplitKind] =
    import IndirectSplitKind._
    node match
    case Result(res) => None
    case Jump(defn, args) => 
      if loc matches node then Some(CallBeforeCase)
      else None
    case Case(scrut, cases) =>
      if loc matches node then Some(FirstCase)
      else cases.find { (cls, arm) => get_indirect_split_kind(arm, loc).isDefined } match
        case Some(_) => Some(AfterCase)
        case None => None
    case LetExpr(name, expr, body) => get_indirect_split_kind(body, loc)
    case LetCall(xs, defnref, args, body) => 
      if loc matches node then Some(CallBeforeCase)
      else get_indirect_split_kind(body, loc)

  private class NewFunctionSplitting(prev_sr: Opt[NewSplittingResult] = None):
    private val first_case = MutHMap[Str, DefnLocMarker]()
    private val specialized_map = MutHMap[Str, Str]()
    private val pre_map = MutHMap[DefnLocMarker, PreFunction]()
    private val single_post_map = MutHMap[DefnLocMarker, PostFunction]()
    private val mutli_post_map = MutHMap[DefnLocMarker, MutHMap[ClassInfo, PostFunction]]()
    private val pre_defs = MutHMap[Str, Defn]()
    private val post_defs = MutHMap[Str, Defn]()
    private val overwrite_defs = MutHMap[Str, Defn]()
    private val specialized_defs = MutHMap[Str, Defn]()
    private val split_memo = MutHSet[DefnLocMarker]()

    def run(defs: Set[Defn], targets: NewSplittingTarget): NewSplittingResult =
      prev_sr match
        case None => 
        case Some(value) =>
          first_case ++= value.first_case
          pre_map ++= value.pre_map
          single_post_map ++= value.single_post_map
          value.mutli_post_map.foreach((k, v) => mutli_post_map.getOrElseUpdate(k, MutHMap.empty) ++= v)
          pre_defs ++= value.pre_defs
          post_defs ++= value.post_defs
          split_memo ++= value.pre_map.keySet

      val defs_map = defs.map(x => (x.name, x)).toMap
      targets.mixing_producer.values.foreach { defn_name =>
        val defn = defs_map(defn_name)
        split_at_first_case(SplitEnv(defn, n => n, None), defn.body)
      }
      targets.mixing_consumer.values.foreach { defn_name =>
        val defn = defs_map(defn_name)
        split_at_first_case(SplitEnv(defn, n => n, None), defn.body)
      }
      targets.indirect_consumer.values.foreach { case IndirectConsumer(defn_name, where, kind) =>
        import IndirectSplitKind._
        val defn = defs_map(defn_name)
        kind match
          case FirstCase => split_at_first_case(SplitEnv(defn, n => n, None), defn.body)
          case JumpBeforeCase | CallBeforeCase => split_at_jump_or_letcall(SplitEnv(defn, n => n, None), defn.body, where.marker)
          case AfterCase => split_at_first_case(SplitEnv(defn, n => n, None), defn.body)        
      }
      targets.specialize.values.foreach { case WrapAndSpecialize(defn_name, spec) =>
        val defn = defs_map(defn_name)
        val new_defn = Defn(
          name = fresh.make(defn_name + "$O").str,
          resultNum = defn.resultNum,
          params = defn.params,
          id = fn_uid.make,
          body = Jump(DefnRef(Right(defn_name)),defn.params.map(Ref(_))).attach_tag(tag),
          specialized = Some(spec),
        )
        specialized_map.update(defn_name, new_defn.name)
        specialized_defs.update(new_defn.name, new_defn)
      }
      val result = NewSplittingResult(
        targets = targets,
        first_case = first_case.toMap, specialized_map = specialized_map.toMap,
        pre_map = pre_map.toMap, single_post_map = single_post_map.toMap,
        mutli_post_map = mutli_post_map.map { (k, v) => (k, v.toMap) }.toMap,
        pre_defs = pre_defs.toMap, post_defs = post_defs.toMap, overwrite_defs = overwrite_defs.toMap,
        specialized_defs = specialized_defs.toMap
      )

      first_case.clear()
      pre_map.clear()
      single_post_map.clear()
      mutli_post_map.clear()
      split_memo.clear()
      pre_defs.clear()
      post_defs.clear()
      result

    private case class SplitEnv(
      val defn: Defn,
      val accu: Node => Node,
      val specialize_on: Opt[Ls[Opt[Intro]]],
    )

    private def duplicate_and_keep_tags(node: Node): Node = node match
      case Result(res) => Result(res).copy_tag(node)
      case Jump(defn, args) => Jump(defn, args).copy_tag(node)
      case Case(scrut, cases) => Case(scrut, cases map { (cls, arm) => (cls, duplicate_and_keep_tags(arm)) }).copy_tag(node)
      case LetExpr(name, expr, body) => LetExpr(name, expr, duplicate_and_keep_tags(body)).copy_tag(node)
      case LetCall(names, defn, args, body) => LetCall(names, defn, args, duplicate_and_keep_tags(body)).copy_tag(node)

    private def split_at_jump_or_letcall(env: SplitEnv, node: Node, marker: LocMarker): Opt[DefnLocMarker] = node match
      case Result(res) => None
      case Jump(defnref, args) =>
        val defn = env.defn
        val dloc = DefnLocMarker(defn.name, marker)

        if split_memo.contains(dloc) then return None
        else split_memo.add(dloc)

        val all_fv = FreeVarAnalysis().run(node)
        val all_fv_list = all_fv.toList
        val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

        val pre_body = env.accu(Result(fv_retvals).attach_tag(tag))
        val pre_name = fresh.make(defn.name + "$A")
        val pre_defn = Defn(
          fn_uid.make,
          pre_name.str,
          defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)

        val new_names = make_new_names_for_free_variables(all_fv_list)
        val names_map = all_fv_list.zip(new_names).toMap
        val override_defn =
          env.defn.copy(body = 
            LetCall(new_names, DefnRef(Right(pre_name.str)), env.defn.params.map(Ref(_)),
              Jump(defnref, args.map { case Ref(Name(x)) => Ref(names_map(x)); case x => x }).attach_tag(tag)).attach_tag(tag))
        overwrite_defs.put(defn.name, override_defn).map(x => throw GraphOptimizingError("Unexpected overwrite"))

        Some(dloc)
      case Case(scrut, cases) => None
      case LetExpr(name, expr, body) => split_at_jump_or_letcall(env.copy(accu = n => env.accu(LetExpr(name, expr, n).copy_tag(node))), body, marker)
      case LetCall(xs, defnref, args, body) if marker matches node =>
        val defn = env.defn
        val dloc = DefnLocMarker(defn.name, marker)

        if split_memo.contains(dloc) then return None
        else split_memo.add(dloc)

        val bindings_fv = xs.map(_.str)
        val all_fv = FreeVarAnalysis().run(node)
        val all_fv_list = all_fv.toList
        val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

        val pre_body = env.accu(Result(fv_retvals).attach_tag(tag))
        val pre_name = fresh.make(defn.name + "$X")
        val pre_defn = Defn(
          fn_uid.make,
          pre_name.str,
          defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)
        
        val post_name = fresh.make(defn.name + "$Y")
        val post_params_list = bindings_fv ++ all_fv.toList
        val post_params = post_params_list.map(Name(_))
        val new_defn = Defn(
          fn_uid.make,
          post_name.str,
          post_params,
          defn.resultNum,
          None,
          body)
        single_post_map.update(dloc, PostFunction(post_name.str, post_params_list))
        post_defs.update(post_name.str, new_defn)

        val new_names = make_new_names_for_free_variables(all_fv_list)
        val names_map = all_fv_list.zip(new_names).toMap
        val new_names_2 = make_new_names_for_free_variables(xs.map(_.str))
        val names_map_2 = names_map ++ xs.map(_.str).zip(new_names_2).toMap
        val override_defn =
          env.defn.copy(body = 
            LetCall(new_names, DefnRef(Right(pre_name.str)), env.defn.params.map(Ref(_)),
              LetCall(new_names_2, defnref, args.map { case Ref(Name(x)) => Ref(names_map(x)); case x => x },
                Jump(DefnRef(Right(post_name.str)), post_params.map{x => Ref(names_map_2(x.str))}).attach_tag(tag)).attach_tag(tag)).attach_tag(tag))
        overwrite_defs.put(defn.name, override_defn).map(x => throw GraphOptimizingError("Unexpected overwrite"))
        
        Some(dloc)
      case LetCall(xs, defnref, args, body) =>
        split_at_jump_or_letcall(env.copy(accu = n => env.accu(LetCall(xs, defnref, args, n).copy_tag(node))), body, marker)
    
    private def split_at_first_case(env: SplitEnv, node: Node): Opt[DefnLocMarker] = node match
      case Result(res) => None
      case Jump(defn, args) => None
      case Case(scrut, cases) =>
        val defn = env.defn
        val loc = node.loc_marker
        val dloc = DefnLocMarker(defn.name, loc)
        
        if split_memo.contains(dloc) then return None
        else split_memo.add(dloc)

        first_case.update(env.defn.name, dloc)

        val arm_fv = cases.map(x => FreeVarAnalysis().run(x._2))
        val all_fv = arm_fv.reduce(_ ++ _) + scrut.str
        val all_fv_list = all_fv.toList
        val fv_retvals = all_fv_list.map { x => Ref(Name(x)) }

        val pre_body = env.accu(Result(fv_retvals).attach_tag(tag))
        val pre_name = fresh.make(defn.name + "$P")
        val pre_defn = Defn(
          fn_uid.make,
          pre_name.str,
          env.defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)
        
        val new_cases = cases.zip(arm_fv).map {
          case ((cls, body), fv) =>
            val post_name = fresh.make(defn.name + "$D")
            val post_params_list = fv.toList
            val post_params = post_params_list.map(Name(_))
            val new_defn = Defn(
              fn_uid.make,
              post_name.str,
              post_params,
              defn.resultNum,
              None,
              body)
            mutli_post_map
              .getOrElseUpdate(dloc, MutHMap.empty)
              .update(cls, PostFunction(post_name.str, post_params_list))
            post_defs.update(post_name.str, new_defn)
            (cls, (post_name.str, post_params_list))
        }


        val (new_names, scrut_new_name) = make_new_names_for_free_variables(all_fv_list, scrut.str)
        val names_map = all_fv_list.zip(new_names).toMap
        val overwrite_defn = env.defn.copy(
          body =
            LetCall(new_names, DefnRef(Right(pre_name.str)), env.defn.params.map(Ref(_)),
              Case(scrut_new_name.get, new_cases.map{
                case (cls, (post_f, post_params)) => (cls, Jump(DefnRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}).attach_tag(tag))
              }).attach_tag(tag)).attach_tag(tag))
        overwrite_defs.put(defn.name, overwrite_defn).map(x => throw GraphOptimizingError("Unexpected overwrite"))

        Some(dloc)
      case LetExpr(name, expr, body) =>
        split_at_first_case(env.copy(accu = n => env.accu(LetExpr(name, expr, n).copy_tag(node))), body)
      case LetCall(xs, defnref, args, body) =>
        split_at_first_case(env.copy(accu = n => env.accu(LetCall(xs, defnref, args, n).copy_tag(node))), body)
    
  private case class IndirectConsumer(val defn: Str, val where: DefnLocMarker, val kind: IndirectSplitKind)
  private case class WrapAndSpecialize(val defn: Str, val spec: Ls[Opt[Intro]])
  
  private class NewSplittingTargetAnalysis:
    private val known_case = MutHMap[LocMarker, Str]()
    private val indirect_consumer = MutHMap[LocMarker, IndirectConsumer]()
    private val specialize = MutHMap[LocMarker, WrapAndSpecialize]()
    private val mixing_consumer = MutHMap[LocMarker, Str]()
    private val mixing_producer = MutHMap[LocMarker, Str]()
    private val name_defn_map = MutHMap[Str, LocMarker]()

    private case class SplitTargetEnv(
      val intros: Map[Str, Intro],
      val defn: Defn,
      val visited: MutHSet[Str],
    )

    private def checkTargets(env: SplitTargetEnv, defn: Defn, csloc: DefnLocMarker, args: Ls[TrivialExpr]) =
      val intros = env.intros
      val name = defn.name
      val params = defn.params
      val active = defn.newActiveParams
      val asa: Ls[(Opt[Name], Opt[Intro])] = args.map {
        case Ref(x) => (Some(x), intros.get(x.str))
        case _ => (None, None)
      }
      asa.zip(params).zip(active).foreach {
        case (((_, Some(ICtor(cls))), param), elims) =>
          def aux: Unit =
            for (elim <- elims)
              elim match
                case ElimInfo(EDestruct, _) =>
                  mixing_consumer += csloc.marker -> name
                  if DestructAnalysis().firstDestructed(defn.body) == Some(param) then
                    known_case += csloc.marker -> cls
                  return
                case ElimInfo(EIndirectDestruct, loc) =>
                  val split_kind = get_indirect_split_kind(defn.body, loc.marker)
                  if split_kind.isDefined then
                    indirect_consumer += csloc.marker -> IndirectConsumer(name, loc, split_kind.get)
                    if DestructAnalysis().firstDestructed(defn.body) == Some(param) then
                      // known_case += csloc.marker -> cls
                    return
                case _ =>
          aux
        case (((Some(arg), Some(IMix(_))), param), elims) =>
          def aux: Unit =
            for (elim <- elims)
              elim match
                case ElimInfo(EDestruct, _) | ElimInfo(EIndirectDestruct, _) =>
                  name_defn_map.get(arg.str) match
                    case Some(loc) => 
                      val target = (
                        loc match
                          case LocMarker.MLetCall(_, defn, _) => defn
                          case _ => throw GraphOptimizingError("Unexpected loc marker"))
                      mixing_producer += loc -> target
                      return
                    case None =>
                case _ =>
          aux
        case _ =>
      }
      /*
      val ai = asa.map(_._2)
      if defn.specialized.isEmpty && 
        ai.exists{ case Some(ICtor(_)) => true; case _ => false } &&
        ai.forall{ case Some(IMix(_)) => false; case _ => true } then
        specialize += csloc.marker -> WrapAndSpecialize(name, ai)
      */

    private def f(env: SplitTargetEnv, node: Node): Unit = node match
      case Result(res) =>
      case Jump(defnref, args) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        val defn = defnref.expectDefn
        checkTargets(env, defn, dloc, args)
      case Case(x, cases) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        env.intros.get(x.str) match
          case Some(IMix(_))  => name_defn_map.get(x.str) match
            case Some(loc) =>
              mixing_producer += loc -> (loc match
                case LocMarker.MLetCall(_, defn, _) => defn
                case _ => throw GraphOptimizingError("Unexpected loc marker"))
            case None =>
          case _ =>
        cases foreach { (cls, arm) => 
          val intros2 = env.intros + (x.str -> ICtor(cls.ident))
          f(env.copy(intros = intros2), arm)
        }
      case LetExpr(x, e1, e2) =>
        val intros = IntroductionAnalysis.getIntro(e1, env.intros).map { y => env.intros + (x.str -> y) }.getOrElse(env.intros)
        f(env.copy(intros = intros), e2)
      case LetCall(xs, defnref, args, e) =>
        val defn = defnref.expectDefn
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        checkTargets(env, defn, dloc, args)
        val intros2 = updateIntroInfoAndMaintainMixingIntrosNew(name_defn_map, defn, node.loc_marker, env.intros, xs)
        f(env.copy(intros = intros2), e)

      def run(x: Program) =
        x.defs.foreach { defn =>
          val env = SplitTargetEnv(
            defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params)).getOrElse(Map.empty),
            defn,
            MutHSet.empty)
          f(env, defn.body)
        }
        NewSplittingTarget(mixing_producer.toMap, mixing_consumer.toMap, indirect_consumer.toMap, known_case.toMap, specialize.toMap)

  private def recBoundaryMatched(producer: Opt[Int], consumer: Opt[Int]) =
    (producer, consumer) match
      case (Some(_), Some(_)) => false
      case _ => true
  
  private def make_new_names_for_free_variables(fvs: Ls[Str]) =
    val new_names = fvs.map { fv => fresh.make }
    new_names

  private def make_new_names_for_free_variables(fvs: Ls[Str], scrut: Str) =
    var scrut_new_name: Opt[Name] = None
    val new_names = fvs.map { fv => 
      val name = fresh.make
      if (scrut == fv)
        scrut_new_name = Some(name)
      name
    }
    (new_names, scrut_new_name)

  private class NewSplittingCallSiteReplacement(
    clsctx: ClassCtx,
    split_result: NewSplittingResult,
  ):
    var changed = false
    private val name_defn_map = MutHMap[Str, LocMarker]()
    private val new_defs = MutHSet[Defn]()
    private var defs = Set.empty[Defn]

    private val pre_map = split_result.pre_map
    private val single_post_map = split_result.single_post_map
    private val mutli_post_map = split_result.mutli_post_map
    private val first_case = split_result.first_case
    private val specialized_map = split_result.specialized_map

    private val targets = split_result.targets

    private case class SubstEnv(
      val intros: Map[Str, Intro],
      val defn: Defn,
    )

    private def rebuild_args_from_marker(args: Ls[LocMarker], map: Map[Str, Name]) =
      args.map {
        case LocMarker.MRef(x) => Ref(map(x))
        case LocMarker.MLit(x) => Literal(x)
        case _ => ???
      }

    private def subst_letcall_known_case(env: SubstEnv, sdloc: DefnLocMarker, xs: Ls[Name], as: Ls[TrivialExpr], body: Node, known_case: Str): Node =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap

      val cls = clsctx(known_case)
      val PostFunction(post_f, post_params) = cases(cls)

      LetCall(new_names, DefnRef(Right(pre_f)), as,
        LetCall(xs, DefnRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
          body).attach_tag(tag)).attach_tag(tag)

    private def subst_letcall_mixing_cases(env: SubstEnv, sdloc: DefnLocMarker, xs: Ls[Name], as: Ls[TrivialExpr], body: Node): Node =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap

      val fv = FreeVarAnalysis().run(body)
      val fv_list = fv.toList

      val new_jp_name = fresh.make(env.defn.name + "$M")
      val new_jp = Defn(
        fn_uid.make,
        new_jp_name.str,
        fv_list.map(Name(_)),
        env.defn.resultNum,
        None,
        body,
      )

      defs += new_jp

      val new_cases = cases.map {
        case (cls, PostFunction(post_f, post_params)) =>
          val new_names_2 = xs.map { _ => fresh.make }
          val names_map_2 = xs.map(_.str).zip(new_names_2).toMap
          
          (cls, 
            LetCall(new_names_2, DefnRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
              Jump(DefnRef(Right(new_jp.name)), fv_list.map{x => Ref(names_map_2.getOrElse(x, Name(x)))}).attach_tag(tag)).attach_tag(tag))
      }

      val node = LetCall(new_names, DefnRef(Right(pre_f)), as,
        Case(scrut_new_name.get, new_cases.toList).attach_tag(tag)).attach_tag(tag)
      node

    private def subst_letcall_indirect(env: SubstEnv, ic: IndirectConsumer, xs: Ls[Name], as: Ls[TrivialExpr], body: Node): Node =
      val defn_name = ic.defn
      val kind = ic.kind
      import IndirectSplitKind._
      kind match
        case FirstCase | AfterCase =>
          // it's impossible to have first case here because we have an EIndirectDestruct elim
          subst_letcall_mixing_cases(env, first_case(defn_name), xs, as, body)
        case JumpBeforeCase =>      
          val (name, args) = ic.where.marker match
            case LocMarker.MJump(name, args) => (name, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(ic.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          LetCall(new_names, DefnRef(Right(pre_f)), as,
            LetCall(xs, DefnRef(Right(name)), rebuild_args_from_marker(args, names_map),
              body).attach_tag(tag)).attach_tag(tag)
        case CallBeforeCase =>
          val (names, defn2, args) = ic.where.marker match
            case LocMarker.MLetCall(names, defn, args) => (names, defn, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(ic.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          val new_names_2 = make_new_names_for_free_variables(names)
          val names_map_2 = names_map ++ names.zip(new_names_2).toMap
          val PostFunction(post_f, post_params) = single_post_map(ic.where)
          val node = LetCall(new_names, DefnRef(Right(pre_f)), as,
            LetCall(new_names_2, DefnRef(Right(defn2)), rebuild_args_from_marker(args, names_map),
              LetCall(xs, DefnRef(Right(post_f)), post_params.map{x => Ref(names_map_2(x))}, body).attach_tag(tag)).attach_tag(tag)).attach_tag(tag)
          node

    private def subst_jump_known_case(sdloc: DefnLocMarker, as: Ls[TrivialExpr], known_case: Str): Node =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap

      val cls = clsctx(known_case)
      val PostFunction(post_f, post_params) = cases(cls)

      LetCall(new_names, DefnRef(Right(pre_f)), as,
        Jump(DefnRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}).attach_tag(tag)).attach_tag(tag)

    private def subst_jump_mixing_cases(sdloc: DefnLocMarker, as: Ls[TrivialExpr]): Node =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap
      val new_cases = cases.map {
        case (cls, PostFunction(post_f, post_params)) => (
          cls, 
          Jump(DefnRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}).attach_tag(tag)
        )
      }
      LetCall(new_names, DefnRef(Right(pre_f)), as,
        Case(scrut_new_name.get, new_cases.toList).attach_tag(tag)).attach_tag(tag)

    private def subst_jump_indirect(ic: IndirectConsumer, as: Ls[TrivialExpr]) =
      val defn_name = ic.defn
      val kind = ic.kind
      import IndirectSplitKind._
      kind match
        case FirstCase | AfterCase =>
          // it's impossible to have first case here because we have an EIndirectDestruct elim
          subst_jump_mixing_cases(first_case(defn_name), as)
        case JumpBeforeCase =>      
          val (name, args) = ic.where.marker match
            case LocMarker.MJump(name, args) => (name, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(ic.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          LetCall(new_names, DefnRef(Right(pre_f)), as,
            Jump(DefnRef(Right(name)), rebuild_args_from_marker(args, names_map)).attach_tag(tag)).attach_tag(tag)
        case CallBeforeCase =>
          val (names, defn2, args) = ic.where.marker match
            case LocMarker.MLetCall(names, defn, args) => (names, defn, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(ic.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          val new_names_2 = make_new_names_for_free_variables(names)
          val names_map_2 = names_map ++ names.zip(new_names_2).toMap
          val PostFunction(post_f, post_params) = single_post_map(ic.where)
          LetCall(new_names, DefnRef(Right(pre_f)), as,
            LetCall(new_names_2, DefnRef(Right(defn2)), rebuild_args_from_marker(args, names_map),
              Jump(DefnRef(Right(post_f)), post_params.map{x => Ref(names_map_2(x))}).attach_tag(tag)).attach_tag(tag)).attach_tag(tag)
    
    private def f(env: SubstEnv, node: Node): Node = node match
      case Result(res) => node
      case Case(scrut, cases) =>
        Case(scrut, cases map {
            (cls, arm) => (cls, f(env.copy(intros = env.intros + (scrut.str -> ICtor(cls.ident))), arm))
        }).copy_tag(node)
      case LetExpr(x, e1, e2) =>
        val intros2 = IntroductionAnalysis.getIntro(e1, env.intros).map { y => env.intros + (x.str -> y) }.getOrElse(env.intros)
        LetExpr(x, e1, f(env.copy(intros = intros2), e2)).copy_tag(node)
      case Jump(defnref, args) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        val defn = defnref.expectDefn
        if targets.indirect_consumer.contains(node.loc_marker) then
          changed = true
          val spec = targets.indirect_consumer(node.loc_marker)
          subst_jump_indirect(spec, args)
        else if targets.mixing_consumer.contains(node.loc_marker) && first_case.contains(targets.mixing_consumer(node.loc_marker)) then
          changed = true
          val target = targets.mixing_consumer(node.loc_marker)
          if targets.known_case.contains(node.loc_marker) then
            subst_jump_known_case(first_case(target), args, targets.known_case(node.loc_marker))
          else
            subst_jump_mixing_cases(first_case(target), args)
        else /* if targets.specialize.contains(node.loc_marker) then
          changed = true
          val spec = targets.specialize(node.loc_marker)
          val new_defn = specialized_map(spec.defn)
          val new_node = Jump(DefnRef(Right(new_defn)), args).attach_tag(tag)
          new_node
        else */
          node
      case LetCall(names, defnref, args, body) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        val defn = defnref.expectDefn
        val intros2 = updateIntroInfoAndMaintainMixingIntrosNew(name_defn_map, defn, node.loc_marker, env.intros, names)
        if targets.indirect_consumer.contains(node.loc_marker) then
          changed = true
          val spec = targets.indirect_consumer(node.loc_marker)
          subst_letcall_indirect(env, spec, names, args, body)
        else if targets.mixing_consumer.contains(node.loc_marker) && first_case.contains(targets.mixing_consumer(node.loc_marker)) then
          changed = true
          val target = targets.mixing_consumer(node.loc_marker)
          val new_node = if targets.known_case.contains(node.loc_marker) then
            subst_letcall_known_case(env, first_case(target), names, args, body, targets.known_case(node.loc_marker))
          else
            subst_letcall_mixing_cases(env, first_case(target), names, args, body)
          new_node
        else if names.tail.isEmpty && intros2.get(names.head.str).exists(_.isInstanceOf[IMix]) && targets.mixing_producer.contains(node.loc_marker) && first_case.contains(targets.mixing_producer(node.loc_marker)) then
          changed = true
          val target = targets.mixing_producer(node.loc_marker)
          val new_node = subst_letcall_mixing_cases(env, first_case(target), names, args, body)
          new_node
        else if targets.specialize.contains(node.loc_marker) then
          changed = true
          val spec = targets.specialize(node.loc_marker)
          val new_defn = specialized_map(spec.defn)
          val new_node = LetCall(names, DefnRef(Right(new_defn)), args, body).attach_tag(tag)
          new_node
        else
          LetCall(names, defnref, args, f(env.copy(intros = intros2), body)).copy_tag(node)
      def run(x: Program) =
        this.defs = Set.empty
        var defs = x.defs.map{ defn =>
          val intros = defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params)).getOrElse(Map.empty)
          val new_defn = defn.copy(body = f(SubstEnv(intros, defn), defn.body))
          new_defn
        }
        val main = x.main
        defs = defs ++ this.defs
        relink(main, defs)
        validate(main, defs)
        Program(x.classes, defs, main)


  private object NewSplitting:
    def run(x: Program) =
      val sta = NewSplittingTargetAnalysis()
      val targets = sta.run(x)
      val fs = NewFunctionSplitting(split_cache)
      val sr = fs.run(x.defs, targets)
      var y = x.copy(defs = sr.overwrite(x.defs) ++ sr.all_defs)
      relink(y.main, y.defs)
      validate(y.main, y.defs)
      activeAnalyze(y)
      recBoundaryAnalyze(y)
      val clsctx = make_class_ctx(y.classes)
      var changed = true
      while (changed)
        val scsr = NewSplittingCallSiteReplacement(clsctx, sr)
        y = scsr.run(y)
        relink(y.main, y.defs)
        validate(y.main, y.defs)
        activeAnalyze(y)
        recBoundaryAnalyze(y)
        changed = scsr.changed
      (y, sr)

  private def splitFunction(prog: Program) = NewSplitting.run(prog)

  private class ScalarReplacementTargetAnalysis extends Iterator:
    val ctx = MutHMap[Str, MutHMap[Str, Set[Str]]]()
    var name_map = Map[Str, Str]()
    private var intros = Map.empty[Str, Intro]

    private def addTarget(name: Str, field: Str, target: Str) =
      ctx.getOrElseUpdate(name, MutHMap()).updateWith(target) {
        case Some(xs) => Some(xs + field)
        case None => Some(Set(field))
      }
    
    private def checkTargets(defn: Defn, intros: Map[Str, Intro], args: Ls[TrivialExpr]) =
      val name = defn.name
      val params = defn.params
      val active = defn.newActiveParams
      args.map {
        case Ref(x) => intros.get(x.str)
        case _ => None
      }.zip(params).zip(active).foreach {
        case ((Some(ICtor(cls)), param), elim) if elim.exists(_.elim.isInstanceOf[ESelect]) && !elim.exists(_.elim == EDirect) =>
          elim.foreach {
            case ElimInfo(ESelect(field), _) => addTarget(name, field, param.str)
            case _ =>
          }
        case x @ ((_, param), elim) =>
      }

    override def iterate(x: Jump): Unit = x match
      case Jump(defnref, args) =>
        val defn = defnref.expectDefn
        checkTargets(defn, intros, args)

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)
    
    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        checkTargets(defn, intros, as)
        intros = updateIntroInfo(defn, intros, xs)
        e.accept_iterator(this)

    override def iterate(x: Case) = x match
      case Case(x, cases) =>
        cases foreach {
          (cls, arm) => 
            intros = intros + (x.str -> ICtor(cls.ident))
            arm.accept_iterator(this)
        }
    
    override def iterate(defn: Defn): Unit =
      intros = defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params)).getOrElse(Map.empty)
      defn.body.accept_iterator(this)

    override def iterate(x: Program): Unit =
      x.defs.foreach { x => x.accept_iterator(this) }
    
    private def sort_targets(fldctx: Map[Str, (Str, ClassInfo)], targets: Set[Str]) =
      val cls = fldctx(targets.head)._2
      cls.fields.filter(targets.contains(_))

    def run(x: Program) =
      x.accept_iterator(this)
      val clsctx = make_class_ctx(x.classes)
      val fldctx = x.classes.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      name_map = ctx.map { (k, _) => k -> fresh.make(k + "$S").str }.toMap
      ctx.map { (k, v) => k -> v.map{ (k, v) => (k, sort_targets(fldctx, v)) }.toMap }.toMap

  private enum ParamSubst:
    case ParamKeep
    case ParamFieldOf(orig: Str, field: Str)

  import ParamSubst._

  private def fieldParamName(name: Str, field: Str) = Name(name + "_" + field)

  private def fieldParamNames(targets: Map[Str, Ls[Str]]) =
    targets.flatMap { (k, fields) => fields.map { x => fieldParamName(k, x) } }

  private def paramSubstMap(params: Ls[Name], targets: Map[Str, Ls[Str]]) =
    params.flatMap { 
      case x if targets.contains(x.str) => None
      case x => Some(x.str -> ParamKeep)
    }.toMap ++ targets.flatMap {
      (k, fields) => fields.map { x => fieldParamName(k, x).str -> ParamFieldOf(k, x) }
    }.toMap


  private def newParams(params: Ls[Name], targets: Map[Str, Ls[Str]]) =
      params.filter(x => !targets.contains(x.str)) ++ fieldParamNames(targets)
  
  private class SelectionReplacement(target_params: Set[Str]):
    def run(node: Node): Node = f(node)

    private def f(node: Node): Node = node match
      case Result(res) => node
      case Jump(defn, args) => node
      case Case(scrut, cases) =>
        Case(scrut, cases.map { (cls, arm) => (cls, f(arm)) }).copy_tag(node)
      case LetExpr(x, Select(y,  cls, field), e2) if target_params.contains(y.str) =>
        LetExpr(x, Ref(fieldParamName(y.str, field)), f(e2)).copy_tag(node)
      case LetExpr(x, e1, e2) =>
        LetExpr(x, e1, f(e2)).copy_tag(node)
      case LetCall(names, defn, args, body) =>
        LetCall(names, defn, args, f(body)).copy_tag(node)
    

  private class ScalarReplacementDefinitionBuilder(name_map: Map[Str, Str], defn_param_map: Map[Str, Map[Str, Ls[Str]]]) extends Iterator:
    var sr_defs = MutHSet[Defn]()
    override def iterate(x: Defn) =
      if (name_map.contains(x.name))
        val targets = defn_param_map(x.name)
        val new_params = newParams(x.params, targets)
        val new_name = name_map(x.name)
        val new_def = Defn(
          fn_uid.make,
          new_name,
          new_params,
          x.resultNum,
          None,
          SelectionReplacement(targets.keySet).run(x.body),
        )
        sr_defs.add(new_def)

  private class ScalarReplacementCallSiteReplacement(defn_map: Map[Str, Str], defn_param_map: Map[Str, Map[Str, Ls[Str]]]):
    var fldctx = Map.empty[Str, (Str, ClassInfo)]

    private def susbtCallsite(defn: Defn, as: Ls[TrivialExpr], f: (Str, Ls[TrivialExpr]) => Node) =
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
      letlist.foldRight(new_node) { case ((x, y, field), node) => 
        LetExpr(x, Select(y, fldctx(field)._2, field), node).attach_tag_as[LetExpr](tag)
      }

    private def f(node: Node): Node = node match
      case Result(res) => node
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => Jump(DefnRef(Right(x)), y).copy_tag(node))
        else
          node
      case Case(scrut, cases) =>
        Case(scrut, cases.map { (cls, arm) => (cls, f(arm)) }).copy_tag(node)
      case LetExpr(name, expr, body) =>
        LetExpr(name, expr, f(body)).copy_tag(node)
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => LetCall(xs, DefnRef(Right(x)), y, f(e)).copy_tag(node))
        else
          LetCall(xs, defnref, as, f(e)).copy_tag(node)
  
    def run(x: Program) =
      val clsctx = make_class_ctx(x.classes)
      fldctx = x.classes.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      val y = Program(x.classes, x.defs.map(x => x.copy(body = f(x. body))), f(x.main))
      relink(y.main, y.defs)
      validate(y.main, y.defs)
      y

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private class ScalarReplacement:
    def run(x: Program) =
      val srta = ScalarReplacementTargetAnalysis()
      val worklist = srta.run(x)
      val name_map = srta.name_map
      val srdb = ScalarReplacementDefinitionBuilder(name_map, worklist)
      
      x.accept_iterator(srdb)

      val new_defs = x.defs ++ srdb.sr_defs

      val srcsp = ScalarReplacementCallSiteReplacement(name_map, worklist)
      val y  = Program(x.classes, new_defs, x.main)
      srcsp.run(y)
 
  def replaceScalar(prog: Program): Program =
    ScalarReplacement().run(prog)

  private class TrivialBindingSimplification:
    def run(x: Program) =
      val new_defs = x.defs.map(x => { x.copy(body = f(Map.empty, x.body))})
      relink(x.main, new_defs)
      Program(x.classes, new_defs, x.main)

    private def f(rctx: Map[Str, TrivialExpr], node: Node): Node = node match
      case Result(res) => Result(res.map(x => f(rctx, x))).copy_tag(node)
      case Jump(defn, args) => Jump(defn, args.map(x => f(rctx, x))).copy_tag(node)
      case Case(scrut, cases) => Case(f(rctx, scrut), cases.map { (cls, arm) => (cls, f(rctx, arm)) }).copy_tag(node)
      case LetExpr(x, Ref(Name(z)), e2) if rctx.contains(z) =>
        val rctx2 = rctx + (x.str -> rctx(z))
        f(rctx2, e2)
      case LetExpr(x, y @ Ref(Name(_)), e2) =>
        val rctx2 = rctx + (x.str -> y)
        f(rctx2, e2)
      case LetExpr(x, y @ Literal(_), e2) =>
        val rctx2 = rctx + (x.str -> y)
        f(rctx2, e2)
      case LetExpr(x, e1, e2) =>
        LetExpr(x, f(rctx, e1), f(rctx, e2)).copy_tag(node)
      case LetCall(names, defn, args, body) =>
        LetCall(names, defn, args.map(x => f(rctx, x)), f(rctx, body)).copy_tag(node)

    private def f(rctx: Map[Str, TrivialExpr], x: Expr): Expr = x match
      case Ref(name) => f(rctx, x)
      case Literal(lit) => x
      case CtorApp(name, args) => CtorApp(name, args.map(x => f(rctx, x)))
      case Select(name, cls, field) => Select(f(rctx, name), cls, field)
      case BasicOp(name, args) => BasicOp(name, args.map(x => f(rctx, x)))
    

    private def f(rctx: Map[Str, TrivialExpr], y: TrivialExpr): TrivialExpr = y match
      case Ref(Name(x)) if rctx.contains(x) =>
        rctx(x)
      case _ => y
    
    private def f(rctx: Map[Str, TrivialExpr], z: Name): Name =
      val Name(x) = z
      rctx.get(x) match 
        case Some(Ref(yy @ Name(y))) => yy
        case _ => z

  private class SelectionSimplification:
    var cctx: Map[Str, Map[Str, TrivialExpr]] = Map.empty

    def run(x: Program) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.copy(body = f(x.body)) })
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      Program(x.classes, new_defs, x.main)

    private def f(x: Node): Node = x match
      case Result(res) => x
      case Jump(defn, args) => x
      case Case(scrut, cases) => Case(scrut, cases map { (cls, arm) => (cls, f(arm)) }).copy_tag(x)
      case LetExpr(name, sel @ Select(y, cls, field), e2) if cctx.contains(y.str) =>
        cctx.get(y.str) match
          case Some(m) =>
            m.get(field) match 
              case Some(v) =>
                LetExpr(name, v.to_expr, f(e2)) .copy_tag(x)
              case None => 
                LetExpr(name, sel, f(e2)).copy_tag(x)
          case None => LetExpr(name, sel, f(e2)).copy_tag(x)
      case LetExpr(name, y @ CtorApp(cls, args), e2) =>
        val m = cls.fields.zip(args).toMap
        cctx = cctx + (name.str -> m)
        LetExpr(name, y, f(e2)).copy_tag(x)
      case LetExpr(name, e1, e2) =>
        LetExpr(name, e1, f(e2)).copy_tag(x)
      case LetCall(names, defn, args, body) =>
        LetCall(names, defn, args, f(body)).copy_tag(x)

  private class DestructSimplification:
    var cctx: Map[Str, Str] = Map.empty

    private def f(x: Node): Node = x match
      case Result(res) => x
      case Jump(defn, args) => x
      case Case(scrut, cases) if cctx.contains(scrut.str) =>
        cctx.get(scrut.str) match
          case Some(cls) =>
            val arm = cases.find(_._1.ident == cls).get._2
            f(arm)
          case None =>
            Case(scrut, cases map { (cls, arm) => (cls, f(arm)) }).copy_tag(x)
      case Case(scrut, cases) =>
        Case(scrut, cases map { (cls, arm) => (cls, f(arm)) }).copy_tag(x)
      case LetExpr(name, y @ CtorApp(cls, args), e2) =>
        cctx = cctx + (name.str -> cls.ident)
        LetExpr(name, y, f(e2)).copy_tag(x)
      case LetExpr(name, e1, e2) =>
        LetExpr(name, e1, f(e2)).copy_tag(x)
      case LetCall(names, defn, args, body) =>
        LetCall(names, defn, args, f(body)).copy_tag(x)

    def run(x: Program) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.copy(body = f(x.body)) })
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      Program(x.classes, new_defs, x.main)


  private def argsToStrs(args: Ls[TrivialExpr]) = {
    args.flatMap {
      case Ref(x) => Some(x.str)
      case _ => None
    }
  }

  private class DeadCodeElimination:
    val defs = MutHMap[Name, Int]()
    var uses = Map[(Name, Int), Int]()

    private def addDef(x: Name) =
      defs.update(x, defs.getOrElse(x, 0) + 1)
    
    private def f(x: Node): Node = x match
      case Result(res) => x
      case Jump(defn, args) => x
      case Case(scrut, cases) => Case(scrut, cases map { (cls, arm) => (cls, f(arm)) }).copy_tag(x)
      case LetExpr(name, expr, body) =>
        addDef(name)
        val ui = uses.get((name, defs(name)))
        ui match
          case Some(n) =>
            LetExpr(name, expr, f(body)).copy_tag(x)
          case None =>
            f(body)
      case LetCall(names, defn, args, body) =>
        names.foreach(addDef)
        val uis = names.map(name => uses.get(name, defs(name)))
        if uis.forall(_.isEmpty) then
          f(body)
        else
          LetCall(names, defn, args, f(body)).copy_tag(x)

    def run(x: Program) =
      val fns = DefRevPostOrdering.ordered(x.main, x.defs)
      val new_fns = fns.map { x =>
        defs.clear()
        uses = UsefulnessAnalysis(verbose).run(x)
        x.params.foreach(addDef)
        x.copy(body = f(x.body))
      }.toSet
      relink(x.main, new_fns)
      validate(x.main, new_fns)
      Program(x.classes, new_fns, x.main)

  private class RemoveTrivialCallAndJump:
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
      val kernel = LetExpr(le.name, new_expr, le.body).attach_tag_as[LetExpr](tag)
      (let_list, kernel)

    private def subst_let_expr_to_node(le: LetExpr, map: Map[Name, TrivialExpr]): Node =
      val (rev_let_list, kernel) = subst_let_expr(le, map)
      rev_let_list.foldLeft(kernel) {
        case (accu, (name, value)) => LetExpr(name, value.to_expr, accu).attach_tag_as[LetExpr](tag)
      }
    
    private def let_list_to_node(let_list: Ls[(Name, TrivialExpr)], node: Node): Node =
      let_list.foldRight(node) {
        case ((name, value), accu) => LetExpr(name, value.to_expr, accu).attach_tag_as[LetExpr](tag)
      }

    private def param_to_arg(param: TrivialExpr, map: Map[Name, TrivialExpr]): TrivialExpr = param match
      case Ref(x) if map.contains(x) => map(x)
      case x: Ref => x
      case x: Literal => x

    private def params_to_args(params: Ls[TrivialExpr], map: Map[Name, TrivialExpr]): Ls[TrivialExpr] =
      params.map(param_to_arg(_, map))

    private def f(x: Node): Node = x match
      case Result(res) => x
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn 
        val parammap = defn.params.zip(as).toMap
        (defn.specialized.isEmpty, defn.body) match
          case (true, Result(ys)) =>
            Result(params_to_args(ys, parammap)).attach_tag(tag)
          case (true, Jump(defnref, as2)) =>
            val node = let_list_to_node(defn.params.zip(as), Jump(defnref, as2).attach_tag(tag))
            node
          case (true, le @ LetExpr(y, e1, Result(Ref(z) :: Nil))) if y == z =>
            subst_let_expr_to_node(le, parammap)
          case (true, LetCall(xs2, defnref2, as2, Result(xs3))) if 
              xs2.zip(xs3).forall{ case (x, Ref(y)) => x == y; case _ => false } =>
            val node = let_list_to_node(
              defn.params.zip(as),
              LetCall(xs2, defnref2, as2, Result(xs3).attach_tag(tag)).attach_tag(tag))
            node
          case _ => x
      case Case(scrut, cases) => Case(scrut, cases.map { (cls, arm) => (cls, f(arm)) }).copy_tag(x)
      case LetExpr(name, expr, body) => LetExpr(name, expr, f(body)).copy_tag(x)
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        val parammap = defn.params.zip(as).toMap
        (defn.specialized.isEmpty, defn.body) match
          case (true, Result(ys)) =>
            val init = e |> f
            xs.zip(ys).foldRight(init) {
              case ((name, retval), node) =>
                LetExpr(name, param_to_arg(retval, parammap).to_expr, node).attach_tag(tag)
            }         
          case (true, Jump(defnref, as2)) =>
            val node = let_list_to_node(defn.params.zip(as), LetCall(xs, defnref, as2, f(e)).attach_tag(tag))
            node
          case (true, le @ LetExpr(y, e1, Result(Ref(z) :: Nil))) if y == z =>
            val (let_list, kernel) = subst_let_expr(le, parammap)
            let_list.foldLeft(
              LetExpr(kernel.name, kernel.expr,
                LetExpr(xs.head, Ref(kernel.name), e |> f).attach_tag(tag)).attach_tag(tag)) {
              case (accu, (name, value)) => LetExpr(name, value.to_expr, accu).attach_tag(tag)
            }
          case (true, LetCall(xs2, defnref2, as2, Result(xs3))) if
              xs2.zip(xs3).forall{ case (x, Ref(y)) => x == y; case _ => false } =>
            val node = let_list_to_node(defn.params.zip(as), LetCall(xs, defnref2, as2, f(e)).attach_tag(tag))
            node
          case _ => LetCall(xs, defnref, as, e |> f).copy_tag(x)

    def run(x: Program) =
      val new_defs = x.defs.map{ x => { x.copy(body = f(x.body)) }}
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      Program(x.classes, new_defs, x.main)

  def simplifyProgram(prog: Program): Program = {
    var changed = true
    var s = prog
    while (changed) {
      val ds = DestructSimplification()
      val ss = SelectionSimplification()
      val tbs = TrivialBindingSimplification()
      val rtcj = RemoveTrivialCallAndJump()
      val dce = DeadCodeElimination()
      var sf = s
      sf = ds.run(sf)
      activeAnalyze(sf)
      sf = ss.run(sf)
      activeAnalyze(sf)
      sf = tbs.run(sf) 
      activeAnalyze(sf)
      sf = rtcj.run(sf)
      activeAnalyze(sf)
      sf = dce.run(sf)
      activeAnalyze(sf)
      validate(sf.main, sf.defs)
      changed = s.defs != sf.defs
      s = sf
    }
    s
  }

  def activeAnalyze(prog: Program): Program =
    prog.accept_iterator(IntroductionAnalysis)
    NewEliminationAnalysis().run(prog)
    prog

  def optimize(prog: Program): Program = {
    var g = simplifyProgram(prog)
    g = activeAnalyze(g)
    g = recBoundaryAnalyze(g)

    val (g2, sr) = splitFunction(g)
    g = g2
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

    split_cache = Some(sr.into_cache(g))
    g
  }

  def recBoundaryAnalyze(prog: Program): Program =
    RecursiveBoundaryAnalysis.run(prog)
    prog

  private object RecursiveBoundaryAnalysis:
    import Expr._
    import Node._
    import Elim._
    import Intro._
    var count = 0
    def run(x: Program, conservative: Bool = false) =
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

  private class CallAnalysis:
    val cg = MutHMap[Str, MutHSet[Str]]()
    private var cur_defn: Opt[Defn] = None

    private def f(x: Node): Unit = x match
      case Result(res) => 
      case Jump(defn, args) => 
        if cur_defn.nonEmpty then
          cg.getOrElseUpdate(cur_defn.get.getName, MutHSet.empty) += defn.getName
      case Case(scrut, cases) => cases foreach { (cls, arm) => f(arm) }
      case LetExpr(name, expr, body) => f(body)
      case LetCall(names, defn, args, body) =>
        if cur_defn.nonEmpty then
          cg.getOrElseUpdate(cur_defn.get.getName, MutHSet.empty) += defn.getName
          f(body)

    def call_graph(x: Program): Map[Str, Set[Str]] = 
      cg.clear()
      cg.addAll(x.defs.map(x => x.getName -> MutHSet.empty))
      x.defs.foreach{ defn =>
        cur_defn = Some(defn)
        f(defn.body)
        cur_defn = None
      }
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
