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

class GraphOptimizer(fresh: Fresh, fn_uid: FreshInt, class_uid: FreshInt, tag: FreshInt, verbose: Bool = false):
  import GOExpr._
  import GONode._
  import Elim._
  import Intro._

  private def log(x: Any) = if verbose then println(x)

  private type ClassCtx = Map[Str, ClassInfo]

  private def make_class_ctx(classes: Set[ClassInfo]) = classes.map { case c @ ClassInfo(_, name, _) => (name, c) }.toMap

  private type FieldCtx = Map[Str, (Str, ClassInfo)]

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

    private def f(env: ElimEnv, x: GOExpr, loc: LocMarker): Unit = x match
      case Ref(name) => f(env, name, loc)
      case Literal(lit) =>
      case CtorApp(name, args) => args.foreach(f(env, _, loc))
      case Select(name, cls, field) => addElim(env, name, ESelect(field), loc)
      case BasicOp(name, args) => args.foreach(f(env, _, loc))

    private def f(env: ElimEnv, x: GONode): Unit = x match
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

    def run(x: GOProgram) = 
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
              env.elims.get(param.str).getOrElse(MutHSet.empty).toSet
          }
          changed |= (old != defn.newActiveParams)
        }

  private object IntroductionAnalysis extends GOIterator:
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

  private case class PreFunction(val name: Str, val retvals: Ls[Str]):
    override def toString = s"Pre($name, [$retvals])"
  private case class PostFunction(val name: Str, val params: Ls[Str]):
    override def toString = s"Post($name, [$params])"

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

  private def updateIntroInfoAndMaintainMixingIntrosNew(out: MutHMap[Str, LocMarker], defn: GODef, loc: LocMarker, intros: Map[Str, Intro], xs: Ls[Name]) =
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
  
  private def updateInputInfo(defn: GODef, intros: Map[Str, Intro], args: Ls[TrivialExpr]) =
    var all_none = true
    val ls = args.map {
      case Ref(Name(arg)) if intros.contains(arg) => all_none = false; Some(intros(arg))
      case _ => None
    }
    if all_none then defn.activeInputs else defn.activeInputs + ls

  
  private class NewSplittingTarget(
    val mixing_producer: Map[DefnLocMarker, Str],
    val mixing_consumer: Map[LocMarker, Str],
    val specialize: Map[LocMarker, DefnSpecialization],
    val known_case: Map[LocMarker, Str],
  )

  private class NewSplittingResult(
    val targets: NewSplittingTarget,
    val first_case: Map[Str, DefnLocMarker],
    val pre_map: Map[DefnLocMarker, PreFunction],
    val single_post_map: Map[DefnLocMarker, PostFunction],
    val mutli_post_map: Map[DefnLocMarker, Map[ClassInfo, PostFunction]],
    val pre_defs: Map[Str, GODef],
    val post_defs: Map[Str, GODef],
    val specialized_defs: Map[Str, GODef],
  ):
    def all_defs = pre_defs.values ++ post_defs.values ++ specialized_defs.values

  private enum IndirectSplitKind:
    case FirstCase        // a pre and multiple posts
    case JumpBeforeCase   // a pre
    case CallBeforeCase   // a pre and a post
    case AfterCase        // a pre and multiple posts

  private def get_indirect_split_kind(node: GONode, loc: LocMarker): Opt[IndirectSplitKind] =
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

  private class NewFunctionSplitting():
    private val first_case = MutHMap[Str, DefnLocMarker]()
    private val pre_map = MutHMap[DefnLocMarker, PreFunction]()
    private val single_post_map = MutHMap[DefnLocMarker, PostFunction]()
    private val mutli_post_map = MutHMap[DefnLocMarker, MutHMap[ClassInfo, PostFunction]]()
    private val pre_defs = MutHMap[Str, GODef]()
    private val post_defs = MutHMap[Str, GODef]()
    private val specialized_defs = MutHMap[Str, GODef]()
    private val split_memo = MutHSet[DefnLocMarker]()

    def run(defs: Set[GODef], targets: NewSplittingTarget): NewSplittingResult =
      val defs_map = defs.map(x => (x.name, x)).toMap
      targets.mixing_producer.values.foreach { defn_name =>
        val defn = defs_map(defn_name)
        split_at_first_case(SplitEnv(defn, n => n, None), defn.body)
      }
      targets.mixing_consumer.values.foreach { defn_name =>
        val defn = defs_map(defn_name)
        split_at_first_case(SplitEnv(defn, n => n, None), defn.body)
      }
      targets.specialize.values.foreach { case DefnSpecialization(defn_name, input, where, kind) =>
        import IndirectSplitKind._
        val defn = defs_map(defn_name)
        kind match
          case FirstCase => split_at_first_case(SplitEnv(defn, n => n, Some(input)), defn.body)
          case JumpBeforeCase | CallBeforeCase => split_at_jump_or_letcall(SplitEnv(defn, n => n, Some(input)), defn.body, where.marker)
          case AfterCase => split_at_first_case(SplitEnv(defn, n => n, Some(input)), defn.body)        
      }
      val result = NewSplittingResult(
        targets = targets,
        first_case = first_case.toMap,
        pre_map = pre_map.toMap, single_post_map = single_post_map.toMap,
        mutli_post_map = mutli_post_map.map { (k, v) => (k, v.toMap) }.toMap,
        pre_defs = pre_defs.toMap, post_defs = post_defs.toMap, specialized_defs = specialized_defs.toMap
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
      val defn: GODef,
      val accu: GONode => GONode,
      val specialize_on: Opt[Ls[Opt[Intro]]],
    )

    private def duplicate_and_keep_tags(node: GONode): GONode = node match
      case Result(res) => Result(res).copy_tag(node)
      case Jump(defn, args) => Jump(defn, args).copy_tag(node)
      case Case(scrut, cases) => Case(scrut, cases map { (cls, arm) => (cls, duplicate_and_keep_tags(arm)) }).copy_tag(node)
      case LetExpr(name, expr, body) => LetExpr(name, expr, duplicate_and_keep_tags(body)).copy_tag(node)
      case LetCall(names, defn, args, body) => LetCall(names, defn, args, duplicate_and_keep_tags(body)).copy_tag(node)

    private def split_at_jump_or_letcall(env: SplitEnv, node: GONode, marker: LocMarker): Opt[DefnLocMarker] = node match
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
        val pre_defn = GODef(
          fn_uid.make,
          pre_name.str,
          false,
          defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)
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
        val pre_defn = GODef(
          fn_uid.make,
          pre_name.str,
          false,
          defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)
        
        val post_name = fresh.make(defn.name + "$Y")
        val post_params_list = bindings_fv ++ all_fv.toList
        val post_params = post_params_list.map(Name(_))
        val new_defn = GODef(
          fn_uid.make,
          post_name.str,
          false,
          post_params,
          defn.resultNum,
          None,
          body)
        single_post_map.update(dloc, PostFunction(post_name.str, post_params_list))
        post_defs.update(post_name.str, new_defn)
        Some(dloc)
      case LetCall(xs, defnref, args, body) =>
        split_at_jump_or_letcall(env.copy(accu = n => env.accu(LetCall(xs, defnref, args, n).copy_tag(node))), body, marker)
    
    private def split_at_first_case(env: SplitEnv, node: GONode): Opt[DefnLocMarker] = node match
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
        val pre_defn = GODef(
          fn_uid.make,
          pre_name.str,
          false,
          env.defn.params,
          all_fv.size,
          None,
          pre_body)
        pre_map.update(dloc, PreFunction(pre_name.str, all_fv_list))
        pre_defs.update(pre_name.str, pre_defn)
        
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
            mutli_post_map
              .getOrElseUpdate(dloc, MutHMap.empty)
              .update(cls, PostFunction(post_name.str, post_params_list))
            post_defs.update(post_name.str, new_defn)
        }
        Some(dloc)
      case LetExpr(name, expr, body) =>
        split_at_first_case(env.copy(accu = n => env.accu(LetExpr(name, expr, n).copy_tag(node))), body)
      case LetCall(xs, defnref, args, body) =>
        split_at_first_case(env.copy(accu = n => env.accu(LetCall(xs, defnref, args, n).copy_tag(node))), body)
    
  private case class DefnSpecialization(val defn: Str, val input: Ls[Opt[Intro]], val where: DefnLocMarker, val kind: IndirectSplitKind)
  
  private class NewSplittingTargetAnalysis:
    private val known_case = MutHMap[LocMarker, Str]()
    private val specialize = MutHMap[LocMarker, DefnSpecialization]()
    private val mixing_consumer = MutHMap[LocMarker, Str]()
    private val mixing_producer = MutHMap[DefnLocMarker, Str]()
    private val name_defn_map = MutHMap[Str, LocMarker]()

    private case class SplitTargetEnv(
      val intros: Map[Str, Intro],
      val defn: GODef,
      val visited: MutHSet[Str],
    )

    private def checkTargets(env: SplitTargetEnv, defn: GODef, csloc: DefnLocMarker, args: Ls[TrivialExpr]) =
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
                    specialize += csloc.marker -> DefnSpecialization(name, asa.map(_._2), loc, split_kind.get)
                    if DestructAnalysis().firstDestructed(defn.body) == Some(param) then
                      known_case += csloc.marker -> cls
                    return
                case _ =>
          aux
        case (((Some(arg), Some(IMix(_))), param), elim) =>
          elim.foreach {
            case ElimInfo(EDestruct, _) =>
              name_defn_map.get(arg.str) match
                case Some(loc) => 
                  val target = (
                    loc match
                      case LocMarker.MLetCall(_, defn, _) => defn
                      case _ => throw GraphOptimizingError("Unexpected loc marker"))
                  mixing_producer += DefnLocMarker(env.defn.name, loc) -> target
                case None =>
            case ElimInfo(EIndirectDestruct, elimloc) =>
            case _ => 
          }
        case _ =>
      }

    private def f(env: SplitTargetEnv, node: GONode): Unit = node match
      case Result(res) =>
      case Jump(defnref, args) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        val defn = defnref.expectDefn
        checkTargets(env, defn, dloc, args)
        if (!env.visited.contains(defn.name))
          env.visited.add(defn.name)
          val intros = bindIntroInfo(env.intros, args, defn.params)
          f(env.copy(intros = intros, defn = defn), defn.body)
      case Case(x, cases) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        env.intros.get(x.str) match
          case Some(IMix(_))  => name_defn_map.get(x.str) match
            case Some(loc) =>
              mixing_producer += DefnLocMarker(env.defn.name, loc) -> (loc match
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
        if (!env.visited.contains(defn.name))
          env.visited.add(defn.name)
          val intros2 = bindIntroInfo(env.intros, args, defn.params)
          f(env.copy(intros = intros2, defn = defn), defn.body)
        val intros2 = updateIntroInfoAndMaintainMixingIntrosNew(name_defn_map, defn, node.loc_marker, env.intros, xs)
        f(env.copy(intros = intros2), e)

      def run(x: GOProgram) =
        x.defs.foreach { defn =>
          val env = SplitTargetEnv(
            defn.specialized.map(bindIntroInfoUsingInput(Map.empty, _, defn.params)).getOrElse(Map.empty),
            defn,
            MutHSet.empty)
          f(env, defn.body)
        }
        NewSplittingTarget(mixing_producer.toMap, mixing_consumer.toMap, specialize.toMap, known_case.toMap)

  private def recBoundaryMatched(producer: Opt[Int], consumer: Opt[Int]) =
    (producer, consumer) match
      case (Some(_), Some(_)) => false
      case _ => true
    
  private class NewSplittingCallSiteReplacement(
    clsctx: ClassCtx,
    split_result: NewSplittingResult,
  ):
    var changed = false
    private val name_defn_map = MutHMap[Str, LocMarker]()
    private val new_defs = MutHSet[GODef]()
    private var defs = Set.empty[GODef]

    private val pre_map = split_result.pre_map
    private val single_post_map = split_result.single_post_map
    private val mutli_post_map = split_result.mutli_post_map
    private val first_case = split_result.first_case

    private val targets = split_result.targets

    private case class SubstEnv(
      val intros: Map[Str, Intro],
      val defn: GODef,
    )

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

    private def rebuild_args_from_marker(args: Ls[LocMarker], map: Map[Str, Name]) =
      args.map {
        case LocMarker.MRef(x) => Ref(map(x))
        case LocMarker.MLit(x) => Literal(x)
        case _ => ???
      }

    private def subst_letcall_known_case(env: SubstEnv, sdloc: DefnLocMarker, xs: Ls[Name], as: Ls[TrivialExpr], body: GONode, known_case: Str): GONode =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap

      val cls = clsctx(known_case)
      val PostFunction(post_f, post_params) = cases(cls)

      LetCall(new_names, GODefRef(Right(pre_f)), as,
        LetCall(xs, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
          body).attach_tag(tag)).attach_tag(tag)

    private def subst_letcall_mixing_cases(env: SubstEnv, sdloc: DefnLocMarker, xs: Ls[Name], as: Ls[TrivialExpr], body: GONode): GONode =
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
      val new_jp = GODef(
        fn_uid.make,
        new_jp_name.str,
        true,
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
            LetCall(new_names_2, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))},
              Jump(GODefRef(Right(new_jp.name)), fv_list.map{x => Ref(names_map_2(x))}).attach_tag(tag)).attach_tag(tag))
      }

      LetCall(new_names, GODefRef(Right(pre_f)), as,
        Case(scrut_new_name.get, new_cases.toList).attach_tag(tag)).attach_tag(tag)

    private def subst_letcall_specialized(env: SubstEnv, spec: DefnSpecialization, xs: Ls[Name], as: Ls[TrivialExpr], body: GONode): GONode =
      val defn_name = spec.defn
      val kind = spec.kind
      import IndirectSplitKind._
      kind match
        case FirstCase | AfterCase =>
          // it's impossible to have first case here because we have an EIndirectDestruct elim
          subst_letcall_mixing_cases(env, first_case(defn_name), xs, as, body)
        case JumpBeforeCase =>      
          val (name, args) = spec.where.marker match
            case LocMarker.MJump(name, args) => (name, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(spec.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          LetCall(new_names, GODefRef(Right(pre_f)), as,
            LetCall(xs, GODefRef(Right(name)), rebuild_args_from_marker(args, names_map),
              body).attach_tag(tag)).attach_tag(tag)
        case CallBeforeCase =>
          val (names, defn2, args) = spec.where.marker match
            case LocMarker.MLetCall(names, defn, args) => (names, defn, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(spec.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          val new_names_2 = make_new_names_for_free_variables(names)
          val names_map_2 = names_map ++ names.zip(new_names_2).toMap
          val PostFunction(post_f, post_params) = single_post_map(spec.where)
          val node = LetCall(new_names, GODefRef(Right(pre_f)), as,
            LetCall(new_names_2, GODefRef(Right(defn2)), rebuild_args_from_marker(args, names_map),
              LetCall(xs, GODefRef(Right(post_f)), post_params.map{x => Ref(names_map_2(x))}, body).attach_tag(tag)).attach_tag(tag)).attach_tag(tag)
          node

    private def subst_jump_known_case(sdloc: DefnLocMarker, as: Ls[TrivialExpr], known_case: Str): GONode =
      val scrut = sdloc.marker match
        case LocMarker.MCase(scrut, cases) => scrut
        case _ => throw GraphOptimizingError("unexpected marker")
      val PreFunction(pre_f, pre_retvals) = pre_map(sdloc)
      val cases = mutli_post_map(sdloc)
      val (new_names, scrut_new_name) = make_new_names_for_free_variables(pre_retvals, scrut)
      val names_map = pre_retvals.zip(new_names).toMap

      val cls = clsctx(known_case)
      val PostFunction(post_f, post_params) = cases(cls)

      LetCall(new_names, GODefRef(Right(pre_f)), as,
        Jump(GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}).attach_tag(tag)).attach_tag(tag)

    private def subst_jump_mixing_cases(sdloc: DefnLocMarker, as: Ls[TrivialExpr]): GONode =
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
          Jump(GODefRef(Right(post_f)), post_params.map{x => Ref(names_map(x))}).attach_tag(tag)
        )
      }
      LetCall(new_names, GODefRef(Right(pre_f)), as,
        Case(scrut_new_name.get, new_cases.toList).attach_tag(tag)).attach_tag(tag)

    private def subst_jump_specialized(spec: DefnSpecialization, as: Ls[TrivialExpr]) =
      val defn_name = spec.defn
      val kind = spec.kind
      import IndirectSplitKind._
      kind match
        case FirstCase | AfterCase =>
          // it's impossible to have first case here because we have an EIndirectDestruct elim
          subst_jump_mixing_cases(first_case(defn_name), as)
        case JumpBeforeCase =>      
          val (name, args) = spec.where.marker match
            case LocMarker.MJump(name, args) => (name, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(spec.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          LetCall(new_names, GODefRef(Right(pre_f)), as,
            Jump(GODefRef(Right(name)), rebuild_args_from_marker(args, names_map)).attach_tag(tag)).attach_tag(tag)
        case CallBeforeCase =>
          val (names, defn2, args) = spec.where.marker match
            case LocMarker.MLetCall(names, defn, args) => (names, defn, args)
            case _ => throw GraphOptimizingError("unexpected marker")
          val PreFunction(pre_f, pre_retvals) = pre_map(spec.where)
          val new_names = make_new_names_for_free_variables(pre_retvals)
          val names_map = pre_retvals.zip(new_names).toMap
          val new_names_2 = make_new_names_for_free_variables(names)
          val names_map_2 = names_map ++ names.zip(new_names_2).toMap
          val PostFunction(post_f, post_params) = single_post_map(spec.where)
          LetCall(new_names, GODefRef(Right(pre_f)), as,
            LetCall(new_names_2, GODefRef(Right(defn2)), rebuild_args_from_marker(args, names_map),
              Jump(GODefRef(Right(post_f)), post_params.map{x => Ref(names_map_2(x))}).attach_tag(tag)).attach_tag(tag)).attach_tag(tag)
    
    private def f(env: SubstEnv, node: GONode): GONode = node match
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
        if targets.specialize.contains(node.loc_marker) then
          changed = true
          val spec = targets.specialize(node.loc_marker)
          subst_jump_specialized(spec, args)
        else if targets.mixing_consumer.contains(node.loc_marker) && first_case.contains(targets.mixing_consumer(node.loc_marker)) then
          changed = true
          val target = targets.mixing_consumer(node.loc_marker)
          if targets.known_case.contains(node.loc_marker) then
            subst_jump_known_case(first_case(target), args, targets.known_case(node.loc_marker))
          else
            subst_jump_mixing_cases(first_case(target), args)
        else
          node
      case LetCall(names, defnref, args, body) =>
        val dloc = DefnLocMarker(env.defn.name, node.loc_marker)
        val defn = defnref.expectDefn
        val intros2 = updateIntroInfoAndMaintainMixingIntrosNew(name_defn_map, defn, node.loc_marker, env.intros, names)
        if targets.specialize.contains(node.loc_marker) then
          changed = true
          val spec = targets.specialize(node.loc_marker)
          subst_letcall_specialized(env, spec, names, args, body)
        else if targets.mixing_consumer.contains(node.loc_marker) && first_case.contains(targets.mixing_consumer(node.loc_marker)) then
          changed = true
          val target = targets.mixing_consumer(node.loc_marker)
          val new_node = if targets.known_case.contains(node.loc_marker) then
            subst_letcall_known_case(env, first_case(target), names, args, body, targets.known_case(node.loc_marker))
          else
            subst_letcall_mixing_cases(env, first_case(target), names, args, body)
          new_node
        else if names.tail.isEmpty && intros2.get(names.head.str).exists(_.isInstanceOf[IMix]) && targets.mixing_producer.contains(dloc) && first_case.contains(targets.mixing_producer(dloc)) then
          changed = true
          val target = targets.mixing_producer(dloc)
          val new_node = subst_letcall_mixing_cases(env, first_case(target), names, args, body)
          new_node
        else
          LetCall(names, defnref, args, f(env.copy(intros = intros2), body)).copy_tag(node)
      def run(x: GOProgram) =
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
        GOProgram(x.classes, defs, main)


  private object NewSplitting:
    def run(x: GOProgram) =
      val sta = NewSplittingTargetAnalysis()
      val targets = sta.run(x)
      val fs = NewFunctionSplitting()
      val sr = fs.run(x.defs, targets)
      var y = x.copy(defs = x.defs ++ sr.all_defs)
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
      y

  def splitFunction(prog: GOProgram) = NewSplitting.run(prog)

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
    
    private def checkTargets(defn: GODef, intros: Map[Str, Intro], args: Ls[TrivialExpr]) =
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
        if (!visited.contains(defn.name))
          visited.add(defn.name)
          intros = bindIntroInfo(intros, args, defn.params)
          defn.body.accept_iterator(this)

    override def iterate(x: LetExpr): Unit = x match
      case LetExpr(x, e1, e2) =>
        intros = IntroductionAnalysis.getIntro(e1, intros).map { y => intros + (x.str -> y) }.getOrElse(intros)
        e2.accept_iterator(this)
    
    override def iterate(x: LetCall): Unit = x match
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        checkTargets(defn, intros, as)
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
  
  private class SelectionReplacement(target_params: Set[Str]):
    def run(node: GONode): GONode = f(node)

    private def f(node: GONode): GONode = node match
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
          SelectionReplacement(targets.keySet).run(x.body),
        )
        sr_defs.add(new_def)

  private class ScalarReplacementCallSiteReplacement(defn_map: Map[Str, Str], defn_param_map: Map[Str, Map[Str, Set[Str]]]):
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
      letlist.foldRight(new_node) { case ((x, y, field), node) => 
        LetExpr(x, Select(y, fldctx(field)._2, field), node).attach_tag_as[LetExpr](tag)
      }

    private def f(node: GONode): GONode = node match
      case Result(res) => node
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => Jump(GODefRef(Right(x)), y).copy_tag(node))
        else
          node
      case Case(scrut, cases) =>
        Case(scrut, cases.map { (cls, arm) => (cls, f(arm)) }).copy_tag(node)
      case LetExpr(name, expr, body) =>
        LetExpr(name, expr, f(body)).copy_tag(node)
      case LetCall(xs, defnref, as, e) =>
        val defn = defnref.expectDefn
        if (defn_param_map.contains(defn.name))
          susbtCallsite(defn, as, (x, y) => LetCall(xs, GODefRef(Right(x)), y, f(e)).copy_tag(node))
        else
          LetCall(xs, defnref, as, f(e)).copy_tag(node)
  
    def run(x: GOProgram) =
      val clsctx = make_class_ctx(x.classes)
      fldctx = x.classes.flatMap { case ClassInfo(_, name, fields) => fields.map { fld => (fld, (name, clsctx(name))) } }.toMap
      val y = GOProgram(x.classes, x.defs.map(x => x.copy(body = f(x. body))), f(x.main))
      relink(y.main, y.defs)
      validate(y.main, y.defs)
      y

  private def expectTexprIsRef(expr: TrivialExpr): Name = expr match {
    case Ref(name) => name
    case _ => ??? // how is a literal scalar replaced?
  }

  private class ScalarReplacement:
    def run(x: GOProgram) =
      val srta = ScalarReplacementTargetAnalysis()
      val worklist = srta.run(x)
      val name_map = srta.name_map
      val srdb = ScalarReplacementDefinitionBuilder(name_map, worklist)
      
      x.accept_iterator(srdb)

      val new_defs = x.defs ++ srdb.sr_defs

      val srcsp = ScalarReplacementCallSiteReplacement(name_map, worklist)
      val y  = GOProgram(x.classes, new_defs, x.main)
      srcsp.run(y)
 
  def replaceScalar(prog: GOProgram): GOProgram =
    ScalarReplacement().run(prog)

  private class TrivialBindingSimplification:
    def run(x: GOProgram) =
      val new_defs = x.defs.map(x => { x.copy(body = f(Map.empty, x.body))})
      relink(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

    private def f(rctx: Map[Str, TrivialExpr], node: GONode): GONode = node match
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

    private def f(rctx: Map[Str, TrivialExpr], x: GOExpr): GOExpr = x match
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

    def run(x: GOProgram) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.copy(body = f(x.body)) })
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

    private def f(x: GONode): GONode = x match
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

    private def f(x: GONode): GONode = x match
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

    def run(x: GOProgram) =
      val new_defs = x.defs.map(x => { cctx = Map.empty; x.copy(body = f(x.body)) })
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)


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
    
    private def f(x: GONode): GONode = x match
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

    def run(x: GOProgram) =
      val fns = GODefRevPostOrdering.ordered(x.main, x.defs)
      val new_fns = fns.map { x =>
        defs.clear()
        uses = UsefulnessAnalysis(verbose).run(x)
        x.params.foreach(addDef)
        x.copy(body = f(x.body))
      }.toSet
      relink(x.main, new_fns)
      validate(x.main, new_fns)
      GOProgram(x.classes, new_fns, x.main)

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

    private def subst_let_expr_to_node(le: LetExpr, map: Map[Name, TrivialExpr]): GONode =
      val (rev_let_list, kernel) = subst_let_expr(le, map)
      rev_let_list.foldLeft(kernel) {
        case (accu, (name, value)) => LetExpr(name, value.to_expr, accu).attach_tag_as[LetExpr](tag)
      }
    
    private def let_list_to_node(let_list: Ls[(Name, TrivialExpr)], node: GONode): GONode =
      let_list.foldRight(node) {
        case ((name, value), accu) => LetExpr(name, value.to_expr, accu).attach_tag_as[LetExpr](tag)
      }

    private def param_to_arg(param: TrivialExpr, map: Map[Name, TrivialExpr]): TrivialExpr = param match
      case Ref(x) if map.contains(x) => map(x)
      case x: Ref => x
      case x: Literal => x

    private def params_to_args(params: Ls[TrivialExpr], map: Map[Name, TrivialExpr]): Ls[TrivialExpr] =
      params.map(param_to_arg(_, map))

    private def f(x: GONode): GONode = x match
      case Result(res) => x
      case Jump(defnref, as) =>
        val defn = defnref.expectDefn 
        val parammap = defn.params.zip(as).toMap
        defn.body match
          case Result(ys) =>
            Result(params_to_args(ys, parammap)).attach_tag(tag)
          case Jump(defnref, as2) =>
            val node = let_list_to_node(defn.params.zip(as), Jump(defnref, as2).attach_tag(tag))
            node
          case le @ LetExpr(y, e1, Result(Ref(z) :: Nil)) if y == z =>
            subst_let_expr_to_node(le, parammap)
          case LetCall(xs2, defnref2, as2, Result(xs3)) if 
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
        defn.body match
          case Result(ys) =>
            val init = e |> f
            xs.zip(ys).foldRight(init) {
              case ((name, retval), node) =>
                LetExpr(name, param_to_arg(retval, parammap).to_expr, node).attach_tag(tag)
            }
          case le @ LetExpr(y, e1, Result(Ref(z) :: Nil)) if y == z =>
            val (let_list, kernel) = subst_let_expr(le, parammap)
            let_list.foldLeft(
              LetExpr(kernel.name, kernel.expr,
                LetExpr(xs.head, Ref(kernel.name), e |> f).attach_tag(tag)).attach_tag(tag)) {
              case (accu, (name, value)) => LetExpr(name, value.to_expr, accu).attach_tag(tag)
            }
          case LetCall(xs2, defnref2, as2, Result(xs3)) if
              xs2.zip(xs3).forall{ case (x, Ref(y)) => x == y; case _ => false } =>
            val node = let_list_to_node(defn.params.zip(as), LetCall(xs, defnref2, as2, f(e)).attach_tag(tag))
            node
          case _ => LetCall(xs, defnref, as, e |> f).copy_tag(x)

    def run(x: GOProgram) =
      val new_defs = x.defs.map{ x => { x.copy(body = f(x.body)) }}
      relink(x.main, new_defs)
      validate(x.main, new_defs)
      GOProgram(x.classes, new_defs, x.main)

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

  def activeAnalyze(prog: GOProgram): GOProgram =
    prog.accept_iterator(IntroductionAnalysis)
    NewEliminationAnalysis().run(prog)
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

  private object RecursiveBoundaryAnalysis:
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

  private class CallAnalysis:
    val cg = MutHMap[Str, MutHSet[Str]]()
    private var cur_defn: Opt[GODef] = None

    private def f(x: GONode): Unit = x match
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

    def call_graph(x: GOProgram): Map[Str, Set[Str]] = 
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
