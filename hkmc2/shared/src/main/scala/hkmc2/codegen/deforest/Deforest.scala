package hkmc2
package codegen
package deforest

import scala.jdk.CollectionConverters.MapHasAsScala
import semantics.*
import syntax.Tree
import utils.*
import mlscript.utils.*, shorthands.*
import scala.collection.mutable
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, Fun, Ins}

case class ImportedInfo(seeThroughMods: Ls[ClsLikeBody])

type ResultId = Uid[Result]
type InstantiationId = Ls[ResultId]
type CtorCls = ClassLikeSymbol | Int
type SelField = TermSymbol | Int
type BranchId = CtorDtorId -> Opt[CtorCls]
type LabelId = LabelSymbol -> InstantiationId
type MatchOrLabelId = ResultId | LabelSymbol
type RestFunId = CtorDtorId | LabelId

object DeforestableSelect:
  // TermSymbol:
  //   - pattern variables (kind is parambind)
  //   - functions and val definition in an module (with an owner)
  // (ClassSymbol | ModuleOrObjectSymbol): class/object defined in a module.
  // ModuleOrObjectSymbols returned will always be an object symbol,
  // e.g., `_.tree.k is Obj`.
  // TopLevelSymbol: selecting from `globalThis`is fine
  def unapply(s: Select)(using eState: Elaborator.State): Opt[TermSymbol | ClassSymbol | ModuleOrObjectSymbol | TopLevelSymbol] =
    s.symbol match
    case S(sSym) if sSym.asTrm.isDefined =>
      val tSym = sSym.asTrm.get
      tSym.k match
        case (Ins | HandlerBind | MutVal) => None
        case _ if tSym.decl.exists(_.isInstanceOf[Param]) => Some(tSym)
        case ImmutVal =>
          // this can be a selection from module or a class
          tSym.owner.flatMap:
            // if selecting from a class, it is only
            // handleable if the selected field is
            // one of the cls params, because in deforestation
            // the known field information of a ctor is only its args
            case cls: ClassSymbol => cls.tree.clsParams.headOption
              .getOrElse(Nil)//FIXME? case when there are only aux parameter lists
              .find(_.id == tSym.id)
            case mod: ModuleOrObjectSymbol => Some(tSym)
            case _ => None
        case LetBind =>
          if tSym.owner.exists(c => c.asMod.isDefined) then None
          else Some(tSym)
        case Fun =>
          // if is class ctor, we should return ClassSymbol
          val isClassCtor =
            tSym.owner.exists(c => c.asCls.exists(cls => cls.name == s.name.name))
          if isClassCtor then tSym.owner.flatMap(_.asCls)
          else Some(tSym)
    case S(s) if s.asCls.isDefined || s.asObj.isDefined =>
      s.asCls orElse s.asObj
    case _ => s match
      case Select(Value.Ref(eState.globalThisSymbol, _), _) => Some(eState.globalThisSymbol)
      case _ => None

object PossibleDeforestTupSelect:
  def unapply(s: Result)(using eState: Elaborator.State): Opt[Symbol -> Int] =
    s match
    case Call(
      Select(Select(Value.Ref(runtimeSym, N), Tree.Ident("Tuple")), Tree.Ident("get")),
      Arg(N, Value.Ref(scrut, N)) :: Arg(N, Value.Lit(Tree.IntLit(n))) :: Nil
    ) if runtimeSym is eState.runtimeSymbol => S(scrut -> n.toInt)
    case _ => N
// (Int, Int): select the i_th field from TupleN
object DeforestTupSelect:
  def unapply(s: Result)(using pre: DeforestPreAnalyzer, eState: Elaborator.State): Opt[Symbol -> (Int, Int)] =
    given dState: Deforest.State = pre.dState
    s match
    case sel@PossibleDeforestTupSelect(scrut, ith) =>
      pre.res.getEnclosingMatchesForSel(sel.uid).find(_._1.getReferredSym is scrut).map:
        case (_, Some(tupSize: Int)) => scrut -> (ith, tupSize)
        case _ => die
    case _ => N
    

object CtorRef:
  def unapply(s: Path)(using Elaborator.State): Option[ClassSymbol | ModuleOrObjectSymbol] =
    s match
      case DeforestableSelect(s: (ClassSymbol | ModuleOrObjectSymbol)) => Some(s)
      case Value.Ref(r, _) => r.asCls orElse r.asObj
      case _ => None

object CtorCall:
  def unapply(r: Result)(using Elaborator.State): Option[(ClassSymbol | ModuleOrObjectSymbol | Int) -> Ls[Arg]] =
    r match
    case Call(CtorRef(ctor), args) => Some(ctor -> args)
    case CtorRef(ctor) if ctor.asObj.isDefined => Some(ctor -> Nil)
    case Tuple(false, args) => Some(args.size, args)
    case _ => None

object FunRef:
  def unapply(s: Path)(using Elaborator.State): Option[TermSymbol] = s match
    case DeforestableSelect(tSym: TermSymbol) if tSym.k is syntax.Fun => Some(tSym)
    case Value.Ref(l, disamb) =>
      for
        defnSym <- disamb
        tSym <- defnSym.asTrm
        // make sure this is not a ref to a class ctor
        if (tSym.k is syntax.Fun) && l.asCls.isEmpty
      yield
        tSym
    case _ => None

object Deforest:
  class State:
    val resultToResultId = new java.util.IdentityHashMap[Result, Uid[Result]].asScala
    val resultIdToResult = mutable.Map.empty[Uid[Result], Result]
    object ResultUidState extends Uid.Result.State
    extension (instId: InstantiationId)
      def mkFunName(using Elaborator.State): String =
        instId
          .map: i =>
            s"${i.getReferredFun.get.name}_$i"
          .mkString("_")
    extension (resultId: ResultId)
      def getResult = resultIdToResult(resultId)
      def getReferredSym: Symbol =
        resultId.getResult match
        case Value.Ref(s, _) => s
        case e => lastWords(s"assumption failed: $e is not a Value.Ref")
      def getReferredFun(using Elaborator.State): Option[TermSymbol] =
        resultId.getResult match
        case FunRef(f) => Some(f)
        case _ => None
    extension (r: Result)
      def uid = resultToResultId.get(r) match
        case None =>
          val id = ResultUidState.nextUid
          resultIdToResult(id) = r
          resultToResultId(r) = id
          id
        case Some(id) => id
  
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    elabState: Elaborator.State,
  ): Program =
    val dState = new State
    // TODO: handle see through imported modules
    val importInfo = ImportedInfo(Nil)
    val pre = new DeforestPreAnalyzer(importInfo, p.main)(using tl, elabState, dState)
    val constrCol = new DeforestConstraintsCollector(pre)
    val constrSol = new DeforestConstrainSolver(constrCol)
    val rewrite = new DeforestRewriter(constrSol)
    Program(p.imports, rewrite.newBody)
