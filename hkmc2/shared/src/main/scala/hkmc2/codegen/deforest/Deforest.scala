package hkmc2
package codegen
package deforest

import scala.jdk.CollectionConverters.MapHasAsScala
import semantics.*
import syntax.Tree
import utils.*
import mlscript.utils.*, shorthands.*
import scala.collection.mutable
import hkmc2.syntax.{ImmutVal, MutVal, LetBind, HandlerBind, ParamBind, Fun, Ins}

case class ImportedInfo(seeThroughMods: Ls[ClsLikeBody])

object DeforestableSelect:
  // TermSymbol:
  //   - pattern variables (kind is parambind)
  //   - functions, let and val definition in an module (with an owner)
  // (ClassSymbol | ModuleOrObjectSymbol): class/object defined in a module.
  // ModuleOrObjectSymbols returned will always be an object symbol,
  // e.g., `_.tree.k is Obj`.
  // TopLevelSymbol: selecting `globalThis.Error` is fine...
  // and this selection gets a bot strategy
  def unapply(s: Select)(using eState: Elaborator.State): Opt[TermSymbol | ClassSymbol | ModuleOrObjectSymbol | TopLevelSymbol] =
    s.symbol match
    case S(sSym) if sSym.asTrm.isDefined =>
      val tSym = sSym.asTrm.get
      tSym.k match
        case (Ins | HandlerBind | MutVal) => None
        case (ImmutVal | LetBind | ParamBind) => Some(tSym)
        case Fun =>
          // if is class ctor, we should return ClassSymbol
          val isClassCtor =
            tSym.owner.exists(c => c.asCls.exists(cls => cls.name == s.name.name))
          if isClassCtor then tSym.owner.flatMap(_.asCls)
          else Some(tSym)
    case S(s) if s.asCls.isDefined || s.asObj.isDefined =>
      s.asCls orElse s.asObj
    case _ => s match
      case Select(
        Value.Ref(eState.globalThisSymbol, _),
        Tree.Ident("Error")
      ) => Some(eState.globalThisSymbol)
      case _ => None

object CtorRef:
  def unapply(s: Path)(using Elaborator.State): Option[ClassSymbol | ModuleOrObjectSymbol] =
    s match
      case DeforestableSelect(s: (ClassSymbol | ModuleOrObjectSymbol)) => Some(s)
      case Value.Ref(r, _) => r.asCls orElse r.asObj
      case _ => None

object CtorCall:
  def unapply(r: Result)(using Elaborator.State): Option[(ClassSymbol | ModuleOrObjectSymbol) -> Ls[Arg]] =
    r match
    case Call(CtorRef(ctor), args) => Some(ctor -> args)
    case CtorRef(ctor) if ctor.asObj.isDefined => Some(ctor -> Nil)
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
    extension (resultId: ResultId)
      def getResult = resultIdToResult(resultId)
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
    p
    // val defns = p.main.gatherDefns()
    // val (funs, clses) = defns.partitionMap:
    //   case f: FunDefn => L(f)
    //   case c: ClsLikeDefn => R(c)
    //   case _: ValDefn => die
    // ???
    


