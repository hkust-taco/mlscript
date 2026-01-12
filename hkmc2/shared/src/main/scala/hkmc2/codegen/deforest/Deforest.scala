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
  // e.g., `_.tree.k is Obj`
  def unapply(s: Select): Opt[TermSymbol | ClassSymbol | ModuleOrObjectSymbol] =
    s.symbol match
    case S(s) if s.asTrm.isDefined =>
      val tSym = s.asTrm.get
      tSym.k match
        case (Ins | HandlerBind | MutVal) => None
        case (ImmutVal | LetBind | Fun | ParamBind) => Some(tSym)
    case S(s) if s.asCls.isDefined || s.asObj.isDefined =>
      s.asCls orElse s.asObj
    case _ => None

object CtorRef:
  def unapply(s: Path): Option[ClassSymbol | ModuleOrObjectSymbol] =
    s match
      case DeforestableSelect(s: (ClassSymbol | ModuleOrObjectSymbol)) => Some(s)
      case Value.Ref(r, _) => r.asCls orElse r.asObj
      case _ => None


object Deforest:
  class State:
    val resultToResultId = new java.util.IdentityHashMap[Result, Uid[Result]].asScala
    val resultIdToResult = mutable.Map.empty[Uid[Result], Result]
    object ResultUidState extends Uid.Result.State
    extension (resultId: ResultId)
      def getResult = resultIdToResult(resultId)
    extension (r: Result)
      def uid = resultToResultId.getOrElseUpdate(r, ResultUidState.nextUid)
  
  def apply(p: Program)(using
    cfg: Config,
    tl: TL,
    raise: Raise,
    elabSt: Elaborator.State,
  ): Program =
    val state = new State
    // TODO: handle see through imported modules
    p
    // val defns = p.main.gatherDefns()
    // val (funs, clses) = defns.partitionMap:
    //   case f: FunDefn => L(f)
    //   case c: ClsLikeDefn => R(c)
    //   case _: ValDefn => die
    // ???
    


