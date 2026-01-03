package hkmc2
package codegen
package deforest

import scala.jdk.CollectionConverters.MapHasAsScala
import semantics.*
import syntax.Tree
import utils.*
import mlscript.utils.*, shorthands.*
import scala.collection.mutable
import hkmc2.Config.LiftDefns
import hkmc2.syntax.Keyword.in

case class ImportedInfo(seeThroughMods: Ls[ClsLikeBody])

// object DeforestableSelect:
//   def unapply(s: Select): Option[TermSymbol | ClassSymbol] =
//     s.symbol.collect: s =>
//       s match
//         case _: TermSymbol => 
//         case _: ClassSymbol =>
//         case _: ModuleOrObjectSymbol =>
//         case _: TypeAliasSymbol =>
//         case _: PatternSymbol =>
//         case _: TopLevelSymbol =>
      

// object CtorRef:
//   def unapply(s: Result): Option[ClassSymbol] =

// object 

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
    


