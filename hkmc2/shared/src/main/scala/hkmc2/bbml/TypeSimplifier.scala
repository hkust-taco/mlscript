package hkmc2.bbml

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import Type.*

final def printPol(pol: Bool): Str = pol match {
    case true => "+"
    case false => "-"
  }

class TypeSimplifier(tl: TraceLogger):
  import tl.{trace, log}
  
  def apply(pol: Bool, lvl: Int)(ty: GeneralType): GeneralType =
    ty |> simplifyStructure(pol, lvl) |> simplifyBounds(pol, lvl) |> simplifyForall
  
  def simplifyStructure(pol: Bool, lvl: Int)(ty: GeneralType): GeneralType =
    val done = MutSet.empty[InfVar]
    def goTV(tv: InfVar): InfVar =
      if done.add(tv) then
        tv.state.lowerBounds = tv.state.lowerBounds.map(goType)
        tv.state.upperBounds = tv.state.upperBounds.map(goType)
      tv
    def goType(ty: Type): Type =
    trace[Type](s"simplifyStructure($ty)", r => s"= $r"):
      ty match
      case tv: InfVar => goTV(tv)
      case _ =>
        ty.map(goType).simp
    def go(ty: GeneralType): GeneralType = ty match
      case ty: Type => goType(ty)
      case pt: PolyType =>
        pt.tvs.foreach(goTV)
        pt.map(go)
      case pf: PolyFunType => pf.map(go)
    go(ty)
  
  def simplifyBounds(pol: Bool, lvl: Int)(ty: GeneralType): GeneralType =
    
    type IV = InfVar
    
    object Analysis extends TypeTraverser:
      val posVars: MutSet[IV] = MutSet.empty
      val negVars: MutSet[IV] = MutSet.empty
      val recVars: MutSet[IV] = MutSet.empty
      
      val occsNum: MutMap[IV, Int] = MutMap.empty[IV, Int]
      
      var curPath: Ls[IV] = Nil
      var pastPathsSet: MutSet[IV] = MutSet.empty
      
      val varSubst: MutMap[IV, IV] = MutMap.empty
      
      val traversedTVs: MutSet[IV] = MutSet.empty
      
      def getRepr(tv: IV): IV = varSubst.get(tv) match {
        case S(tv2) =>
          varSubst.get(tv2) match {
            case S(tv3) =>
              varSubst += tv -> tv3
              // varSubst += tv2 -> tv3
              getRepr(tv3)
            case N => tv2
          }
        case N => tv
      }
      
      override def apply(pol: Bool)(ty: GeneralType): Unit =
        trace(s"Analyse[${printPol(pol)}] $ty  [${curPath.reverseIterator.mkString(" ~> ")}]"):
          ty match
            case ty if ty.lvl <= lvl =>
              log(s"Level is < $lvl")
            case tv: IV if { occsNum(tv) = occsNum.getOrElse(tv, 0) + 1; false } =>
            case tv: IV =>
              if varSubst.contains(tv) then return log(s"Already subst'd") // * If the IV was set to be substituted, it means it's been found recursive and we don't need to traverse it again
              var continue = true
              // if (!traversedTVs.contains(tv)) {
              if curPath.exists(_ is tv) then // TODO opt
                traversedTVs += tv
                val recPrefix = curPath.takeWhile(_ isnt tv)
                log(s"UNIFYING $tv with ${recPrefix.mkString(", ")}")
                recPrefix.foreach: tv2 =>
                  if tv2 isnt tv then
                    traversedTVs += tv2
                    var tvRepr = getRepr(tv2)
                    assert(traversedTVs(tvRepr))
                    if tvRepr isnt tv then
                      // assert(!varSubst.contains(tvRepr))
                      if tv.lvl === tvRepr.lvl /* && tvRepr.nameHint.isEmpty */ && !varSubst.contains(tvRepr) then {
                        varSubst += tvRepr -> tv
                      }
                      else if tv.lvl > tvRepr.lvl then varSubst += tv -> tvRepr
                      else if tvRepr.lvl > lvl && !varSubst.contains(tvRepr) then varSubst += tvRepr -> tv
                continue = false
              // TODO else??
              if traversedTVs.contains(tv) then log(s"Now already traversed $tv")
              else if pastPathsSet.contains(tv) then
                log(s"REC $tv")
                recVars += tv
                continue = false
              if continue then
                // log(s">>> $curPath")
                val oldPath = curPath
                curPath ::= tv
                
                if pol
                then posVars += tv
                else negVars += tv
                
                // log(s">>>> $curPath")
                // traversingTVs += tv
                // traversedTVs += tv
                super.apply(pol)(ty)
                // traversingTVs -= tv
                curPath = oldPath
            case _ =>
              val oldPath = curPath
              pastPathsSet ++= oldPath
              curPath = Nil
              super.apply(pol)(ty)
              curPath = oldPath
              pastPathsSet --= oldPath
              ()
    
    trace(s"Simplifying type $ty"):
      Analysis(pol)(ty)
    
    log("Unif-pre: " + Analysis.varSubst)
    Analysis.varSubst.valuesIterator.foreach { Analysis.getRepr(_) }
    // log("Unif-pst: " + Analysis.varSubst)
    
    log("Occ#: " + Analysis.occsNum.toSortedMap)
    log("Pos: " + Analysis.posVars.toSortedSet)
    log("Neg: " + Analysis.negVars.toSortedSet)
    log("Rec: " + Analysis.recVars.toSortedSet)
    log("Unif: " + Analysis.varSubst.toSortedMap)
    
    val cache: MutMap[IV, Type] = MutMap.empty
    val traversed: MutSet[IV] = MutSet.empty
    val transformed: MutMap[IV, Type] = MutMap.empty
    
    def subst(ty: GeneralType): GeneralType = trace[GeneralType](s"subst($ty)", r => s"= $r"):
      ty match
        case ty if ty.lvl <= lvl => ty // TODO NOPE
        case _tv: IV =>
          val tv = Analysis.getRepr(_tv)
          log(s"Repr: $tv")
          transformed.getOrElseUpdate(tv, {
            if Analysis.recVars.contains(tv) then
              log(s"It's recursive!")
              transformed += tv -> tv
            else transformed += tv ->
              // TypeBounds(TopType, BotType)(noProv) // TODO improve? creates lots of junk...
              Top // FIXME arbitrary
            // TODO rm self-cycles
            val newLBs = tv.state.lowerBounds.map(subst(_).monoOr(???))
            val newUBs = tv.state.upperBounds.map(subst(_).monoOr(???))
            tv.state.lowerBounds = newLBs
            tv.state.upperBounds = newUBs
            val isPos = Analysis.posVars.contains(tv)
            val isNeg = Analysis.negVars.contains(tv)
            // if (isPos && !isNeg && (Analysis.occsNum(tv) === 1 && {newLBs match { case (tv: IV) :: Nil => true; case _ => false }} || newLBs.forall(_.isSmall))) {
            if isPos && !isNeg && ({newLBs match { case (tv: IV) :: Nil => true; case _ => false }} || newLBs.forall(_ => true)) then {
            // if (isPos && !isNeg && ({newLBs match { case (tv: IV) :: Nil => true; case _ => false }})) {
              newLBs.foldLeft(Bot: Type)(_ | _)
            } else
            // if (isNeg && !isPos && (Analysis.occsNum(tv) === 1 && {newUBs match { case (tv: IV) :: Nil => true; case _ => false }} || newUBs.forall(_.isSmall))) {
            if isNeg && !isPos && ({newUBs match { case (tv: IV) :: Nil => true; case _ => false }} || newUBs.forall(_ => true)) then
            // if (isNeg && !isPos && ({newUBs match { case (tv: IV) :: Nil => true; case _ => false }})) {
              newUBs.foldLeft(Top: Type)(_ & _)
            else
              // tv.lowerBounds = newLBs
              // tv.upperBounds = newUBs
              tv
          })
        case ty: Type => ty.map(subst(_).monoOr(???))
        case pt: PolyType => pt.map(subst)
        case pf: PolyFunType => pf.map(subst)
    
    subst(ty)

  def simplifyForall(ty: GeneralType): GeneralType = ty match
    case PolyType(tvs, body) =>
      val visited = MutSet.empty[InfVar]
      object CollectTVs extends TypeTraverser:
        override def apply(pol: Boolean)(ty: GeneralType): Unit = ty match
          case v @ InfVar(_, _, state, _) =>
            if visited.add(v) then
              state.lowerBounds.foreach: bd =>
                apply(true)(bd)
              state.upperBounds.foreach: bd =>
                apply(false)(bd)
              super.apply(pol)(ty)
          case _ => super.apply(pol)(ty)
      CollectTVs(true)(ty)
      val newTvs = tvs.filter(visited)
      if newTvs.isEmpty then body
      else PolyType(newTvs, body)
    case _ => ty
