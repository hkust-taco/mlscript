package mlscript.ucs

import collection.mutable.{Buffer, Map => MutMap, SortedMap => MutSortedMap, Set => MutSet}
import mlscript.{Loc, NuFunDef, NuTypeDef, TypeName, Var}
import mlscript.{Cls, Trt, Mxn, Als, Mod}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._

class ClassPatternInfo(scrutinee: ScrutineeData) {
  private val locations: Buffer[Loc] = Buffer.empty
  private var unappliedVarOpt: Opt[Var] = N
  private val parameters: MutSortedMap[Int, ScrutineeData] = MutSortedMap.empty

  def getParameter(index: Int): ScrutineeData =
    parameters.getOrElse(index, new ScrutineeData(S(scrutinee)))

  def addLocation(location: Opt[Loc]): Unit = locations ++= location

  def getUnappliedVar(default: => Var): Var =
    unappliedVarOpt.getOrElse {
      val unappliedVar = default
      unappliedVarOpt = S(unappliedVar)
      unappliedVar
    }
}

class TuplePatternInfo(scrutinee: ScrutineeData) {
  private val locations: Buffer[Loc] = Buffer.empty
  private val fields: MutSortedMap[Int, ScrutineeData] = MutSortedMap.empty

  def getField(index: Int): ScrutineeData =
    fields.getOrElse(index, new ScrutineeData(S(scrutinee)))
}

class ScrutineeData(parent: Opt[ScrutineeData]) {
  private var generatedVarOpt: Opt[Var] = N
  private val classLikePatterns: MutMap[TypeSymbol, ClassPatternInfo] = MutMap.empty
  // Currently we only support simple tuple patterns, so there is only _one_
  // slot for tuple patterns. After we support complex tuple patterns, we need
  // to extend this fields to a map from tuple arity to `TuplePatternInfo`.
  //    private val tuplePatterns: MutMap[Int, TuplePatternInfo] = MutMap.empty
  // If we support tuple pattern splice, we need a more expressive key in the
  // map's type.
  private var tuplePatternOpt: Opt[TuplePatternInfo] = N

  def getClassUnappliedVar(classLikeSymbol: TypeSymbol, default: => Var): Var =
    classLikePatterns.getOrElse(classLikeSymbol, new ClassPatternInfo(this)).getUnappliedVar(default)

  def getClassLikeParameter(classLikeSymbol: TypeSymbol, index: Int, location: Opt[Loc]): ScrutineeData = {
    val classPattern = classLikePatterns.getOrElse(classLikeSymbol, new ClassPatternInfo(this))
    classPattern.addLocation(location)
    classPattern.getParameter(index)
  }

  def getClassLikeParameter(classLikeSymbol: TypeSymbol, index: Int): ScrutineeData =
    classLikePatterns.getOrElse(classLikeSymbol, new ClassPatternInfo(this)).getParameter(index)

  def getTupleField(index: Int): ScrutineeData =
    tuplePatternOpt.getOrElse {
      val tuplePattern = new TuplePatternInfo(this)
      tuplePatternOpt = S(tuplePattern)
      tuplePattern
    }.getField(index)
}