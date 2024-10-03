package mlscript.compiler.mono
import mlscript.{Var, Lit}
import scala.collection.mutable.{Map => MutMap}
import scala.collection.immutable.ListMap


sealed abstract class MonoVal extends MonoValImpl
final case class TypeVal(name: String) extends MonoVal
final case class ObjVal(name: String, params: List[String], fields: MutMap[String, BoundedTerm]) extends MonoVal with ObjValImpl
final case class FuncVal(name: String, params: Option[List[String]], ctx: List[(String, BoundedTerm)]) extends MonoVal
final case class UnknownVal() extends MonoVal
/* 
 * VarVal represents the evaluation bounds of a function, which can change 
 * as we progress through evaluation.
 * TODO: Terribly unintuitive implementation, should attempt to refactor.
 */
final case class VarVal(vx: Int, version: Int, val getter: VarVal => BoundedTerm) extends MonoVal with VarValImpl
final case class LiteralVal(i: Lit | Boolean) extends MonoVal with LitValImpl
final case class PrimVal() extends MonoVal
final case class TupVal(fields: Map[Var, BoundedTerm]) extends MonoVal


class BoundedTerm(val values: Set[MonoVal]) extends BoundedTermImpl

object BoundedTerm {
  def apply(): BoundedTerm = new BoundedTerm(Set())
  def apply(singleVal: MonoVal): BoundedTerm = new BoundedTerm(Set(singleVal))
  def apply(valSet: Set[MonoVal]): BoundedTerm = new BoundedTerm(valSet)
}

trait MonoValImpl { self: MonoVal =>
  override def toString: String = this match {
    case FuncVal(name, params, ctx) => s"FuncVal(${name}, ${params.map(_.mkString("(",",",")")).getOrElse("None")}, ${ctx})"
    case LiteralVal(i) => s"LiteralVal(${i})"
    case ObjVal(name, params, fields) => s"ObjVal(${name}, ${fields})"
    case TypeVal(name) => s"TypeVal(${name})"
    case TupVal(fields) => s"TupVal(${fields})"
    case UnknownVal() =>  s"UnknownVal"
    case PrimVal() => s"PrimVal()"
    case VarVal(vx, version, _) => s"VarVal(${vx})"
  }
}

trait VarValImpl { 
  
}

trait LitValImpl { self: LiteralVal =>
  def asBoolean(): Option[Boolean] = self match {
    case LiteralVal(b: Boolean) => Some(b)
    case _ => None
  }
}

trait ObjValImpl { self: ObjVal =>
  def merge(other: ObjVal)(implicit instackExps: Set[Int]): ObjVal = {
    val allKeys = self.fields.keys
    val nFlds = allKeys.map(k => {
      val s1 = self.fields.get(k).get
      val s2 = other.fields.get(k).get
      if(instackExps.contains(s1.hashCode()) && instackExps.contains(s2.hashCode()))
        (k -> s1)
      else (k -> (s1 ++ s2))
    })
    ObjVal(self.name, self.params, MutMap(nFlds.toList*))
  }

}

trait BoundedTermImpl { self: BoundedTerm =>
  override def toString: String = self.values.map(_.toString).mkString(";")
  def getObjNames(): Set[String] = self.values.flatMap{
    case ObjVal(name, _, _) => Some(name)
    case _ => None
  }

  private def splitSpecifiedObjects(vs: Set[MonoVal], nms: Set[String]): (Set[MonoVal], Map[String, ObjVal]) = {
      val ret = vs.map{
        case o@ObjVal(name, params, fields) => 
          if (nms.contains(name)) {
            (None, Some(name -> o))
          } else {
            (Some(o), None)
          }
        case x => (Some(x), None)
      }.unzip
      val ret1 = ret._1.flatten
      val ret2 = ret._2.flatten.toMap
      (ret1, ret2)
    }
  
  /* 
   * Unfold VarVals into primitive values recursively.
   */
  def unfoldVars(implicit instackExps: Set[Int] = Set()): BoundedTerm = { 
    val (vars, others) = self.values.toList.map{
      case vx: VarVal => (Some(vx), None)
      case others => (None, Some(others))
    }.unzip
    val varSets: List[BoundedTerm] = vars.flatten.map(x => {
      val vSet = x.getter(x)
      if(!instackExps.contains(vSet.hashCode())) {
        vSet.unfoldVars(instackExps + vSet.hashCode())
      }
      else BoundedTerm(x)
    })
    varSets.foldLeft(BoundedTerm(others.flatten.toSet))((x, y) => (x ++ y)(instackExps + y.hashCode))
  }

  def asValue: Option[MonoVal] = {
    val tmp = this.unfoldVars
    if (tmp.values.size == 1) {
      Some(tmp.values.head)
    }
    else None
  }

  def getValue: Set[MonoVal] = {
    unfoldVars.values.filterNot(_.isInstanceOf[VarVal])
  }

  def literals2Prims: BoundedTerm = {
    val hasPrim = values.find(x => x.isInstanceOf[PrimVal] || x.isInstanceOf[LiteralVal]).isDefined
    if(hasPrim)
      BoundedTerm(values.filterNot(x => x.isInstanceOf[PrimVal] || x.isInstanceOf[LiteralVal])/* + PrimVal()*/)
    else this
  }

  /* 
   * Merge two BoundedTerms together recursively, including its component values & objects.
   */
  def ++(other: BoundedTerm)(implicit instackExps: Set[Int] = Set()): BoundedTerm = {
    if (this == other) this
    else {
      val mergingValNms = self.getObjNames().intersect(other.getObjNames())
      val (restVals1, mergingVals1) = splitSpecifiedObjects(self.values, mergingValNms)
      val (restVals2, mergingVals2) = splitSpecifiedObjects(other.values, mergingValNms)

      val ret = mergingValNms.map(nm => (mergingVals1.get(nm), mergingVals2.get(nm)) match {
        case (Some(x1: ObjVal), Some(x2: ObjVal)) => x1.merge(x2)(instackExps ++ Set(self.hashCode(), other.hashCode()))
        case _ => ???
      })

      var ret2 = restVals1 ++ restVals2
      // TODO: eliminate redundant values
      val retVals = BoundedTerm(ret ++ ret2)
      retVals
    }
  }

  def size: Int = values.size

  /*
   * Returns true if the bounds of other is larger than this.
   */
  def compare(other: BoundedTerm)(implicit instackExps: Set[Int] = Set()): Boolean = {
    if (instackExps.contains(this.hashCode()) && instackExps.contains(other.hashCode()))
      false
    else {
      if (this.values.find(_.isInstanceOf[PrimVal]).isEmpty && other.values.find(_.isInstanceOf[PrimVal]).isDefined)
        true
      else if (this.size != other.size)
        this.size < other.size
      else {
        val nms1 = this.getObjNames()
        val nms2 = other.getObjNames()
        if(nms1.equals(nms2)){
          val (rests1, objs1) = splitSpecifiedObjects(this.values, nms1)
          val (rests2, objs2) = splitSpecifiedObjects(other.values, nms1)
          nms1.find(nm => {
            val v1s = objs1.get(nm).get.fields
            val v2s = objs2.get(nm).get.fields
            v1s.keySet.find(k => v1s.get(k).get.compare(v2s.get(k).get)(using instackExps + this.hashCode() + other.hashCode())).isDefined
          }).isDefined
        }
        else true
      }
    }
  }
}