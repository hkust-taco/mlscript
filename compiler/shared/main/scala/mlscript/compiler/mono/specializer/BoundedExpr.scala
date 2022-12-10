package mlscript.compiler.mono.specializer

import mlscript.compiler.{Expr, UnitValue}
import mlscript.compiler.debug.Printable
import mlscript.compiler.debug.DebugOutput
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet

abstract class MonoValue {
  def toBoundedExpr = BoundedExpr(this)
  def toStringSafe(using Set[Int]) = this.toString()
}
case class ObjectValue(name: String, fields: MutMap[String, BoundedExpr]) extends MonoValue{
  override def toString(): String = fields.map(x => (s"${x._1}: ${x._2.toStringSafe}")).mkString(s"$name@{", ", ", "}")
  override def toStringSafe(using Set[Int]): String = fields.map(x => (s"${x._1}: ${x._2.toStringSafe}")).mkString(s"$name@{", ", ", "}")
  def merge(other: ObjectValue)(using inStackExps: Set[Int]): ObjectValue = {
    val allKeys = fields.keySet
    val nFlds = allKeys.map(k => {
      val s1 = fields.get(k).get
      val s2 = other.fields.get(k).get
      if(inStackExps.contains(s1.hashCode()) && inStackExps.contains(s2.hashCode()))
        (k -> s1)
      else (k -> (s1 ++ s2))
    })
    ObjectValue(name, MutMap(nFlds.toSeq: _*))
  }
  def mergeMut(other: ObjectValue)(using inStackExps: Set[Int]): Boolean = {
    val retVals = other.fields.map[Boolean]((k, s2) => {
      val s1 = fields.get(k).get
      if(!inStackExps.contains(s1.hashCode()) || !inStackExps.contains(s2.hashCode())){
        if(inStackExps.contains(s1.hashCode())){
          val tmp = BoundedExpr()
          s1.values.foreach(tmp.values.addOne(_))
          val ret = tmp += s2
          fields.update(k, tmp)
          ret
        } 
        else
          s1 += s2
      }
      else false
    })
    retVals.fold(false)(_ || _)
  }
  override def equals(x: Any): Boolean = {
    x match {
      case ObjectValue(xName, _) => name.equals(xName)
      case _ => false
    }
  }
}
case class FunctionValue(name: String, prm: List[String], ctx: List[(String, BoundedExpr)]) extends MonoValue{
  override def toString(): String = prm.mkString(s"$name(", ", ", ")") + ctx.map(x => (s"${x._1}: ${x._2.toStringSafe}")).mkString(" given {", ", ", "}")
  override def toStringSafe(using Set[Int]): String = prm.mkString(s"$name(", ", ", ")") + ctx.map(x => (s"${x._1}: ${x._2.toStringSafe}")).mkString(" given {", ", ", "}")
  override def equals(x: Any): Boolean = x match{
    case FunctionValue(xName, _, _) => name.equals(xName)
    case _ => false
  }
}
case class UnknownValue() extends MonoValue{
  val idValue = UnknownValue.refresh()
  override def toString(): String = s"?$idValue?"
}
object UnknownValue{
  var unknownCnt: Int = 0
  def refresh() = {
    unknownCnt += 1
    unknownCnt
  }
}
case class LiteralValue(i: BigInt | BigDecimal | Boolean | String | UnitValue) extends MonoValue{
  def asBoolean(): Option[Boolean] = i match{
    case x: Boolean => Some(x)
    case _ => None
  }
  override def toString(): String = i.toString()
}
case class PrimitiveValue() extends MonoValue{
  override def toString(): String = "*LIT*"
}

class BoundedExpr(val values: MutSet[MonoValue]) extends Printable {
  def this(singleVal: MonoValue) = this(MutSet(singleVal))
  def this() = this(MutSet())
  def this(vs: Set[MonoValue]) = this(MutSet(vs.toSeq: _*))
  def getDebugOutput: DebugOutput = DebugOutput.Plain(toStringSafe)
  def getObjNames() = values.flatMap{
    // case FunctionValue(name, body, prm, ctx) => Some(name)
    case ObjectValue(name, _) => Some(name)
    case _ => None
  }.toSet
  override def hashCode(): Int = values.hashCode()
  override def toString(): String = toStringSafe
  var updateCnt: Int = 0
  def toStringSafe(using printed: Set[Int] = Set()): String = {
    if(printed.contains(this.hashCode())) s"***"
    else values.map(_.toStringSafe(using printed + this.hashCode())).mkString("[", " | ", s"]")
  }
  def asValue: Option[MonoValue] = {
    if(values.size == 1) {
      Some(values.head)
    }
    else None
  }
  // def crossList(other: Set[List[MonoValue]]): Set[List[MonoValue]] = {
  //   for{
  //     x <- values;
  //     y <- other
  //   } yield x :: y
  // }
  // def crossP[A](other: Set[A]): Set[(MonoValue, A)] = {
  //   for{
  //     x <- values;
  //     y <- other
  //   } yield (x, y)
  // }

  private def split(vs: Set[MonoValue], nms: Set[String]): (Set[MonoValue], Map[String, ObjectValue]) = {
      val ret = vs.map{
        case o@ObjectValue(name, fields) => 
          if nms.contains(name) then {
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

  def ++(other: BoundedExpr)(using instackExps: Set[Int] = Set()): BoundedExpr = {
    if(this == other) this
    else {
      val mergingValNms = getObjNames().intersect(other.getObjNames())
      val (restVals1, mergingVals1) = split(values.toSet, mergingValNms)
      val (restVals2, mergingVals2) = split(other.values.toSet, mergingValNms)
      // val map2 = other.values.flatMap(x => if(values.fin(x)) then None else Some(x))
      val ret = mergingValNms.map(nm => (mergingVals1.get(nm), mergingVals2.get(nm)) match
        case (Some(x1: ObjectValue), Some(x2: ObjectValue)) => x1.merge(x2)(using instackExps ++ Set(this.hashCode(), other.hashCode()))
        case _ => ???
      )
      // println(s"get ${BoundedExpr(restVals1 ++ restVals2 ++ ret)}")
      var ret2 = restVals1 ++ restVals2
      if(ret2.count(x => (x.isInstanceOf[LiteralValue] || x.isInstanceOf[PrimitiveValue])) > 1){
        ret2 = ret2.filterNot(_.isInstanceOf[LiteralValue]) + PrimitiveValue()
      }
      val retVals = BoundedExpr(MutSet((ret2 ++ ret).toSeq: _*))
      retVals.updateCnt = this.updateCnt
      if(this.compare(retVals)) retVals.updateCnt += 1
      retVals
    }
  }

  def +=(other: BoundedExpr)(using instackExps: Set[Int] = Set()): Boolean = {
    val retVal = if(other != this) {
      val mergingValNms = getObjNames().intersect(other.getObjNames()).toSet
      val (_, mergingVals) = split(values.toSet, mergingValNms)
      var litCount = values.find(x => (x.isInstanceOf[LiteralValue] || x.isInstanceOf[PrimitiveValue]))
      val ret = other.values.map{
        case i: (LiteralValue | PrimitiveValue) => 
          if(litCount.isEmpty) {
            values.add(i) 
            true
          }
          else if(!litCount.get.isInstanceOf[PrimitiveValue]) {
            values.remove(litCount.get)
            values.add(PrimitiveValue())
            litCount = Some(PrimitiveValue())
            true
          }
          else false
        case o@ObjectValue(name, fields) => 
          mergingVals.get(name).fold[Boolean]{
            values.add(o)
            true
          }(v => {
            v.mergeMut(o)(using instackExps ++ Set(this.hashCode(), other.hashCode()))
          })
        case other => {
          values.add(other)
          true
        }
      }
      ret.fold(false)(_ || _)
    }
    else false
    if(retVal)  updateCnt += 1
    retVal
  }

  def size = values.size
  // lazy val eleCnt: Int = countEles
  def eleCnt(using objCallingStack: Set[String] = Set()): Int = {
    if(values.size == 0) {
      0
    }
    else {
      val seperated = values.map{
        case o: ObjectValue => (None, Some(o))
        case f: FunctionValue => (Some(1), None)
        case _: LiteralValue => (Some(1), None)
        case _: PrimitiveValue => (Some(100000), None)
        case UnknownValue() => (Some(1), None)
      }.unzip
      val (lits, objs) = (seperated._1.flatten, seperated._2.flatten)
      val objn = objs.map{ 
        case ObjectValue(name, fields) => 
          if(objCallingStack.contains(name))  1
          else {
            fields.map(x => x._2.eleCnt(using objCallingStack + name)).fold(0)(_ + _) + 1
          }
      }.fold(0)(_ + _)
      lits.fold(0)(_ + _) + objn
    }
  }
  def compare(other: BoundedExpr)(using instackExps: Set[Int] = Set()): Boolean = {
    if(instackExps.contains(this.hashCode()) && instackExps.contains(other.hashCode()))
      false
    else if(values.find(_.isInstanceOf[PrimitiveValue]).isEmpty && other.values.find(_.isInstanceOf[PrimitiveValue]).isDefined)
      true
    else if(this.size != other.size)
      this.size < other.size
    else{
      val nms1 = this.getObjNames()
      val nms2 = other.getObjNames()
      if(nms1.equals(nms2)){
        val (rests1, objs1) = split(this.values.toSet, nms1)
        val (rests2, objs2) = split(other.values.toSet, nms1)
        nms1.find(nm => {
          val v1s = objs1.get(nm).get.fields
          val v2s = objs2.get(nm).get.fields
          v1s.keySet.find(k => v1s.get(k).get.compare(v2s.get(k).get)(using instackExps + this.hashCode() + other.hashCode())).isDefined
        }).isDefined
      }
      else true
    }
    // (values.find(_.isInstanceOf[UnknownValue]), other.values.find(_.isInstanceOf[UnknownValue])) match{
    //   // case (Some(_), None) => true
    //   // case (None, Some(_)) => false
    // }
  }
}

// given Conversion[MutSet[? <: MonoValue], BoundedExpr] with 
//   def apply(x: MutSet[? <: MonoValue]): BoundedExpr = BoundedExpr(x)
// given Conversion[BoundedExpr, MutSet[? <: MonoValue]] with 
//   def apply(x: BoundedExpr): MutSet[? <: MonoValue] = x.values