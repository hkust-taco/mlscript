package ts2mls.types

import ts2mls.DecWriter

abstract class TSAccessModifier
case object Public extends TSAccessModifier
case object Private extends TSAccessModifier {
  override def toString(): String = "-"
}
case object Protected extends TSAccessModifier {
  override def toString(): String = "o"
}

case class TSMemberType(val base: TSType, val modifier: TSAccessModifier = Public) extends TSType {
  override val priority = base.priority
  override def toString(): String = modifier match {
    case Public => base.toString
    case _ => s"$modifier $base"
  }
}

abstract class TSFieldType(members: Map[String, TSMemberType], parents: List[TSType]) extends TSType {
  private def findInParents(name: String): Option[TSType] = parents.foldLeft[Option[TSType]](None)((res, p) => res match {
    case None => try {Some(p.>(name))} catch {case e: Exception => None}
    case _ => res
  })

  override def >(fieldName: String): TSType = members.get(fieldName) match {
    case Some(t) => t
    case _ => findInParents(fieldName) match {
      case Some(t) => t
      case _ => throw new java.lang.Exception(s"Field \"$fieldName\" not found.")
    }
  }
}
