package ts2mls.types;

import scala.collection.mutable.HashMap

abstract class TSType {
  val priority: Int = 0
  override def toString(): String = ???
  def >(fieldName: String): TSType = throw new java.lang.Exception("Field is not allowed.")
}

case class TSTypeVariable(val name: String, val constraint: Option[TSType]) extends TSType {
  override val priority = 0

  override def toString(): String = s"$name'"

  def getConstraint(): String = constraint match {
    case Some(t) => s"$name' <: $t"
    case _ => ""
  }
}

case class TSNamedType(typeName: String) extends TSType {
  override val priority = 0

  override def toString(): String = typeName
}

case class TSEnumType(name: String) extends TSType {
  override val priority = 0

  override def toString(): String = name
}

case class TSTupleType(types: List[TSType]) extends TSType {
  override val priority = 0
  override def toString(): String = {
    val body = types.foldLeft("")((s, t) => s"$s$t, ")
    s"[${body.substring(0, body.length() - 2)}]"
  }
}

case class TSFunctionType(params: List[TSType], res: TSType, typeVars: List[TSTypeVariable]) extends TSType {
  override val priority = 1
  override def toString(): String = {
    val rhs = if (res.priority < priority && res.priority > 0) s"($res)" else res.toString()
    val body = 
      if (params.length == 0) res.toString()
      else {
        val ps = params.foldLeft("")((ls: String, p: TSType) => ls + p.toString() + ", ")
        s"(${ps.substring(0, ps.length() - 2)}) => ${rhs}"
      }

    val cons = typeVars.foldLeft("")((s, v) => {
      val c = v.getConstraint()
      if (c.isEmpty()) s else s"$s$c, "
    })

    if (cons.isEmpty()) body
    else s"$body where ${cons.substring(0, cons.length() - 2)}"
  }
}

case class TSClassType(name: String, members: Map[String, TSMemberType], typeVars: List[TSTypeVariable], parents: List[TSType])
  extends TSFieldType(members, parents) {
  override val priority = 0

  override def toString(): String = {
    val body = s"class $name"
    val cons = typeVars.foldLeft("")((s, v) => {
      val c = v.getConstraint()
      if (c.isEmpty()) s else s"$s$c, "
    })

    if (cons.isEmpty()) body
    else s"$body where ${cons.substring(0, cons.length() - 2)}"
  }
}

case class TSInterfaceType(name: String, members: Map[String, TSMemberType], typeVars: List[TSTypeVariable], parents: List[TSType])
  extends TSFieldType(members, parents) {
  override val priority = 0

  override def toString(): String = {
    val s = if (name.isEmpty()) ", " else "\n\t"
    val memString = members.foldLeft("")((str, it) => str + s"$s${it._1}: ${it._2.toString()}")
    val body =
      if (name.isEmpty()) s"{${memString.substring(2)}}"
      else s"interface $name {$memString\n}"

    val cons = typeVars.foldLeft("")((s, v) => {
      val c = v.getConstraint()
      if (c.isEmpty()) s else s"$s$c, "
    })

    if (cons.isEmpty()) body
    else s"$body where ${cons.substring(0, cons.length() - 2)}"
  }
}

case class TSArrayType(eleType: TSType) extends TSType {
  override val priority = 3
  override def toString(): String = 
    if (eleType.priority < priority && eleType.priority > 0) s"($eleType)[]"
    else s"$eleType[]"
}

abstract class TSStructuralType(lhs: TSType, rhs: TSType, notion: String) extends TSType {
  override val priority = 2

  override def toString(): String = {
    val slhs = lhs match {
      case f: TSFunctionType => s"($f)"
      case _ => lhs.toString()
    }

    val srhs = if (rhs.priority <= priority && rhs.priority > 0) s"($rhs)" else s"$rhs"

    s"$slhs $notion $srhs"
  }
}

case class TSUnionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "|")
case class TSIntersectionType(lhs: TSType, rhs: TSType) extends TSStructuralType(lhs, rhs, "&")

case class TSApplicationType(base: TSType, applied: List[TSType]) extends TSType {
  override val priority = 0

  override def toString(): String = {
    val appBody = applied.foldLeft("")((body, app) => s"$body, $app")
    s"$base<${appBody.substring(2)}>"
  }

  private lazy val applicationMap = base match {
    case TSClassType(_, _, typeVars, _) =>
      typeVars.zip(applied).foldLeft(Map[String, TSType]())((mp, v) => mp ++ Map(v._1.name -> v._2))
    case TSInterfaceType(_, _, typeVars, _) =>
      typeVars.zip(applied).foldLeft(Map[String, TSType]())((mp, v) => mp ++ Map(v._1.name -> v._2))
    case _ => Map[String, TSType]()
  }

  private def replace(t: TSType): TSType = t match {
    case TSTypeVariable(name, _) => applicationMap(name)
    case TSTupleType(types) => TSTupleType(types.map((s) => replace(s)))
    case TSFunctionType(params, res, cons) =>
      TSFunctionType(params.map((p) => replace(p)), replace(res), cons)
    case TSClassType(n, members, tv, c) =>
      TSClassType(n, members.map[String, TSMemberType]((m) => (m._1, TSMemberType(replace(m._2.base), m._2.modifier))), tv, c)
    case TSInterfaceType(n, members, tv, c) =>
      TSInterfaceType(n, members.map[String, TSMemberType]((m) => (m._1, TSMemberType(replace(m._2.base)))), tv, c)
    case TSArrayType(elementType) => TSArrayType(replace(elementType))
    case TSUnionType(lhs, rhs) => TSUnionType(replace(lhs), replace(rhs))
    case TSIntersectionType(lhs, rhs) => TSIntersectionType(replace(lhs), replace(rhs))
    case TSMemberType(base, mod) => TSMemberType(replace(base), mod)
    case _ => t
  }

  override def >(fieldName: String): TSType = base match {
    case f: TSFieldType => replace(f.>(fieldName))
    case _ => throw new java.lang.Exception("Field is not allowed.")
  }
}