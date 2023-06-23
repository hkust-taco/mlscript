package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._
import mlscript.utils._

class TSNamespace(name: String, parent: Option[TSNamespace]) {
  // name -> (namespace/type, export)
  private val subSpace = HashMap[String, (TSNamespace, Boolean)]()
  private val members = HashMap[String, (TSType, Boolean)]()

  // write down the order of members
  // easier to check the output one by one
  private val order = ListBuffer.empty[Either[String, String]]

  override def toString(): String = parent match {
    case Some(parent) if !parent.toString().isEmpty() => s"${parent.toString()}.$name"
    case _ => name
  }

  def derive(name: String, exported: Boolean): TSNamespace =
    if (subSpace.contains(name)) subSpace(name)._1 // if the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this)) // not a top level module!
      subSpace.put(name, (sub, exported))
      order += Left(name)
      sub
    }

  def put(name: String, tp: TSType, exported: Boolean, overrided: Boolean): Unit =
    if (!members.contains(name)) {
      order += Right(name)
      members.put(name, (tp, exported))
    }
    else if (overrided) members.update(name, (tp, exported))

  def `export`(name: String): Unit =
    if (members.contains(name))
      members.update(name, (members(name)._1, true))
    else if (subSpace.contains(name))
      subSpace.update(name, (subSpace(name)._1, true))

  def exported(name: String): Boolean =
    if (members.contains(name)) members(name)._2
    else throw new Exception(s"member $name not found.")

  def get(name: String): TSType =
    if (members.contains(name)) members(name)._1
    else parent.fold(throw new Exception(s"member $name not found."))(p => p.get(name))

  def getTop(name: String): Option[TSType] =
    if (members.contains(name)) members(name)._1 match {
      case cls: TSClassType => Some(TSReferenceType(cls.name))
      case itf: TSInterfaceType => Some(TSReferenceType(itf.name))
      case _: TSTypeAlias => None // type alias in ts would be erased.
      case tp => Some(tp) // variables & functions
    }
    else if (subSpace.contains(name)) Some(TSReferenceType(name))
    else None

  def containsMember(name: String, searchParent: Boolean = true): Boolean =
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))


  private def expStr(exp: Boolean) = if (exp) "export " else ""

  def generate(writer: JSWriter, indent: String): Unit =
    order.toList.foreach((p) => p match {
      case Left(subName) => {
        val ss = subSpace(subName)
        writer.writeln(s"${indent}${expStr(ss._2)}declare module ${Converter.escapeIdent(subName)} {")
        ss._1.generate(writer, indent + "  ")
        writer.writeln(s"$indent}")
      }
      case Right(name) => {
        val (mem, exp) = members(name)
        mem match {
          case inter: TSIntersectionType => // overloaded functions
            writer.writeln(Converter.generateFunDeclaration(inter, name, exp)(indent))
          case f: TSFunctionType =>
            writer.writeln(Converter.generateFunDeclaration(f, name, exp)(indent))
          case overload: TSIgnoredOverload =>
            writer.writeln(Converter.generateFunDeclaration(overload, name, exp)(indent))
          case _: TSClassType => writer.writeln(Converter.convert(mem, exp)(indent))
          case TSInterfaceType(name, _, _, _) if (name =/= "") =>
            writer.writeln(Converter.convert(mem, exp)(indent))
          case _: TSTypeAlias => writer.writeln(Converter.convert(mem, exp)(indent))
          case TSRenamedType(name, original) if (exp) =>
            writer.writeln(s"${indent}export val ${Converter.escapeIdent(name)} = ${Converter.convert(original)("")}")
          case _ => writer.writeln(s"${indent}${expStr(exp)}val ${Converter.escapeIdent(name)}: ${Converter.convert(mem)("")}")
        }
      }
    })
}

object TSNamespace {
  def apply() = new TSNamespace("", None) // global namespace
}
