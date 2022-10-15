package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._
import mlscript.utils._

class TSNamespace(name: String, parent: Option[TSNamespace]) {
  private val subSpace = HashMap[String, TSNamespace]()
  private val members = HashMap[String, TSType]()

  // write down the order of members
  // easier to check the output one by one
  private val order = ListBuffer.empty[Either[String, String]]

  def derive(name: String): TSNamespace =
    if (subSpace.contains(name)) subSpace(name) // if the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this))
      subSpace.put(name, sub)
      order += Left(name)
      sub
    }

  def put(name: String, tp: TSType): Unit =
    if (!members.contains(name)) {
      order += Right(name)
      members.put(name, tp)
    }
    else members.update(name, tp)

  def get(name: String): TSType =
    members.getOrElse(name,
      if (!parent.isEmpty) parent.get.get(name) else throw new Exception(s"member $name not found."))

  def containsMember(name: String, searchParent: Boolean = true): Boolean =
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))

  def generate(writer: JSWriter, indent: String): Unit =
    order.toList.foreach((p) => p match {
      case Left(subName) => {
        writer.writeln(s"${indent}namespace $subName {")
        subSpace(subName).generate(writer, indent + "  ")
        writer.writeln(s"$indent}")
      }
      case Right(name) => {
        val mem = members(name)
        mem match {
          case inter: TSIntersectionType => // overloaded functions
            writer.writeln(Converter.generateFunDeclaration(inter, name)(indent))
          case f: TSFunctionType =>
            writer.writeln(Converter.generateFunDeclaration(f, name)(indent))
          case overload: TSIgnoredOverload =>
            writer.writeln(Converter.generateFunDeclaration(overload, name)(indent))
          case _: TSClassType => writer.writeln(Converter.convert(mem)(indent))
          case TSInterfaceType(name, _, _, _) if (name =/= "") =>
            writer.writeln(Converter.convert(mem)(indent))
          case _: TSTypeAlias => writer.writeln(Converter.convert(mem)(indent))
          case _ => throw new AssertionError("only functions, classes, interfaces and type alias can be exported.")
        }
      }
    })
}

object TSNamespace {
  def apply() = new TSNamespace("", None) // global namespace
}
