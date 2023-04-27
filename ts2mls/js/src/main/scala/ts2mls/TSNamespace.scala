package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._
import mlscript.utils._

// even though we don't use `export` keywords for some top-level variables/functions
// we still want to keep them (e.g., es5.d.ts built-in)
class TSNamespace(name: String, parent: Option[TSNamespace], keepUnexportedVars: Boolean) {
  // name -> (namespace/type, export)
  private val subSpace = HashMap[String, (TSNamespace, Boolean)]()
  private val members = HashMap[String, (TSType, Boolean)]()

  // write down the order of members
  // easier to check the output one by one
  private val order = ListBuffer.empty[Either[String, String]]

  def derive(name: String, exported: Boolean): TSNamespace =
    if (subSpace.contains(name)) subSpace(name)._1 // if the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this), false) // not a top level module!
      subSpace.put(name, (sub, exported))
      order += Left(name)
      sub
    }

  def put(name: String, tp: TSType, exported: Boolean): Unit =
    if (!members.contains(name)) {
      order += Right(name)
      members.put(name, (tp, exported))
    }
    else members.update(name, (tp, exported))

  def get(name: String): TSType =
    if (members.contains(name)) members(name)._1
    else if (!parent.isEmpty) parent.get.get(name)
    else throw new Exception(s"member $name not found.")

  def containsMember(name: String, searchParent: Boolean = true): Boolean =
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))


  private def expStr(exp: Boolean) = if (exp || keepUnexportedVars) "export " else ""

  def generate(writer: JSWriter, indent: String): Unit =
    order.toList.foreach((p) => p match {
      case Left(subName) => {
        val ss = subSpace(subName)
        writer.writeln(s"${indent}${expStr(ss._2)}declare module $subName {")
        ss._1.generate(writer, indent + "  ")
        writer.writeln(s"$indent}")
      }
      case Right(name) => {
        val (mem, exp) = members(name)
        mem match {
          case inter: TSIntersectionType => // overloaded functions
            writer.writeln(Converter.generateFunDeclaration(inter, name, exp || keepUnexportedVars)(indent))
          case f: TSFunctionType =>
            writer.writeln(Converter.generateFunDeclaration(f, name, exp || keepUnexportedVars)(indent))
          case overload: TSIgnoredOverload =>
            writer.writeln(Converter.generateFunDeclaration(overload, name, exp || keepUnexportedVars)(indent))
          case _: TSClassType => writer.writeln(Converter.convert(mem, exp)(indent))
          case TSInterfaceType(name, _, _, _) if (name =/= "") =>
            writer.writeln(Converter.convert(mem, exp)(indent))
          case _: TSTypeAlias => writer.writeln(Converter.convert(mem, exp)(indent))
          case _ => writer.writeln(s"${indent}${expStr(exp || keepUnexportedVars)}val $name: ${Converter.convert(mem)("")}")
        }
      }
    })
}

object TSNamespace {
  def apply(keepUnexportedVars: Boolean) = new TSNamespace("", None, keepUnexportedVars) // global namespace
}
