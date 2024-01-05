package ts2mls

import scala.collection.mutable.{HashMap, ListBuffer}
import types._
import mlscript.utils._

class TSNamespace(name: String, parent: Option[TSNamespace], allowReservedTypes: Boolean) {
  // name -> (namespace/type, export)
  private val subSpace = HashMap[String, (TSNamespace, Boolean)]()
  private val members = HashMap[String, (TSType, Boolean)]()
  private val cjsExport = HashMap[String, String]()

  // Write down the order of members.
  // Easier to check the output one by one.
  private val order = ListBuffer.empty[Either[String, String]]

  def isCommonJS = !cjsExport.isEmpty

  override def toString(): String = parent match {
    case Some(parent) if !parent.toString().isEmpty() => s"${parent.toString()}.$name"
    case _ => name
  }

  def derive(name: String, exported: Boolean): TSNamespace =
    if (subSpace.contains(name)) subSpace(name)._1 // If the namespace has appeared in another file, just return it
    else {
      val sub = new TSNamespace(name, Some(this), allowReservedTypes) // Not a top level module!
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
    else (members(name), tp) match {
      case ((cls: TSClassType, exp), itf: TSInterfaceType) =>
        members.update(name, (TSClassType(
          name, cls.members ++ itf.members, cls.statics, cls.typeVars,
          cls.parents, cls.constructor
        ), exported || exp))
      case ((itf1: TSInterfaceType, exp), itf2: TSInterfaceType) =>
        members.update(name, (TSInterfaceType(
          name, itf1.members ++ itf2.members, itf1.typeVars, itf1.parents,
          itf1.callSignature.fold(itf2.callSignature)(cs => Some(cs))
        ), exported || exp))
      case _ => ()
    }

  def `export`(name: String): Unit =
    if (members.contains(name))
      members.update(name, (members(name)._1, true))
    else if (subSpace.contains(name))
      subSpace.update(name, (subSpace(name)._1, true))

  def renameExport(from: String, to: String): Unit =
    if (members.contains(from)) {
      cjsExport.put(from, to)
      members.update(from, (members(from)._1, true))
    }
    else if (subSpace.contains(from)) {
      cjsExport.put(from, to)
      subSpace.update(from, (subSpace(from)._1, true))
    }
    else throw new Exception(s"member $from not found.")

  def exported(name: String): Boolean =
    if (members.contains(name)) members(name)._2
    else throw new Exception(s"member $name not found.")

  private def getNS(name: String): TSNamespace =
    if (subSpace.contains(name)) subSpace(name)._1
    else parent.fold(throw new Exception(s"namespace $name not found."))(p => p.getNS(name))

  def get(name: String): TSType =
    if (members.contains(name)) members(name)._1
    else parent.fold[TSType](TSReferenceType(name))(p => p.get(name)) // Default in es5

  def get(names: List[String]): TSType = names match {
    case head :: Nil => get(head)
    case head :: tails =>
      def run(ns: TSNamespace, list: List[String]): TSType =
        list match {
          case head :: Nil => ns.members(head)._1
          case head :: tails => run(ns.subSpace(name)._1, tails)
          case _ => throw new Exception(s"member ${names.mkString(".")} not found.")
        }
      run(getNS(head), tails)
    case _ => throw new Exception(s"member ${names.mkString(".")} not found.")
  }

  def exportWithAlias(name: String, alias: String): Unit =
    if (members.contains(name)) members(name)._1 match {
      case _: TSClassType => put(alias, TSRenamedType(alias, TSReferenceType(name)), true, false)
      case _: TSInterfaceType => put(alias, TSRenamedType(alias, TSReferenceType(name)), true, false)
      case _: TSTypeAlias => None // Type alias in ts would be erased.
      case tp => put(alias, TSRenamedType(alias, tp), true, false) // Variables & functions
    }
    else if (subSpace.contains(name)) put(alias, TSRenamedType(alias, TSReferenceType(name)), true, false)

  def containsMember(name: String, searchParent: Boolean = true): Boolean =
    if (parent.isEmpty) members.contains(name) else (members.contains(name) || (searchParent && parent.get.containsMember(name)))

  private lazy val typer =
    new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false,
      newDefs = true
    )

  private def generateNS(name: String, writer: JSWriter, indent: String): Unit = {
    val ss = subSpace(name)
    val realName = cjsExport.getOrElse(name, name)
    val exp = Converter.genExport(realName =/= name || ss._2)
    writer.writeln(s"${indent}${exp}declare module ${Converter.escapeIdent(realName)} {")
    ss._1.generate(writer, indent + "  ")
    writer.writeln(s"$indent}")
  }

  private def merge(name: String, writer: JSWriter, indent: String): Unit = {
    (members(name), subSpace(name)._1) match {
      case ((ref: TSReferenceType, exp), ns) => get(ref.nameList) match {
        case TSInterfaceType(itf, members, _, _, _) =>
          ns.subSpace.mapValuesInPlace {
            case (_, (ns, _)) => (ns, false)
          }
          ns.members.mapValuesInPlace {
            case (_, (mem, _)) => (mem, false)
          }
          members.foreach{
            case (name, TSMemberType(tp, _)) =>
              ns.put(name, tp, true, true)
          }
        case _ =>
          writer.writeln(s"$indent// WARNING: duplicate $name") // If merging is not supported, do nothing
      }
      case _ =>
        writer.writeln(s"$indent// WARNING: duplicate $name") // If merging is not supported, do nothing
    }
    generateNS(name, writer, indent)
  }

  def generate(writer: JSWriter, indent: String): Unit =
    order.toList.foreach((p) => p match {
      case Left(subName) if (!members.contains(subName)) =>
        generateNS(subName, writer, indent)
      case Right(name) =>
        if (typer.reservedTypeNames.contains(name) && !allowReservedTypes)
          writer.writeln(s"$indent// WARNING: type $name is reserved")
        else if (subSpace.contains(name))
          merge(name, writer, indent)
        else {
          val (mem, exp) = members(name)
          val realName = cjsExport.getOrElse(name, name)
          mem match {
            case inter: TSIntersectionType => // Overloaded functions
              writer.writeln(Converter.generateFunDeclaration(inter, realName, exp)(indent))
            case f: TSFunctionType =>
              writer.writeln(Converter.generateFunDeclaration(f, realName, exp)(indent))
            case overload: TSIgnoredOverload =>
              writer.writeln(Converter.generateFunDeclaration(overload, realName, exp)(indent))
            case _: TSClassType => writer.writeln(Converter.convert(mem, exp)(indent))
            case TSInterfaceType(name, _, _, _, _) if (name =/= "") => // TODO: rename?
              writer.writeln(Converter.convert(mem, exp)(indent))
            case _: TSTypeAlias => writer.writeln(Converter.convert(mem, exp)(indent))
            case TSRenamedType(name, original) =>
              writer.writeln(s"${indent}${Converter.genExport(exp)}val ${Converter.escapeIdent(realName)} = ${Converter.convert(original)("")}")
            case _ => writer.writeln(s"${indent}${Converter.genExport(exp)}val ${Converter.escapeIdent(realName)}: ${Converter.convert(mem)("")}")
          }
        }
      case _ => ()
    })
}

object TSNamespace {
  def apply(allowReservedTypes: Boolean) = new TSNamespace("", None, allowReservedTypes) // global namespace
}
