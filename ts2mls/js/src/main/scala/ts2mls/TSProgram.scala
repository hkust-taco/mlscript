package ts2mls;

import scala.scalajs.js
import js.Dynamic.{global => g}
import js.DynamicImplicits._
import scala.collection.mutable.HashMap
import ts2mls.types._

class TSProgram(filenames: Seq[String]) extends Module {
  private val program = TypeScript.createProgram(filenames)

  filenames.foreach((fn) => if (!program.fileExists(fn)) throw new java.lang.Exception(s"file ${fn} doesn't exist."))

  implicit private val checker: TSTypeChecker = TSTypeChecker(program.getTypeChecker())
  val globalNamespace: TSNamespace = TSNamespace()
  private val sourceFiles: Map[String, TSSourceFile] = filenames.map(filename => {
    filename -> TSSourceFile(program.getSourceFile(filename), globalNamespace)
  }).toMap

  override def >(name: String): TSType = sourceFiles.foldLeft[Option[TSType]](None)((res, cur) => res match {
    case None => try {Some(cur._2.>(name))} catch {case e: Exception => None}
    case _ => res
  }) match {
    case None => throw new java.lang.Exception(s"Symbol $name not found")
    case Some(t) => t
  }

  override def >>(name: String): TSNamespace = sourceFiles.foldLeft[Option[TSNamespace]](None)((res, cur) => res match {
    case None => try {Some(cur._2.>>(name))} catch {case e: Exception => None}
    case _ => res
  }) match {
    case None => throw new java.lang.Exception(s"Namespace $name not found")
    case Some(t) => t
  }

  def getNameSpace(namespace: String, filename: String): TSNamespace = sourceFiles.get(filename) match {
    case Some(sf) => sf.>>(namespace)
    case _ => throw new java.lang.Exception(s"Namespace $namespace not found")
  }

  def getSymbol(symbol: String, filename: String): TSType = sourceFiles.get(filename) match {
    case Some(sf) => sf.>(symbol)
    case _ => throw new java.lang.Exception(s"Symbol $symbol not found")
  }
  
  def getMLSType(name: String) = TSProgram.getMLSType(this.>(name))

  override def visit(writer: DecWriter, prefix: String): Unit = globalNamespace.visit(writer, prefix)
}

object TSProgram {
    def apply(filenames: Seq[String]) = new TSProgram(filenames)

    def getMLSType(tp: TSType): String = Converter.convert(tp)
}