package ts2mls.types

import ts2mls.TSNamespace
import ts2mls.DecWriter

trait Module {
  def >(name: String): TSType = ???
  def >>(name: String): TSNamespace = ???

  def visit(writer: DecWriter, prefix: String = ""): Unit = ???
}
