package ts2mls.types

import ts2mls.TSNamespace

trait Module {
  def >(name: String): TSType = ???
  def >>(name: String): TSNamespace = ???
}
