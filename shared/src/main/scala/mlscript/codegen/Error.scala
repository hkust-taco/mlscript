package mlscript.codegen

import scala.collection.mutable.ArrayBuffer

final case class CodeGenError(message: String) extends Exception(message)

final case class UnimplementedError(symbol: StubValueSymbol)
    extends Exception({
      val names = new ArrayBuffer[String]()
      var current: Option[StubValueSymbol] = Some(symbol)
      while (
        current match {
          case Some(sym) =>
            names += sym.lexicalName
            current = sym.previous
            true
          case None => false
        }
      ) ()
      val sep = ", "
      val concat = {
        val joined = names.mkString(sep)
        val pos = joined.lastIndexOf(sep)
        if (pos > -1) {
          joined.substring(0, pos) + " and " + joined.substring(pos + sep.length)
        } else {
          joined
        }
      }
      val be = if (names.lengthIs > 1) "are" else "is"
      s"$concat $be not implemented"
    })
