package mlscript.codegen

final case class CodeGenError(message: String) extends Exception(message)

final case class UnimplementedError(symbol: StubValueSymbol)
    extends Exception(s"${symbol.shortName} is not implemented")
