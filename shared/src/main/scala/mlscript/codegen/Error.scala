package mlscript.codegen

final case class CodeGenError(message: String) extends Exception(message)
