package mlscript

import scala.language.implicitConversions
import mlscript.utils._, shorthands._

final case class Message(bits: Ls[Message.Bit]) {
  def show: Str = {
    val ctx = ShowCtx.mk(typeBits)
    showIn(ctx)
  }
  def typeBits: Ls[Type] = bits.collect{ case Message.Code(t) => t }
  def showIn(ctx: ShowCtx): Str = {
    bits.map {
      case Message.Code(ty) => ty.showIn(ctx, 0)
      case Message.Text(txt) => txt
    }.mkString
  }
  def showDbg: Str = {
    bits.iterator.map {
      case Message.Code(trm) => s"$trm"
      case Message.Text(txt) => txt
    }.mkString
  }
  def +(that: Message): Message = Message(bits ++ that.bits)
}
object Message {
  
  def mkCtx(msgs: IterableOnce[Message], pre: Str = "'"): ShowCtx =
    ShowCtx.mk(msgs.iterator.flatMap(_.typeBits), pre)
  
  def join(msgs: Seq[Message]): Message = Message(msgs.iterator.flatMap(_.bits).toList)
  
  sealed abstract class Bit
  final case class Text(str: Str) extends Bit
  final case class Code(ty: Type) extends Bit
  implicit def fromType(ty: Type): Message = Message(Code(ty)::Nil)
  implicit def fromStr(str: Str): Message = Message(Text(str)::Nil)
  
  implicit class MessageContext(private val ctx: StringContext) {
    def msg(inserted: Message*): Message = {
      assert(inserted.length === ctx.parts.length - 1)
      val parts = ctx.parts.map(str => Text(StringContext(str).s()))
      val h = parts.head
      val t = parts.tail
      Message((h +: inserted.lazyZip(t).flatMap(_.bits :+ _)).toList)
    }
  }
  
}
