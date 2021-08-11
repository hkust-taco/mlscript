package mlscript

import fansi.{ Str => FStr }
import scala.language.implicitConversions
import mlscript.utils._, shorthands._

final case class Message(bits: Ls[Message.Bit]) {
  def show: FStr = {
    val ctx = ShowCtx.mk(typeBits)
    showIn(ctx)
  }
  def typeBits: Ls[Type] = bits.collect{ case Message.Code(t) => t }
  def showIn(ctx: ShowCtx): FStr = {
    FStr.join(bits.map {
      case Message.Code(ty) => ty.showIn(ctx, 0): FStr // TODO make Type use FStr
      case Message.Text(txt) => txt
    }: _*)
  }
  def showDbg: Str = {
    FStr.join(bits.map {
      case Message.Code(trm) => s"$trm": FStr
      case Message.Text(txt) => txt
    }: _*).toString
  }
  def +(that: Message): Message = Message(bits ++ that.bits)
}
object Message {
  
  def mkCtx(msgs: IterableOnce[Message], pre: Str = "'"): ShowCtx =
    ShowCtx.mk(msgs.iterator.flatMap(_.typeBits), pre)
  
  def join(msgs: Seq[Message]): Message = Message(msgs.iterator.flatMap(_.bits).toList)
  
  sealed abstract class Bit
  final case class Text(str: FStr) extends Bit
  implicit def fromFStr(str: FStr): Message = Message(Text(str)::Nil)
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
