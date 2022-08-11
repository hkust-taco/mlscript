package mlscript

import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MutSet}
import mlscript.utils._, shorthands._

class RepThmTest
  extends org.scalatest.funsuite.AnyFunSuite
{
  test("representation theorem") {
    val typer = new Typer(dbg = false, verbose = false, explainErrors = false)
    val typeDefs = Ls(
      TypeDef(Cls, TypeName("A"), Nil, Top),
      TypeDef(Cls, TypeName("B"), Nil, TypeName("A")),
      TypeDef(Cls, TypeName("C"), Nil, Top),
    )
    implicit val ctx: typer.Ctx = typer.processTypeDefs(typeDefs)(typer.Ctx.init, println(_))
    implicit val expandTupleFields: typer.ExpandTupleFields = false

    val top = typer.ExtrType(false)(typer.noProv)
    val bot = typer.ExtrType(true)(typer.noProv)
    val init = Ls(
      top,
      bot,
      typer.RecordType(Ls(Var("x") -> typer.FieldType(N, top)(typer.noProv)))(typer.noProv),
      typer.RecordType(Ls(Var("x") -> typer.FieldType(N, bot)(typer.noProv)))(typer.noProv),
      typer.RecordType(Ls(Var("y") -> typer.FieldType(N, top)(typer.noProv)))(typer.noProv),
      typer.RecordType(Ls(Var("y") -> typer.FieldType(N, bot)(typer.noProv)))(typer.noProv),
      typer.FunctionType(top, top)(typer.noProv),
      typer.FunctionType(top, bot)(typer.noProv),
      typer.FunctionType(bot, top)(typer.noProv),
      typer.FunctionType(bot, bot)(typer.noProv),
    ) // ::: typeDefs.map(td => typer.clsNameToNomTag(ctx.tyDefs(td.nme.name))(typer.noProv, ctx))
    val binops = Ls(
      // (_: typer.DNF) & (_: typer.DNF),
      // (_: typer.DNF) | (_: typer.DNF),
      (dnf1: typer.DNF, dnf2: typer.DNF) => typer.DNF.mk(typer.ComposedType(true, dnf1.toType(), dnf2.toType())(typer.noProv), true),
      (dnf1: typer.DNF, dnf2: typer.DNF) => typer.DNF.mk(typer.ComposedType(false, dnf1.toType(), dnf2.toType())(typer.noProv), true),
    )
    val unops = Ls(
      (dnf: typer.DNF) => typer.DNF.mk(typer.NegType(dnf.toType())(typer.noProv), true),
    )

    val dnfs = MutSet.from(init.map(typer.DNF.mk(_, true)))
    var count = 0
    var its = 0
    while (count =/= dnfs.size) {
      count = dnfs.size
      val tmp = dnfs.toSet
      // binops.foreach(f => dnfs ++= (for { x <- tmp; y <- tmp } yield f(x, y)))
      // unops.foreach(f => dnfs ++= tmp.map(f))
      for { f <- binops; x <- tmp; y <- tmp } dnfs += f(x, y)
      for { f <- unops; x <- tmp } dnfs += f(x)
      println(dnfs.size)
    }
    dnfs.foreach(println)
    println(s"No. of unique DNFs: ${dnfs.size}")
  }
}
