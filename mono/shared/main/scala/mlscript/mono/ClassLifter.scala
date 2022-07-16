package mlscript.mono

import mlscript.TypingUnit
import mlscript.NuTypeDef
import mlscript.NuFunDef
import scala.collection.mutable.ArrayBuffer
import mlscript.NuDecl
import mlscript.Term
import mlscript.TypeName
import mlscript.Var

// Flatten nested classes.
object ClassLifter:
  def lift(unit: TypingUnit): TypingUnit =
    val classes = ArrayBuffer[Term | NuDecl]()

    def go(tyDef: NuTypeDef, enclosing: Option[TypeName]): Unit =
      // Create a new `NuTypeDef` without nested `NuTypeDef`s.
      classes += NuTypeDef(
        tyDef.kind,
        tyDef.nme,
        tyDef.tparams,
        enclosing match {
          case Some(pnme) => (Var("parent"), Some(pnme)) :: tyDef.specParams
          case None => tyDef.specParams
        },
        tyDef.parents,
        TypingUnit(tyDef.body.entities.filter {
          case Right(tyDef: NuTypeDef) => false
          case _                       => true
        })
      )

      tyDef.body.entities.foreach {
        case Right(tyDef: NuTypeDef) => go(tyDef, Some(tyDef.nme))
        case _ => ()
      }

    unit.entities.foreach {
      case Left(term) => classes += term
      case Right(tyDef: NuTypeDef) => go(tyDef, None)
      case Right(funDef: NuFunDef) => classes += funDef
    }

    TypingUnit(classes.iterator.map {
      case term: Term => Left(term)
      case decl: NuDecl => Right(decl)
    }.toList)