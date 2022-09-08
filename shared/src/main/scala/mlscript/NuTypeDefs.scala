package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NuTypeDefs extends ConstraintSolver { self: Typer =>
  import TypeProvenance.{apply => tp}
  
  
  // * For now these are just unused stubs to be completed and used later
  
  case class TypedNuTypeDef(
    kind: TypeDefKind,
    nme: TypeName,
    tparamsargs: List[(TypeName, TypeVariable)],
    bodyTy: SimpleType,
    baseClasses: Set[TypeName],
    toLoc: Opt[Loc],
  )
  
  def typeTypingUnit(tu: TypingUnit)(implicit ctx: Ctx, raise: Raise): SimpleType = {
    // tu.entities
    ???
  }
  
  class TypedTypingUnit(tu: TypingUnit)(implicit ctx: Ctx, raise: Raise) {
    
  }
  
  
}

