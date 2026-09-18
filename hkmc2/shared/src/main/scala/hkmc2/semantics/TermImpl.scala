package hkmc2
package semantics

import scala.collection.mutable.{Buffer, Set as MutSet, LinkedHashSet}

import hkmc2.utils.*, shorthands.*
import syntax.*
import hkmc2.utils.Scope
import hkmc2.utils.Scope.scope
import hkmc2.document.*
import hkmc2.document.Document.*

import Elaborator.State
import hkmc2.typing.Type
import hkmc2.semantics.Elaborator.{Ctx, ctx}
import hkmc2.Message.MessageContext
import hkmc2.semantics.flow.{SelectionTarget, AppTarget}

import Term.*


// enum ReslTaregt:
//   case 

type AnyResolvable = Resolvable | NewResolvableImpl
// type AnyRef = Ref | SimpleRef | MemberRef

type NewResolvable = NewResolvableImpl & Term

trait NewResolvableImpl:
  self: MemberRef | NewSel =>
  var resolvedTargets: Ls[DefinitionSymbol[?]] = Nil // * filled during flow analysis
  // val resSym: FlowSymbol = FlowSymbol.simpleRef(self.sym.name)
  // var disamb: Opt[Disambiguation] = None // * filled during flow analysis
  var isErroneous: Boolean = false // * filled during resolution




