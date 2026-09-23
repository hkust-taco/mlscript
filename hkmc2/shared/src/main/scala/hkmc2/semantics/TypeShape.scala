package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import codegen.{ErasedType, ErasedValueType}
import Elaborator.{Ctx, State}

/** A type interpretation, separate from the value shapes of the same reference syntax.
  * Compound types retain links to their operands so forward aliases need not be expanded eagerly.
  */
enum TypeShape:
  case Nominal(defn: ClassLikeDef)
  case Alias(symbol: TypeAliasSymbol, rhs: Opt[TypeResolution])
  case Union(left: TypeResolution, right: TypeResolution)
  case Intersection(left: TypeResolution, right: TypeResolution)
  case Function
  case Unit
  case Abstract

/** Candidates are published during elaboration. Erasure reads the resulting graph; it
  * never performs lookup or resolves an alias by inspecting an elaborated definition.
  */
final class TypeResolution(val source: Term, report: Ls[(Message, Opt[Loc])] => Unit) extends Host[TypeShape]:
  private var reported = false
  def showDbg(using DebugPrinter): Str = s"type of ${source.showDbg}"
  def publish(shape: TypeShape): Unit =
    if shapes.add(shape) then shapeListeners.foreach(_(shape))
  def listen(listener: TypeShape => Unit): Unit =
    shapeListeners += listener
    shapes.foreach(listener)
  def fail(messages: Ls[(Message, Opt[Loc])]): Unit = if !reported then
    reported = true
    report(messages)
  def validate(seen: Set[TypeResolution]): Unit = if !seen(this) then
    import TypeShape.*
    import Message.MessageContext
    val next = seen + this
    val ambiguousReceiver = source.withoutCaptures match
      case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.sizeCompare(1) > 0
      case sel: Term.NewSel => sel.hasAmbiguousClass
      case _ => false
    if shapes.isEmpty then fail(msg"This type has no resolved target" -> source.toLoc :: Nil)
    else if ambiguousReceiver || shapes.sizeCompare(1) > 0 then
      val candidates = source.withoutCaptures match
        case ref: Term.UnresolvedRef => ref.resolvedMembers.distinct.map: (prefix, member) =>
          msg"candidate: ${member.describe}" -> member.toLoc
        case _ => shapes.toList.flatMap:
          case Nominal(defn) => msg"candidate: ${defn.sym.describeKind}" -> defn.toLoc :: Nil
          case Alias(symbol, _) => msg"candidate: ${symbol.describeKind}" -> symbol.toLoc :: Nil
          case _ => Nil
      fail(msg"This type is ambiguous, as it has multiple resolved targets" -> source.toLoc :: candidates)
    shapes.foreach:
      case Alias(_, rhs) => rhs.foreach(_.validate(next))
      case Union(left, right) => left.validate(next); right.validate(next)
      case Intersection(left, right) => left.validate(next); right.validate(next)
      case _ => ()

  def erase(seen: Set[TypeResolution])(using Ctx, State): ErasedValueType =
    import TypeShape.*
    import Message.MessageContext
    validate(seen)
    if seen(this) || reported then ErasedType.Unknown
    else
      val next = seen + this
      shapes.toList match
        case Nominal(defn) :: Nil => defn.sym match
          case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
          case _ => ErasedType.Unknown
        case Alias(_, rhs) :: Nil => rhs.fold(ErasedType.Unknown)(_.erase(next))
        case Union(left, right) :: Nil => ErasedType.union(left.erase(next), right.erase(next))
        case Intersection(_, _) :: Nil | Abstract :: Nil => ErasedType.Unknown
        case Function :: Nil => ErasedType.Function(S(false))
        case Unit :: Nil => ErasedType.Unit
        case Nil =>
          ErasedType.Unknown
        case _ =>
          ErasedType.Unknown
