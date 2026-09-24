package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import codegen.Erasure

/** A type interpretation, separate from the value shapes of the same reference syntax.
  * Compound types retain links to their operands so forward aliases need not be expanded eagerly.
  */
enum TypeShape:
  case Nominal(defn: ClassLikeDef)
  case Alias(symbol: TypeAliasSymbol, rhs: Opt[TypeResolution])
  case Union(left: TypeResolution, right: TypeResolution)
  case Intersection(left: TypeResolution, right: TypeResolution)
  case Tuple(fields: Ls[TypeResolution])
  case Record(source: Term.Rcd, fields: Ls[(RcdField, TypeResolution)])
  case Function(params: Term, result: TypeResolution)
  case Applied(base: TypeResolution, args: Ls[TypeResolution])
  // The same third-party symbol can have different inference in two exporters.
  // Retain its originating host so importing a result needs no whole-state copy.
  case Parameter(symbol: VarSymbol, host: Publisher.Data[Shape])
  // Synthesized generic arguments can retain inferred value shapes, for example
  // the element union of the Array supertype of a tuple. Written annotations
  // never introduce this case by inspecting their implementation.
  case Inferred(value: TermShape)
  case Captured(base: TypeResolution, thru: AnyDefinitionSymbol)
  case Unit
  case Dynamic
  case Abstract

/** Candidates are published during elaboration. Erasure reads the resulting graph; it
  * never performs lookup or resolves an alias by inspecting an elaborated definition.
  */
final class TypeResolution(val source: Term, report: Ls[(Message, Opt[Loc])] => Unit) extends Host[TypeShape]:
  private var reported = false
  def hasErrors: Bool = reported
  def showDbg(using DebugPrinter): Str = s"type of ${source.showDbg}"
  def publish(shape: TypeShape)(using NewResolverState): Unit =
    if currentShapes.add(shape) then notifyShapeListeners(shape)
  def listen(listener: ShapeListener[TypeShape])(using NewResolverState): Unit =
    subscribeToShapes(listener)
  def fail(messages: Ls[(Message, Opt[Loc])]): Unit = if !reported then
    reported = true
    report(messages)
  def validate(seen: Set[TypeResolution])(using Erasure): Unit = if !seen(this) then
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
      case Captured(base, _) => base.validate(next)
      case Applied(base, args) => base.validate(next); args.foreach(_.validate(next))
      case Function(_, result) => result.validate(next)
      case Tuple(fields) => fields.foreach(_.validate(next))
      case Record(_, fields) => fields.foreach(_._2.validate(next))
      case Union(left, right) => left.validate(next); right.validate(next)
      case Intersection(left, right) => left.validate(next); right.validate(next)
      case _ => ()

/** A type with its lexical type-parameter bindings. These bindings describe declared
  * interfaces, not constructor arguments or value-flow capture paths.
  */
final case class DeclaredType(resolution: TypeResolution, bindings: Map[VarSymbol, DeclaredType])
