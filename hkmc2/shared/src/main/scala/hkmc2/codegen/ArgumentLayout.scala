package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*


/** Describes source parameter bindings in the complete argument tuple. Call-site coercions resolve
  * these positions at a known argument count; the callee emits the same bindings against its packed
  * rest argument. Optional elements carry the tuple length at which they are present, reserving the
  * trailing arguments before they can fill an optional slot.
  */
private[codegen] final class ArgumentLayout private (
  val required: Ls[Param],
  val minimumCount: Int,
  bindings: Ls[(Param, ArgumentLayout.Source)],
):
  /** The physical rest argument excludes the required prefix. Shift both indices and presence
    * thresholds together so its extraction code implements the complete-tuple bindings above. */
  lazy val extracted: Ls[(Param, ArgumentLayout.Source)] =
    val count = required.length
    bindings.iterator.drop(count).map((param, source) => param -> source.dropPrefix(count)).toList

  /** Unknown spread lengths leave only the required prefix at fixed argument positions.
    * So do counts below `minimumCount`: resolution already reports the arity error, and resolving
    * trailing slots from the end would check leading arguments against unrelated trailing types. */
  def expectedTypes(count: Opt[Int]): Ls[Opt[ErasedValueType]] = count match
    case S(n) if n >= minimumCount =>
      val types = bindings.iterator.flatMap: (param, source) =>
        source.argumentIndex(n).map(_ -> param.sym.erasedType)
      .toMap
      List.tabulate(n)(index => types.get(index).flatten)
    case _ => required.map(_.sym.erasedType)

private[codegen] object ArgumentLayout:
  enum Source:
    /** Negative indices count from the end. A presence threshold supplies null below that length;
      * it applies to optional leading slots, whose arguments must precede all trailing arguments.
      * Elements of the required prefix and trailing elements have none: the arity check ensures them. */
    case Element(index: Int, minimumLength: Opt[Int])
    /** Drop `start` leading arguments and `trailing` trailing arguments. */
    case Slice(start: Int, trailing: Int)

    def argumentIndex(count: Int): Opt[Int] = this match
      case Element(index, minimumLength) if minimumLength.forall(count >= _) =>
        val position = if index < 0 then count + index else index
        Option.when(position >= 0 && position < count)(position)
      case _ => N

    def dropPrefix(count: Int): Source = this match
      case Element(index, minimumLength) =>
        assert(index < 0 || index >= count, "An extracted element must follow the physical fixed prefix")
        Element(if index < 0 then index else index - count, minimumLength.map(_ - count))
      case Slice(start, trailing) =>
        assert(start >= count, "An extracted slice must follow the physical fixed prefix")
        Slice(start - count, trailing)

  /** Only trailing parameters need a packed binding plan; ordinary fixed/rest lists already have
    * the IR calling convention. The fixed prefix also defines the physical parameter signature. */
  def trailing(ps: ParamList): Opt[ArgumentLayout] = ps.variadic match
    case S(Variadic(rest, suffix @ (_ :: _))) =>
      val required = LoweredParamList.fixedPrefix(ps)
      val trailingCount = suffix.length
      val leading = ps.params.iterator.zipWithIndex.map: (param, index) =>
        param -> Source.Element(index, Option.when(index >= required.length)(index + trailingCount + 1))
      val trailing = suffix.iterator.zipWithIndex.map: (param, index) =>
        param -> Source.Element(index - trailingCount, N)
      val bindings = leading.toList :::
        (rest -> Source.Slice(ps.params.length, trailingCount)) :: trailing.toList
      S(new ArgumentLayout(required, required.length + trailingCount, bindings))
    case _ => N
