package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*

/** WORKAROUND: the builtin operators are not declared functions, and several of them are overloaded
  * (for example, `+` adds numbers and concatenates strings). Until they are declared as properly
  * overloaded functions, new resolution and IR erasure approximate the result of an operator
  * application from the primitive classes of its operands, using the rules below. Both use the same
  * rules, so that the representation inferred for a slot an application flows into agrees with the
  * erased type of that application in the IR. Without them, an application has no shapes at all, and
  * a slot it flows into would only be inferred from its other inputs.
  *
  * The rules follow JavaScript semantics: resolution applies them only when targeting JavaScript,
  * since the Wasm backend implements operators with dynamically typed runtime intrinsics.
  * Remove this object, together with its uses in `NewResolver.builtinApplication` and
  * `ErasedType.builtinOperatorResult`, once the builtins are overloaded declarations.
  */
object BuiltinOperatorResults:

  /** The builtin classes the rules distinguish. `Int` is a subclass of `Num`. */
  enum PrimitiveClass:
    case Int, Num, Str, Bool, BigInt

  /** One alternative among the values an application can produce. */
  enum Alternative:
    /** Values of a primitive class. */
    case Of(primitive: PrimitiveClass)
    /** The values of the operand at this index. */
    case Operand(index: Int)

  import PrimitiveClass.*, Alternative.*

  private val comparisons = Set("==", "!=", "<", "<=", ">", ">=", "===", "!==")
  private val arithmetic = Set("+", "-", "*", "/", "%")

  /** Whether some operands make the rules approximate an application of `op` to `arity` operands. */
  def approximates(op: Str, arity: Int): Bool = arity match
    case 2 => comparisons(op) || arithmetic(op) || op === "," || op === "&&" || op === "||"
    case 1 => op === "!" || op === "typeof" || op === "-" || op === "+" || op === "~"
    case _ => false

  /** Alternatives whose union contains every value an application of the operator named `op` can produce,
    * given the primitive class of each operand (`N` when it is unknown or not one of the `PrimitiveClass` cases),
    * or `N` when no approximation is known. An application that throws produces no value, so it needs no
    * alternative.
    */
  def apply(op: Str, operands: Ls[Opt[PrimitiveClass]]): Opt[Ls[Alternative]] =
    def numeric(operand: Opt[PrimitiveClass]): Bool = operand match
      case S(Int | Num) => true
      case _ => false
    operands match
    case lhs :: rhs :: Nil => op match
      case op if comparisons(op) => S(Of(Bool) :: Nil)
      // The comma operator evaluates both operands and yields the second.
      case "," => S(Operand(1) :: Nil)
      // Lowering short-circuits these operators: they yield their second operand or a Boolean.
      case "&&" | "||" => S(Of(Bool) :: Operand(1) :: Nil)
      // JavaScript concatenates as soon as either operand is a string.
      case "+" if lhs.contains(Str) || rhs.contains(Str) => S(Of(Str) :: Nil)
      // Division and remainder can produce fractions or NaN, so only these preserve Int. Like the operator
      // signatures of InvalML's prelude, this ignores that results beyond the largest finite number overflow to
      // Infinity, which is not an Int: checked casts of these results to Int are elided.
      case "+" | "-" | "*" if lhs.contains(Int) && rhs.contains(Int) => S(Of(Int) :: Nil)
      case op if arithmetic(op) && numeric(lhs) && numeric(rhs) => S(Of(Num) :: Nil)
      // Mixing BigInt and Num operands throws.
      case op if arithmetic(op) && lhs.contains(BigInt) && rhs.contains(BigInt) => S(Of(BigInt) :: Nil)
      case _ => N
    case operand :: Nil => op match
      case "!" => S(Of(Bool) :: Nil)
      case "typeof" => S(Of(Str) :: Nil)
      case "-" | "+" if operand.contains(Int) => S(Of(Int) :: Nil)
      case "-" if operand.contains(Num) => S(Of(Num) :: Nil)
      case "-" if operand.contains(BigInt) => S(Of(BigInt) :: Nil)
      // Unary plus converts any operand to a number, and throws for a BigInt.
      case "+" => S(Of(Num) :: Nil)
      // Bitwise negation converts any operand other than a BigInt to a 32-bit integer.
      case "~" if operand.exists(_ isnt BigInt) => S(Of(Int) :: Nil)
      case _ => N
    case _ => N

end BuiltinOperatorResults
