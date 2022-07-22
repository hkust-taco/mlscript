package mlscript.codegen

enum PairedPunctuator(fore: String, back: String):
  case None extends PairedPunctuator("", "")
  case Angle extends PairedPunctuator("<", ">")
  case Brace extends PairedPunctuator("(", ")")
  case Bracket extends PairedPunctuator("[", "]")
  case Parenthesis extends PairedPunctuator("{", "}")

enum SourceCode:
  /**
   * A `Block` represents an block, separated and surrounded list of elements.
   * For example, a block of statements.
   */
  case Block(surroundedBy: PairedPunctuator, elementTail: String, elements: List[SourceCode])
  /**
   * A `Inline` represents an inline, separated and surrounded list of elements.
   * For example, `[a, b, c]`.
   */
  case Inline(surroundedBy: PairedPunctuator, elementTail: String, elements: List[SourceCode])
  /**
   * A `Chain` represents a series of elements. For example, expressions.
   */
  case Chain(elements: List[SourceCode])
  /**
   * An `Atom` represents an indivisible elements. For example, literals.
   */
  case Atom(value: String)
