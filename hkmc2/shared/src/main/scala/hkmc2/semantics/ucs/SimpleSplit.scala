package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*

object SimpleSplit:
  private def display(split: SimpleSplit): Str =
    import PatternStub.*
    def go(split: SimpleSplit): Str = split match
      case Accept => "accept"
      case Reject => ""
      case Branch(pattern, consequence, alternative) =>
        val pat = pattern.display
        val con = display(consequence)
        val alt = display(alternative)
        s"$pat ->"
          + "\n" + con.indent("  ")
          + (if alt.isEmpty then "" else s"\n$alt")
    go(split)

enum SimpleSplit extends ProductWithTail:
  case Branch(pattern: PatternStub,
              consequence: SimpleSplit,
              alternative: SimpleSplit)
  case Accept
  case Reject
  
  def display: Str = SimpleSplit.display(this)
  

