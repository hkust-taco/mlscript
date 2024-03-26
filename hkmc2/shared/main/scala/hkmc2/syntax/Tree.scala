package hkmc2
package syntax

import mlscript.utils.*, shorthands.*


enum Tree:
  case Lit(lit: hkmc2.Lit)
  case Let(lhs: Tree, rhs: Tree, body: Opt[Tree])
  case Ident(name: Str)
  case Empty


