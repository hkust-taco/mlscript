package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Pattern extends Located:

  case Alias(nme: VarSymbol, pattern: Pattern)
  case LitPat(literal: Literal)
  case Concrete(nme: VarSymbol)
  case Var(nme: BlockLocalSymbol)
  /**
    * Represents wildcard patterns or missing patterns which match everything.
    * Should be transformed from `Var("_")` or unrecognized terms.
    */
  case Empty(source: Term)
  case Class(nme: ClassSymbol, parameters: Opt[List[BlockLocalSymbol]], var refined: Bool)(val ident: Tree.Ident)
  case Tuple(fields: List[Pattern])
  case Record(entries: List[(VarSymbol -> Pattern)])
  
  def boundSymbols: Ls[Str -> Symbol] = ???
  
  def toLoc: Opt[Loc] = this match
    case LitPat(literal) => literal.toLoc
    case pat @ Class(_, _, _) => pat.ident.toLoc
  
  
  /* 
  def toLoc: Opt[Loc] = Loc(children)
  
  def children: Ls[Located] = this match
    case Alias(nme, pattern) =>
      nme :: pattern :: Nil
    case LitPat(literal) =>
      literal :: Nil
    case Concrete(nme) =>
      nme :: Nil
    case Var(nme) =>
      nme :: Nil
    case Empty(source) =>
      source :: Nil
    case Class(nme, parameters, refined) =>
      // nme :: parameters.getOrElse(Nil)
      ???
    case Tuple(fields: List[Pattern]) =>
      fields
    case Record(entries: List[(VarSymbol -> Pattern)]) =>
      // entries.iterator.flatMap { case (nme, als) => nme :: als :: Nil }.toList
      ???
  */
  
  def showDbg: Str = this match
    case Alias(nme, pattern) => s"($nme as $pattern)"
    case LitPat(literal) => literal.idStr
    case Concrete(nme) => s"`${nme.name}`"
    case Var(nme) => nme.toString
    case Empty(_) => "•"
    case Class(sym, ps, rfd) => (if rfd then "refined " else "") + (ps match {
      case N => sym.nme
      case S(parameters) => parameters.mkString(s"${sym.nme}(", ", ", ")")
    })
    case Tuple(fields) => fields.mkString("(", ", ", ")")
    case Record(Nil) => "{}"
    case Record(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
      

