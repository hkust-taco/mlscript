package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Pattern extends AutoLocated:

  case Alias(nme: VarSymbol, pattern: Pattern)
  case Lit(literal: Literal)
  case Concrete(nme: VarSymbol)
  case Var(nme: BlockLocalSymbol)
  /**
    * Represents wildcard patterns or missing patterns which match everything.
    * Should be transformed from `Var("_")` or unrecognized terms.
    */
  case Empty(source: Term)
  case ClassLike(sym: ClassSymbol | ModuleSymbol, trm: Term, parameters: Opt[List[BlockLocalSymbol]], var refined: Bool)(val tree: Tree)
  case Tuple(fields: List[Pattern])
  case Record(entries: List[(VarSymbol -> Pattern)])
  
  def boundSymbols: Ls[Str -> Symbol] = ???
  
  def subTerms: Ls[Term] = this match
    case Alias(nme, pattern) => pattern.subTerms
    case Lit(literal) => Nil
    case Concrete(nme) => Nil
    case Var(nme) => Nil
    case Empty(source) => source :: Nil
    case ClassLike(_, t, parameters, _) => t :: Nil
    case Tuple(fields) => fields.flatMap(_.subTerms)
    case Record(entries) => entries.flatMap(_._2.subTerms)
  
  def children: Ls[Located] = this match
    case Alias(nme, pattern) => nme :: pattern :: Nil
    case Lit(literal) => Nil
    case Concrete(nme) => Nil
    case Var(nme) => Nil
    case Empty(source) => source :: Nil
    case ClassLike(_, t, parameters, _) => t :: parameters.toList.flatten
    case Tuple(fields) => fields
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
  
  def showDbg: Str = this match
    case Alias(nme, pattern) => s"($nme as $pattern)"
    case Lit(literal) => literal.idStr
    case Concrete(nme) => s"`${nme.name}`"
    case Var(nme) => nme.toString
    case Empty(_) => "•"
    case ClassLike(sym, t, ps, rfd) => (if rfd then "refined " else "") + (ps match {
      case N => sym.nme
      case S(parameters) => parameters.mkString(s"${sym.nme}(", ", ", ")")
    })
    case Tuple(fields) => fields.mkString("(", ", ", ")")
    case Record(Nil) => "{}"
    case Record(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
      

