package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Pattern extends AutoLocated:
  case Lit(literal: Literal)
  case Var(nme: BlockLocalSymbol)
  case ClassLike(sym: ClassSymbol | ModuleSymbol, trm: Term, parameters: Opt[List[BlockLocalSymbol]], var refined: Bool)(val tree: Tree)
  case Tuple(fields: List[Pattern])
  case Record(entries: List[(VarSymbol -> Pattern)])
  
  def subTerms: Ls[Term] = this match
    case Lit(literal) => Nil
    case Var(nme) => Nil
    case ClassLike(_, t, parameters, _) => t :: Nil
    case Tuple(fields) => fields.flatMap(_.subTerms)
    case Record(entries) => entries.flatMap(_._2.subTerms)
  
  def children: Ls[Located] = this match
    case Lit(literal) => Nil
    case Var(nme) => Nil
    case ClassLike(_, t, parameters, _) => t :: parameters.toList.flatten
    case Tuple(fields) => fields
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
  
  def showDbg: Str = this match
    case Lit(literal) => literal.idStr
    case Var(nme) => nme.toString
    case ClassLike(sym, t, ps, rfd) => (if rfd then "refined " else "") + (ps match {
      case N => sym.nme
      case S(parameters) => parameters.mkString(s"${sym.nme}(", ", ", ")")
    })
    case Tuple(fields) => fields.mkString("(", ", ", ")")
    case Record(Nil) => "{}"
    case Record(entries) => entries.iterator.map { case (nme, als) => s"$nme: $als" }.mkString("{ ", ", ", " }")
      

