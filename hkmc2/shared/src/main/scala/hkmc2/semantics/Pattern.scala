package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*, Tree.Ident


enum Pattern extends AutoLocated:
  case Lit(literal: Literal)
  case Var(sym: BlockLocalSymbol)
  case ClassLike(sym: ClassSymbol | ModuleSymbol, trm: Term, parameters: Opt[List[BlockLocalSymbol]], var refined: Bool)(val tree: Tree)
  case Tuple(fields: List[BlockLocalSymbol])
  case Record(entries: List[(Ident -> BlockLocalSymbol)])
  
  def subTerms: Ls[Term] = this match
    case Lit(_) => Nil
    case Var(_) => Nil
    case ClassLike(_, t, _, _) => t :: Nil
    case Tuple(_) => Nil
    case Record(_) => Nil
  
  def children: Ls[Located] = this match
    case Lit(literal) => literal :: Nil
    case Var(nme) => Nil
    case ClassLike(_, t, parameters, _) => t :: parameters.toList.flatten
    case Tuple(fields) => fields
    case Record(entries) => entries.flatMap { case (nme, als) => nme :: als :: Nil }
  
  def showDbg: Str = this match
    case Lit(literal) => literal.idStr
    case Var(sym) => sym.nme
    case ClassLike(sym, t, ps, rfd) => (if rfd then "refined " else "") +
      sym.nme + ps.fold("")(_.mkString("(", ", ", ")"))
    case Tuple(fields) => fields.mkString("[", ", ", "]")
    case Record(Nil) => "{}"
    case Record(entries) =>
      entries.iterator.map(_.name + ": " + _).mkString("{ ", ", ", " }")
      

