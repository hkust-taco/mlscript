package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*
import Tree.*
import hkmc2.Message.MessageContext


object Elaborator:
  case class Ctx(parent: Opt[Scope], members: Map[Str, Symbol], locals: Map[Str, VarSymbol])
  object Ctx:
    val empty: Ctx = Ctx(N, Map.empty, Map.empty)
  type Ctxl[A] = Ctx ?=> A
  def ctx: Ctxl[Ctx] = summon
import Elaborator.*

class Elaborator(raise: Raise):
  
  def term(tree: Tree): Ctxl[Term] = tree match
    case Block(s :: Nil) =>
      term(s)
    case Block(sts) =>
      block(sts)._1
    case lit: Literal =>
      Term.Lit(lit)
    case Let(lhs, rhs, bodo) =>
      val (pat, syms) = pattern(lhs)
      val r = term(rhs)
      val b = bodo.map(term(_)(using ctx.copy(locals = ctx.locals ++ syms))).getOrElse(unit)
      Term.Blk(List(LetBinding(pat, r)), b)
    case Ident(name) =>
      ctx.locals.get(name) match
        case S(sym) => Term.Var(sym)
        case N =>
          raise(ErrorReport(msg"Unbound variable: $name" -> tree.toLoc :: Nil))
          Term.Error
    case App(lhs, rhs) =>
      Term.App(term(lhs), term(rhs))
    case Tup(fields) =>
      Term.Tup(fields.map(f => Fld(FldFlags.empty, term(f))))
    case Empty() =>
      raise(ErrorReport(msg"A term was expected in this position, but no term was found." -> tree.toLoc :: Nil))
      Term.Error
    case Error() =>
      Term.Error
    // case _ =>
    //   ???
    
    def unit: Term.Lit = Term.Lit(UnitLit(true))
    
    def block(sts: Ls[Tree]): Ctxl[(Term, Ctx)] =
      def go(sts: Ls[Tree], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] = sts match
        case Nil =>
          val res = unit
          (Term.Blk(acc.reverse, res), ctx)
        case Let(lhs, rhs, N) :: sts =>
          val (pat, syms) = pattern(lhs)
          val rhsTerm = term(rhs)
          go(sts, LetBinding(pat, rhsTerm) :: acc)(using ctx.copy(locals = ctx.locals ++ syms))
        case Val(body) :: sts =>
          ???
        case TypeDecl(head, extension, body) :: sts =>
          ???
        case (result: Tree) :: Nil =>
          val res = term(result)
          (Term.Blk(acc.reverse, res), ctx)
      sts match
        case s :: Nil => (term(s), ctx)
        case _ => go(sts, Nil)
    
    def pattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol])] =
      val boundVars = mutable.HashMap.empty[Str, VarSymbol]
      def go(t: Tree): Pattern = t match
        case Ident(name) =>
          val sym = boundVars.getOrElseUpdate(name, VarSymbol(name, nextUid))
          Pattern.Var(sym)
        case Tup(fields) =>
          // val pats = fields.map(pattern)
          // Pattern.Tup(pats)
          ???
        case _ =>
          ???
      (go(t), boundVars.toList)
  
  private var curUi = 0
  def nextUid: Int = { curUi += 1; curUi }
  
end Elaborator

