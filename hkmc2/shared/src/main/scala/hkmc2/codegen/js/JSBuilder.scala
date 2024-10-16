package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*

import Scope.scope


// TODO factor some logic for other codegen backends
abstract class CodeBuilder:
    
  type Context
  

class JSBuilder extends CodeBuilder:
  
  val builtinOps: Set[Str] =
    Set("+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||")

  // TODO use this to avoid parens when we generate recomposed expressions later
  enum Context:
    case TopLevel
    case SelectionPrefix
    case Argument
    case Operand(prec: Int)
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.Ref(m: semantics.MemberSymbol[?]) =>
      m.nme // TODO qualify if necessary? (maybe never needed)
    case Value.Ref(l: semantics.BlockLocalSymbol) =>
      summon[Scope].lookup_!(l)
    case Value.Lit(lit) =>
      lit.idStr
    case Call(Value.Ref(l: semantics.MemberSymbol[?]), lhs :: rhs :: Nil) if builtinOps contains l.nme =>
      doc"${result(lhs)} ${l.nme} ${result(rhs)}"
    case Call(fun, args) =>
      doc"${result(fun)}(${args.map(result).mkDocument(", ")})"
    case Value.Lam(ps, bod) => scope.nest givenIn:
      val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
      doc"($vars) => { #{  # ${
        body(bod)
      } #}  # }"
    case Select(qual, name) =>
      doc"${result(qual)}.${name.name}"
  def returningTerm(t: Block)(using Raise, Scope): Document = t match
    case Assign(l, r, rst) =>
      doc" # ${scope.lookup_!(l)} = ${result(r)};${returningTerm(rst)}"
    case Define(defn, rst) => scope.nest givenIn:
      val defnJS = defn match
      case TermDefn(syntax.Fun, sym, N, body) =>
        TODO("getters")
      case TermDefn(syntax.Fun, sym, S(ps), bod) =>
        val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
        doc"function ${sym.nme}($vars) { #{  # ${body(bod)} #}  # }"
      doc" # ${defnJS};${returningTerm(rst)}"
    case Return(res) =>
      doc" # return ${result(res)}"
    case Match(scrut, Case.Lit(syntax.Tree.BoolLit(true)) -> trm :: Nil, els, rest) =>
      val t = doc" # if (${ result(scrut) }) { #{ ${
          returningTerm(trm)
        } #}  # }"
      val e = els match
      case S(el) =>
        doc" else { #{ ${ returningTerm(el) } #}  # }"
      case N  => doc""
      t :: e :: returningTerm(rest)
    case End("") => doc""
    case End(msg) =>
      doc" # /* $msg */"
    // case _ => ???
  
  def body(t: Block)(using Raise, Scope): Document = scope.nest givenIn:
    val prelude = if t.definedVars.isEmpty then doc"" else
      val vars = t.definedVars.toSeq.sortBy(_.uid).iterator.map(l =>
        l -> scope.allocateName(l))
      doc"let " ::  vars.map: (_, nme) =>
        nme
      .toList.mkDocument(", ")
      :: doc";"
    prelude :: returningTerm(t)
  
