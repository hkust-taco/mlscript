package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*

import Scope.scope
import hkmc2.syntax.ImmutVal


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
  
  def getVar(l: Local)(using Raise, Scope): Document = l match
    case ts: semantics.TermSymbol =>
      ts.owner match
      case S(owner) =>
        doc"${result(Value.This(owner))}.${
          if (ts.k is syntax.LetBind) && !owner.isInstanceOf[semantics.TopLevelSymbol]
          then "#" + ts.id.name
          else ts.id.name
        }"
      case N =>
        ts.id.name
    case ts: semantics.ClassSymbol => // TODO dedup
      ts.owner match
      case S(owner) =>
        doc"${result(Value.This(owner))}.${ts.id.name}"
      case N =>
        ts.id.name
    case _ => summon[Scope].lookup_!(l)
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => doc"this" // TODO qualify if necessary
    case Value.Ref(l) => getVar(l)
    case Value.Lit(lit) =>
      lit.idStr
    case Call(Value.Ref(l: semantics.MemberSymbol[?]), lhs :: rhs :: Nil) if builtinOps contains l.nme =>
      doc"${result(lhs)} ${l.nme} ${result(rhs)}"
    case Call(fun, args) =>
      val base = fun match
        case _: Value.Lam => doc"(${result(fun)})"
        case _ => result(fun)
      doc"${base}(${args.map(result).mkDocument(", ")})"
    case Value.Lam(ps, bod) => scope.nest givenIn:
      val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
      doc"($vars) => { #{  # ${
        body(bod)
      } #}  # }"
    case Select(qual, name) =>
      doc"${result(qual)}.${name.name}"
    case Instantiate(sym, as) =>
      doc"new ${sym.nme}(${as.map(result).mkDocument(", ")})"
  def returningTerm(t: Block)(using Raise, Scope): Document = t match
    case Assign(l, r, rst) =>
      doc" # ${getVar(l)} = ${result(r)};${returningTerm(rst)}"
    case Define(defn, rst) => scope.nest givenIn:
      val defnJS = defn match
      case TermDefn(syntax.Fun, sym, N, body) =>
        TODO("getters")
      case TermDefn(syntax.Fun, sym, S(ps), bod) =>
        val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
        doc"function ${sym.nme}($vars) { #{  # ${body(bod)} #}  # }"
      case ClsDefn(sym, syntax.Cls, mtds, flds, ctor) =>
        val clsDefn = sym.defn.getOrElse(die)
        val clsParams = clsDefn.paramsOpt.getOrElse(Nil)
        val ctorParams = clsParams.map(p => p.sym -> scope.allocateName(p.sym))
        val ctorCode = ctorParams.foldRight(body(ctor)):
          case ((sym, nme), acc) =>
            doc" # this.${sym.name} = $nme;${acc}"
        val clsJS = doc"class ${sym.nme} { #{ ${
          flds.map(f => doc" # #${f.nme};").mkDocument(doc"")
        } # constructor(${
          ctorParams.unzip._2.mkDocument(", ")
        }) { #{  # ${
          ctorCode
        } #}  # }${
          mtds.map: td =>
            val vars = td.params.get.map(p => scope.allocateName(p.sym)).mkDocument(", ")
            doc" # ${td.sym.nme}($vars) { #{  # ${
              body(td.body)
            } #}  # }"
          .mkDocument(" ")
        } #}  # }"
        if clsDefn.kind is syntax.Mod then sym.owner match
        case S(owner) =>
          assert(clsDefn.paramsOpt.isEmpty)
          doc"${result(Value.This(owner))}.${sym.nme} = new ${clsJS}"
        case N => doc"const ${sym.nme} = new $clsJS"
        else sym.owner match
        case S(owner) =>
          doc"${result(Value.This(owner))}.${sym.nme} = ${clsJS}"
        case N => clsJS
      doc" # ${defnJS};${returningTerm(rst)}"
    case Return(res, true) => doc" # ${result(res)}"
    case Return(res, false) => doc" # return ${result(res)}"
    
    // TODO factor out common logic
    case Match(scrut, Case.Lit(syntax.Tree.BoolLit(true)) -> trm :: Nil, els, rest) =>
      val t = doc" # if (${ result(scrut) }) { #{ ${
          returningTerm(trm)
        } #}  # }"
      val e = els match
      case S(el) =>
        doc" else { #{ ${ returningTerm(el) } #}  # }"
      case N  => doc""
      t :: e :: returningTerm(rest)
    case Match(scrut, Case.Cls(cls) -> trm :: Nil, els, rest) =>
      val test = cls.defn.getOrElse(die).kind match
        case syntax.Mod => doc"=== ${getVar(cls)}"
        case _ => doc"instanceof ${getVar(cls)}"
      val t = doc" # if (${ result(scrut) } $test) { #{ ${
          returningTerm(trm)
        } #}  # }"
      val e = els match
      case S(el) =>
        doc" else { #{ ${ returningTerm(el) } #}  # }"
      case N  => doc""
      t :: e :: returningTerm(rest)
    case Match(scrut, Case.Lit(lit) -> trm :: Nil, els, rest) =>
      val t = doc" # if (${ result(scrut) } === ${lit.idStr}) { #{ ${
          returningTerm(trm)
        } #}  # }"
      val e = els match
      case S(el) =>
        doc" else { #{ ${ returningTerm(el) } #}  # }"
      case N  => doc""
      t :: e :: returningTerm(rest)
    
    case Begin(sub, thn) =>
      doc"${returningTerm(sub)}${returningTerm(thn)}"
      
    case End("") => doc""
    case End(msg) =>
      doc" # /* $msg */"
    // case _ => ???
  
  def block(t: Block)(using Raise, Scope): Document =
    if t.definedVars.isEmpty then returningTerm(t).stripBreaks else
      val vars = t.definedVars.toSeq.sortBy(_.uid).iterator.map(l =>
        l -> scope.allocateName(l))
      doc"let " :: vars.map: (_, nme) =>
        nme
      .toList.mkDocument(", ")
      :: doc";" :: returningTerm(t)
  
  def body(t: Block)(using Raise, Scope): Document = scope.nest givenIn:
    block(t)
  
