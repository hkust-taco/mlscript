package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*

import Scope.scope
import hkmc2.syntax.ImmutVal
import hkmc2.semantics.Elaborator
import hkmc2.syntax.Tree
import hkmc2.semantics.TopLevelSymbol
import hkmc2.semantics.MemberSymbol
import hkmc2.semantics.ParamList
import hkmc2.codegen.Value.Lam


// TODO factor some logic for other codegen backends
abstract class CodeBuilder:
    
  type Context
  

class JSBuilder extends CodeBuilder:
  
  val builtinOpsBase: Ls[Str] = Ls(
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "===",
    "&&", "||")
  val builtinOpsMap: Map[Str, Str] = (
    builtinOpsBase.map(op => op -> op).toMap
    + (";" -> ",")
  )
  val needsParens: Set[Str] = Set(",")
  
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
    case Value.This(sym) => summon[Scope].findThis_!(sym)
    case Value.Ref(l) => getVar(l)
    case Value.Lit(Tree.StrLit(value)) => JSBuilder.makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Call(Value.Ref(l: semantics.MemberSymbol[?]), lhs :: rhs :: Nil) if builtinOpsMap contains l.nme =>
      val op = builtinOpsMap(l.nme)
      val res = doc"${result(lhs)} ${op} ${result(rhs)}"
      if needsParens(op) then doc"(${res})" else res
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
    case Select(qual, id) =>
      val name = id.name
      doc"${result(qual)}${
        if JSBuilder.isValidFieldName(name)
        then doc".$name"
        else name.toIntOption match
          case S(index) => s"[$index]"
          case N => s"[${JSBuilder.makeStringLiteral(name)}]"
      }"
    case Instantiate(cls, as) =>
      doc"new ${result(cls)}(${as.map(result).mkDocument(", ")})"
    case Value.Arr(es) =>
      doc"[ #{  # ${es.map(result).mkDocument(doc", # ")} #}  # ]"
  def returningTerm(t: Block)(using Raise, Scope): Document = t match
    case Assign(l, r, rst) =>
      doc" # ${getVar(l)} = ${result(r)};${returningTerm(rst)}"
    case Define(defn, rst) =>
      def mkThis(sym: MemberSymbol[?]): Document =
        result(Value.This(sym))
      val (thisProxy, res) = scope.nestRebindThis(defn.sym):
        val defnJS = defn match
        case TermDefn(syntax.Fun, sym, Nil, body) =>
          TODO("getters")
        case TermDefn(syntax.Fun, sym, ParamList(_, ps) :: pss, bod) =>
          val paramList = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
          val result = pss.foldRight(bod):
            case (ParamList(_, ps), block) => 
              Return(Lam(ps, block), false)
          doc"function ${sym.nme}(${paramList}) { #{  # ${body(result)} #}  # }"
        case ClsDefn(sym, syntax.Cls, mtds, flds, ctor) =>
          val clsDefn = sym.defn.getOrElse(die)
          val clsParams = clsDefn.paramsOpt.getOrElse(Nil)
          val ctorParams = clsParams.map(p => p.sym -> scope.allocateName(p.sym))
          val ctorCode = ctorParams.foldRight(body(ctor)):
            case ((sym, nme), acc) =>
              doc"this.${sym.name} = $nme; # ${acc}"
          val clsJS = doc"class ${sym.nme} { #{ ${
            flds.map(f => doc" # #${f.nme};").mkDocument(doc"")
          } # constructor(${
            ctorParams.unzip._2.mkDocument(", ")
          }) { #{  # ${
            ctorCode.stripBreaks
          } #}  # }${
            mtds.map: 
              case td @ TermDefn(_, _, ParamList(_, ps) :: Nil, _) =>
                val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
                doc" # ${td.sym.nme}($vars) { #{  # ${
                  body(td.body)
                } #}  # }"
            .mkDocument(" ")
          }${
            if mtds.exists(_.sym.nme == "toString")
            then doc""
            else doc""" # toString() { return "${sym.nme}${
              if clsDefn.paramsOpt.isEmpty then doc"""""""
              else doc"""(" + ${
                  ctorParams.headOption.fold("")("this." + _._2)
                }${
                  ctorParams.tailOption.fold("")(_.map(
                    """ + ", " + this.""" + _._2).mkString)
                } + ")""""
            }; }"""
          } #}  # }"
          if clsDefn.kind is syntax.Mod then sym.owner match
          case S(owner) =>
            assert(clsDefn.paramsOpt.isEmpty)
            doc"${mkThis(owner)}.${sym.nme} = new ${clsJS}"
          case N => doc"const ${sym.nme} = new $clsJS"
          else sym.owner match
          case S(owner) =>
            doc"${mkThis(owner)}.${sym.nme} = ${clsJS}"
          case N => clsJS
        doc" # ${defnJS}"
      thisProxy match
        case S(proxy) => doc" # const $proxy = this; # ${res.stripBreaks};${returningTerm(rst)}"
        case N => doc"$res;${returningTerm(rst)}"
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
      doc"${returningTerm(sub)} # ${returningTerm(thn).stripBreaks}"
      
    case End("") => doc""
    case End(msg) =>
      doc" # /* $msg */"
    
    case Throw(res) =>
      doc" # throw ${result(res)}"
      
    case TryBlock(sub, fin, rst) =>
      doc" # try { #{ ${returningTerm(sub)
        } #}  # } finally { #{ ${returningTerm(fin)} #}  # } # ${
        returningTerm(rst).stripBreaks}"
    
    // case _ => ???
  
  def program(p: Program, exprt: Opt[Str])(using Raise, Scope): Document =
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    val imps = p.imports.map: i =>
      val v = doc"this.${getVar(i._1)}"
      doc"""$v = await import("${i._2.toString
        }"); # if ($v.default !== undefined) $v = $v.default;"""
    imps.mkDocument(doc" # ") :/: block(p.main) :: (
      exprt match
        case S(e) => doc"\nexport default ${e};\n"
        case N => doc""
      )
  
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
  
  
object JSBuilder:
  import scala.util.matching.Regex
  
  private val identifierPattern: Regex = "^[A-Za-z$][A-Za-z0-9$]*$".r

  def isValidIdentifier(s: Str): Bool = identifierPattern.matches(s) && !keywords.contains(s)
  
  // in this case, a keyword can be used as a field name
  // e.g. `something.class` is valid
  def isValidFieldName(s: Str): Bool = identifierPattern.matches(s)
  
  val keywords: Set[Str] = Set(
    // Reserved keywords as of ECMAScript 2015
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "export",
    "extends",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    // The following are reserved as future keywords by the ECMAScript specification.
    // They have no special functionality at present, but they might at some future time,
    // so they cannot be used as identifiers. These are always reserved:
    "enum",
    // The following are only reserved when they are found in strict mode code:
    "abstract",
    "boolean",
    "byte",
    "char",
    "double",
    "final",
    "float",
    "goto",
    "int",
    "long",
    "native",
    "short",
    "synchronized",
    "throws",
    "transient",
    "volatile",
  )
  
  def makeStringLiteral(s: Str): Str =
    s.map[Str] {
      case '"'  => "\\\""
      case '\\' => "\\\\"
      case '\b' => "\\b"
      case '\f' => "\\f"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case c =>
        if 0 < c && c <= 255 && !c.isControl
        then c.toString
        else f"\\u${c.toInt}%04X"
    }.mkString("\"", "", "\"")
  
end JSBuilder


