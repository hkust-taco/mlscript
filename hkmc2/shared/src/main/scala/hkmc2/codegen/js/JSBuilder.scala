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
import hkmc2.semantics.InnerSymbol
import hkmc2.semantics.ParamList
import hkmc2.codegen.Value.Lam
import hkmc2.semantics.BlockMemberSymbol
import hkmc2.semantics.BuiltinSymbol
import hkmc2.Message.MessageContext


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
  
  def err(errMsg: Message)(using Raise, Scope): Document =
    raise(ErrorReport(errMsg -> N :: Nil,
      source = Diagnostic.Source.Compilation))
    doc"(()=>{throw globalThis.Error(${result(Value.Lit(syntax.Tree.StrLit(errMsg.show)))})})()"
  
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
    case ts: semantics.BlockMemberSymbol => // this means it's a locally-defined member
      ts.nme
      // ts.trmTree
    case ts: semantics.InnerSymbol =>
      summon[Scope].findThis_!(ts)
    case _ => summon[Scope].lookup_!(l)
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => summon[Scope].findThis_!(sym)
    case Value.Lit(Tree.StrLit(value)) => JSBuilder.makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Value.Ref(l: BuiltinSymbol) =>
      if l.nullary then l.nme
      else err(msg"Illegal reference to builtin symbol '${l.nme}'")
    case Value.Ref(l) => getVar(l)
    
    case Call(Value.Ref(l: BuiltinSymbol), lhs :: rhs :: Nil) =>
      if l.binary then
        val res = doc"${result(lhs)} ${l.nme} ${result(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else err(msg"Cannot call non-binary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), rhs :: Nil) =>
      if l.unary then
        val res = doc"${l.nme} ${result(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else err(msg"Cannot call non-unary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), args) =>
      err(msg"Illeal arity for builtin symbol '${l.nme}'")
    
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
    case AssignField(p, n, r, rst) =>
      doc" # ${result(p)}.${n.name} = ${result(r)};${returningTerm(rst)}"
    case Define(defn, rst) =>
      def mkThis(sym: InnerSymbol): Document =
        result(Value.This(sym))
      // println(defn.sym)
      val resJS = defn match
      // case FunDefn(k: syntax.Val, sym, pss, bod) =>
      case ValDefn(own, k: syntax.Val, sym, p) =>
        // scope.nest.givenIn:
        val sym = defn.sym
        // assert(pss.isEmpty)
        // val result = returningTerm(bod)
        // doc"const ${sym.nme} = ${result}"
        own match
        case N =>
          doc"const ${sym.nme} = ${result(p)};${returningTerm(rst)}"
        case S(owner) =>
          // doc"const ${sym.nme} = ${result(p)}; # ${mkThis(owner)}.${sym.nme} = ${sym.nme}"
          doc"${mkThis(owner)}.${sym.nme} = ${result(p)};${returningTerm(rst)}"
      case _ =>
        val (thisProxy, res) = scope.nestRebindThis(
            // * Either this is an InnerSymbol or this is a Fun,
            // * and we need to rebind `this` to None to shadow it.
            S(defn.sym).collectFirst{ case s: InnerSymbol => s }):
          defn match
          case FunDefn(sym, Nil, body) =>
            TODO("getters")
          case FunDefn(sym, ParamList(_, ps) :: pss, bod) =>
            val paramList = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
            val result = pss.foldRight(bod):
              case (ParamList(_, ps), block) => 
                Return(Lam(ps, block), false)
            doc"function ${sym.nme}(${paramList}) { #{  # ${body(result)} #}  # }"
          case ClsLikeDefn(sym, syntax.Cls, mtds, flds, ctor) =>
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
                  case td @ FunDefn(_, ParamList(_, ps) :: pss, bod) =>
                    val vars = ps.map(p => scope.allocateName(p.sym)).mkDocument(", ")
                    val result = pss.foldRight(bod):
                      case (ParamList(_, ps), block) => 
                        Return(Lam(ps, block), false)
                    doc" # ${td.sym.nme}($vars) { #{  # ${
                      body(result)
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
            if clsDefn.kind is syntax.Mod then
              val clsTmp = summon[Scope].allocateName(new semantics.TempSymbol(0/*TODO rm this useless param*/, N, sym.nme+"$"+"class"))
              clsDefn.owner match
              case S(owner) =>
                assert(clsDefn.paramsOpt.isEmpty)
                // doc"${mkThis(owner)}.${sym.nme} = new ${clsJS}"
                doc"const $clsTmp = ${clsJS}; # ${mkThis(owner)}.${sym.nme} = new ${clsTmp
                  }; # ${mkThis(owner)}.${sym.nme}.class = $clsTmp;"
              case N => doc"const $clsTmp = ${clsJS}; const ${sym.nme} = new ${clsTmp
                  }; # ${sym.nme}.class = $clsTmp;"
            else
              val fun = clsDefn.paramsOpt match
                case S(params) =>
                  val args = params.map(p => scope.allocateName(p.sym)).mkDocument(", ")
                  S(doc"function ${sym.nme}($args) { return new ${sym.nme}.class($args); }")
                case N => N
              clsDefn.owner match
              case S(owner) =>
                val ths = mkThis(owner)
                fun match
                case S(f) =>
                  doc"${ths}.${sym.nme} = ${f}; # ${ths}.${sym.nme}.class = ${clsJS};"
                case N =>
                  doc"${ths}.${sym.nme} = ${clsJS};"
              case N =>
                fun match
                case S(f) => doc"${f}; # ${sym.nme}.class = ${clsJS};"
                case N => clsJS
        thisProxy match
          case S(proxy) => doc" # const $proxy = this; # ${res.stripBreaks}${returningTerm(rst)}"
          case N => doc"$res${returningTerm(rst)}"
      doc" # ${resJS}"
    case Return(res, true) => doc" # ${result(res)}"
    case Return(res, false) => doc" # return ${result(res)};"
    
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
    case Match(scrut, Case.Cls(cls, pth) -> trm :: Nil, els, rest) =>
      val test = cls.defn.getOrElse(die).kind match
        // case syntax.Mod => doc"=== ${result(pth)}"
        case _ => doc"instanceof ${result(pth)}"
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
      doc" # throw ${result(res)};"
    
    case Break(lbl, false) =>
      doc" # break ${getVar(lbl)};"
    
    case Break(lbl, true) =>
      doc" # continue ${getVar(lbl)};"
    
    case Label(lbl, bod, rst) =>
      scope.allocateName(lbl)
      doc" # ${getVar(lbl)}: while (true) { #{ ${
        returningTerm(bod)
      } # break; #}  # }${returningTerm(rst)}"
      
    case TryBlock(sub, fin, rst) =>
      doc" # try { #{ ${returningTerm(sub)
        } #}  # } finally { #{ ${returningTerm(fin)} #}  # } # ${
        returningTerm(rst).stripBreaks}"
    
    // case _ => ???
  
  def program(p: Program, exprt: Opt[Str], wd: os.Path)(using Raise, Scope): Document =
    val compilingFile: Bool = exprt.isDefined // * If there's an export, it means we're not in the worksheet
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    val imps = p.imports.map: i =>
      if compilingFile
      then
        val relPath = os.Path(i._2.toString).relativeTo(wd).toString
        doc"""import "./${relPath}";"""
      else
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


