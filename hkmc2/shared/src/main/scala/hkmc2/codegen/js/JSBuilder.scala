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
  

class JSBuilder(using Elaborator.State, Elaborator.Ctx) extends CodeBuilder:
  
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
  
  def argument(a: Arg)(using Raise, Scope): Document =
    if a.spread then doc"...${result(a.value)}" else result(a.value)
  
  def operand(a: Arg)(using Raise, Scope): Document =
    if a.spread then die else subexpression(a.value)
  
  def subexpression(r: Result)(using Raise, Scope): Document = r match
    case _: Value.Lam => doc"(${result(r)})"
    case _ => result(r)
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => summon[Scope].findThis_!(sym)
    case Value.Lit(Tree.StrLit(value)) => JSBuilder.makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Value.Ref(l: BuiltinSymbol) =>
      if l.nullary then l.nme
      else err(msg"Illegal reference to builtin symbol '${l.nme}'")
    case Value.Ref(l) => getVar(l)
    
    case Call(Value.Ref(l: BuiltinSymbol), lhs :: rhs :: Nil) if !l.functionLike =>
      if l.binary then
        val res = doc"${operand(lhs)} ${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else err(msg"Cannot call non-binary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), rhs :: Nil) if !l.functionLike =>
      if l.unary then
        val res = doc"${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else err(msg"Cannot call non-unary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), args) =>
      if l.functionLike then
        val argsDoc = args.map(argument).mkDocument(", ")
        doc"${l.nme}(${argsDoc})"
      else err(msg"Illegal arity for builtin symbol '${l.nme}'")
    
    case Call(s @ Select(_, id), lhs :: rhs :: Nil) =>
      Elaborator.ctx.Builtins.getBuiltinOp(id.name) match
        case S(jsOp) =>
          val res = doc"${operand(lhs)} ${jsOp} ${operand(rhs)}"
          if needsParens(jsOp) then doc"(${res})" else res
        case N => doc"${result(s)}(${(argument(lhs) :: argument(rhs) :: Nil).mkDocument(", ")})"
    case c @ Call(fun, args) =>
      val base = subexpression(fun)
      val argsDoc = args.map(argument).mkDocument(", ")
      if c.isMlsFun then doc"${base}(${argsDoc})" else doc"${base}(${argsDoc}) ?? null"
    case Value.Lam(ps, bod) => scope.nest givenIn:
      val (params, bodyDoc) = setupFunction(none, ps, bod)
      doc"($params) => ${ braced(bodyDoc) }"
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
    case Value.Arr(es) if es.isEmpty => doc"[]"
    case Value.Arr(es) =>
      doc"[ #{  # ${es.map(argument).mkDocument(doc", # ")} #}  # ]"
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
            // doc"function ${sym.nme}() ${ braced(this.body(body)) }"
            lastWords("cannot generate function with no parameter list")
          case FunDefn(sym, ps :: pss, bod) =>
            val result = pss.foldRight(bod):
              case (ps, block) => 
                Return(Lam(ps, block), false)
            val (params, bodyDoc) = setupFunction(some(sym.nme), ps, result)
            doc"function ${sym.nme}($params) ${ braced(bodyDoc) }"
          case ClsLikeDefn(sym, syntax.Cls, parentSym, mtds, privFlds, _pubFlds, preCtor, ctor) =>
            // * Note: `_pubFlds` is not used because in JS, fields are not declared
            val clsDefn = sym.defn.getOrElse(die)
            val clsParams = clsDefn.paramsOpt.fold(Nil)(_.paramSyms)
            val ctorParams = clsParams.map(p => p -> scope.allocateName(p))
            val preCtorCode = ctorParams.foldLeft(body(preCtor)):
              case (acc, (sym, nme)) =>
                doc"$acc # this.${sym.name} = $nme;"
            val ctorCode = doc"$preCtorCode${body(ctor)}"
            val clsJS = doc"class ${sym.nme}${parentSym.map(p => s" extends ${result(p)}").getOrElse("")} { #{ ${
                privFlds.map(f => doc" # #${f.nme};").mkDocument(doc"")
              } # constructor(${
                ctorParams.unzip._2.mkDocument(", ")
              }) ${ braced(ctorCode) }${
                mtds.map: 
                  case td @ FunDefn(_, ps :: pss, bod) =>
                    val result = pss.foldRight(bod):
                      case (ps, block) => 
                        Return(Lam(ps, block), false)
                    val (params, bodyDoc) = setupFunction(some(td.sym.nme), ps, result)
                    doc" # ${td.sym.nme}($params) ${ braced(bodyDoc) }"
                  case td @ FunDefn(_, Nil, bod) =>
                    doc" # get ${td.sym.nme}() ${ braced(body(bod)) }"
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
            if (clsDefn.kind is syntax.Mod) || (clsDefn.kind is syntax.Obj) || (clsDefn.kind is syntax.Pat) then
              val clsTmp = summon[Scope].allocateName(new semantics.TempSymbol(N, sym.nme+"$"+"class"))
              clsDefn.owner match
              case S(owner) =>
                assert((clsDefn.kind is syntax.Pat) || clsDefn.paramsOpt.isEmpty)
                // doc"${mkThis(owner)}.${sym.nme} = new ${clsJS}"
                doc"const $clsTmp = ${clsJS}; # ${mkThis(owner)}.${sym.nme} = new ${clsTmp
                  }; # ${mkThis(owner)}.${sym.nme}.class = $clsTmp;"
              case N => doc"const $clsTmp = ${clsJS}; const ${sym.nme} = new ${clsTmp
                  }; # ${sym.nme}.class = $clsTmp;"
            else
              val fun = clsDefn.paramsOpt match
                case S(params) =>
                  val (ps, bod) = setupFunction(some(sym.nme), params, End())
                  S(doc"function ${sym.nme}($ps) { return new ${sym.nme}.class($ps); }")
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
                case S(f) => doc"${f} # ${sym.nme}.class = ${clsJS};"
                case N => clsJS
        thisProxy match
          case S(proxy) if !scope.thisProxyDefined =>
            scope.thisProxyDefined = true
            doc"const $proxy = this; # $res${returningTerm(rst)}"
          case _ => doc"$res${returningTerm(rst)}"
      doc" # $resJS"
    case Return(res, true) => doc" # ${result(res)}"
    case Return(res, false) => doc" # return ${result(res)};"
    
    case Match(scrut, Nil, els, rest) =>
      val e = els match
      case S(el) => returningTerm(el)
      case N => doc""
      e :: returningTerm(rest)
    case Match(scrut, hd :: tl, els, rest) =>
      val sd = result(scrut)
      def cond(cse: Case) = cse match
        case Case.Lit(lit) => doc"$sd === ${lit.idStr}"
        case Case.Cls(cls, pth) => cls match
          // case _: semantics.ModuleSymbol => doc"=== ${result(pth)}"
          case Elaborator.ctx.Builtins.Str => doc"typeof $sd === 'string'"
          case Elaborator.ctx.Builtins.Num => doc"typeof $sd === 'number'"
          case Elaborator.ctx.Builtins.Int => doc"globalThis.Number.isInteger($sd)"
          case _ => doc"$sd instanceof ${result(pth)}"
        case Case.Tup(len, inf) => doc"globalThis.Array.isArray($sd) && $sd.length ${if inf then ">=" else "==="} ${len}"
      val h = doc" # if (${ cond(hd._1) }) ${ braced(returningTerm(hd._2)) }"
      val t = tl.foldLeft(h)((acc, arm) => acc :: doc" else if (${ cond(arm._1) }) ${ braced(returningTerm(arm._2)) }")
      val e = els match
      case S(el) =>
        doc" else ${ braced(returningTerm(el)) }"
      case N  => doc""
      t :: e :: returningTerm(rest)
    
    case Begin(sub, thn) =>
      doc"${returningTerm(sub)}${returningTerm(thn)}"
      
    case End("") => doc""
    case End(msg) =>
      doc" # /* $msg */"
    
    case Throw(res) =>
      doc" # throw ${result(res)};"
    
    case Break(lbl) =>
      doc" # break ${getVar(lbl)};"
    
    case Continue(lbl) =>
      doc" # continue ${getVar(lbl)};"
    
    case Label(lbl, bod, rst) =>
      scope.allocateName(lbl)
      doc" # ${getVar(lbl)}: while (true) { #{ ${
        returningTerm(bod)
      } # break; #}  # }${returningTerm(rst)}"
      
    case TryBlock(sub, fin, rst) =>
      doc" # try ${ braced(returningTerm(sub)) } finally ${ braced(returningTerm(fin)) } # ${
        returningTerm(rst).stripBreaks}"
    
    // case _ => ???
  
  def program(p: Program, exprt: Opt[Str], wd: os.Path)(using Raise, Scope): Document =
    val compilingFile: Bool = exprt.isDefined // * If there's an export, it means we're not in the worksheet
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    val imps = p.imports.map: i =>
      if compilingFile
      then
        val path = i._2
        val relPath = if path.startsWith("/")
          then "./" + os.Path(path).relativeTo(wd).toString
          else path
        doc"""import ${getVar(i._1)} from "${relPath}";"""
      else
        val v = doc"this.${getVar(i._1)}"
        doc"""$v = await import("${i._2.toString
          }"); # if ($v.default !== undefined) $v = $v.default;"""
    imps.mkDocument(doc" # ") :/: block(p.main).stripBreaks :: (
      exprt match
        case S(e) => doc"\nexport default ${e};\n"
        case N => doc""
      )
  
  def block(t: Block)(using Raise, Scope): Document =
    val vars = t.definedVars.toSeq.filter(scope.lookup(_).isEmpty).sortBy(_.uid).iterator.map(l =>
      l -> scope.allocateName(l))
    if vars.isEmpty then returningTerm(t) else
      doc" # let " :: vars.map: (_, nme) =>
        nme
      .toList.mkDocument(", ")
      :: doc";" :: returningTerm(t)
  
  def body(t: Block)(using Raise, Scope): Document = scope.nest givenIn:
    block(t)
  
  def braced(t: Document)(using Raise, Scope): Document =
    if t.isEmpty then
      doc"{}"
    else
      doc"{ #{ ${t} #}  # }"
  
  def setupFunction(name: Option[Str], params: ParamList, body: Block)
      (using Raise, Scope): (Document, Document) =
    val paramsList = params.params.map(p => scope.allocateName(p.sym))
      .++(params.restParam.map(p => "..." + scope.allocateName(p.sym)))
      .mkDocument(", ")
    (paramsList, this.body(body))



object JSBuilder:
  import scala.util.matching.Regex
  
  private val identifierPattern: Regex = "^[A-Za-z_$][A-Za-z0-9_$]*$".r

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
    s"\"${escapeStringCharacters(s)}\""
  
  def escapeStringCharacters(s: Str): Str =
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
    }.mkString
  
end JSBuilder


trait JSBuilderArgNumSanityChecks
    (instrument: Bool)(using Elaborator.State)
    extends JSBuilder:
  
  val functionParamVarargSymbol = semantics.TempSymbol(N, "args")
  
  override def setupFunction(name: Option[Str], params: ParamList, body: Block)(using Raise, Scope): (Document, Document) =
    if instrument then
      val paramsList = params.params.map(p => Scope.scope.allocateName(p.sym))
      val paramRest = params.restParam.map(p => Scope.scope.allocateName(p.sym))
      val paramsStr = Scope.scope.allocateName(functionParamVarargSymbol)
      val functionName = JSBuilder.makeStringLiteral(name.fold("")(n => s"${JSBuilder.escapeStringCharacters(n)}"))
      val checkArgsNum = doc"\nglobalThis.Predef.checkArgs($functionName, ${params.paramCountLB}, ${params.paramCountUB.toString}, $paramsStr.length);"
      val paramsAssign = paramsList.zipWithIndex.map{(nme, i) =>
        doc"\nlet ${nme} = ${paramsStr}[$i];"}.mkDocument("")
      val restAssign = paramRest match
        case N => doc""
        case S(p) => doc"\nlet $p = globalThis.Predef.tupleSlice($paramsStr, ${params.paramCountLB}, 0);"
      (doc"...$paramsStr", doc"$checkArgsNum$paramsAssign$restAssign${this.body(body)}")
    else
      super.setupFunction(name, params, body)

