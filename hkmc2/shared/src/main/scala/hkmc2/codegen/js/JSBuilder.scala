package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*

import hkmc2.Message.MessageContext
import hkmc2.syntax.{Tree, ImmutVal}
import hkmc2.semantics.*
import Elaborator.{State, Ctx}
import hkmc2.codegen.Value.Lam

import Scope.scope
import hkmc2.syntax.Tree.UnitLit


// TODO factor some logic for other codegen backends
abstract class CodeBuilder:
    
  type Context
  

class JSBuilder(using TL, State, Ctx) extends CodeBuilder:
  import JSBuilder.*
  
  def checkMLsCalls: Bool = false
  def checkSelections: Bool = false
  
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
  
  def mkErr(errMsg: Message)(using Raise, Scope): Document =
    doc"throw globalThis.Error(${result(Value.Lit(syntax.Tree.StrLit(errMsg.show)))})"
  
  def errExpr(errMsg: Message)(using Raise, Scope): Document =
    raise(ErrorReport(errMsg -> N :: Nil,
      source = Diagnostic.Source.Compilation))
    doc"(()=>{${mkErr(errMsg)}})()"
  
  def errStmt(errMsg: Message)(using Raise, Scope): Document =
    raise(ErrorReport(errMsg -> N :: Nil,
      source = Diagnostic.Source.Compilation))
    doc" # ${mkErr(errMsg)};"
  
  def getVar(l: Local)(using Raise, Scope): Document = l match
    case ts: semantics.TermSymbol =>
      ts.owner match
      case S(owner) =>
        doc"${getVar(owner)}${
          if (ts.k is syntax.LetBind) && !owner.isInstanceOf[semantics.TopLevelSymbol]
          then ".#" + owner.privatesScope.lookup_!(ts)
          else fieldSelect(ts.id.name)
        }"
      case N => summon[Scope].lookup_!(ts)
    case ts: semantics.InnerSymbol =>
      if ts.asMod.isDefined
      then
        // * Module self-references use the module name itself instead of `this`
        summon[Scope].lookup_!(ts)
      else summon[Scope].findThis_!(ts)
    case _ => summon[Scope].lookup_!(l)
  
  def runtimeVar(using Raise, Scope): Document = getVar(State.runtimeSymbol)
  
  def argument(a: Arg)(using Raise, Scope): Document =
    if a.spread then doc"...${result(a.value)}" else result(a.value)
  
  def operand(a: Arg)(using Raise, Scope): Document =
    if a.spread then die else subexpression(a.value)
  
  def subexpression(r: Result)(using Raise, Scope): Document = r match
    case _: Value.Lam => doc"(${result(r)})"
    case _ => result(r)
  
  def fieldSelect(s: Str): Document =
    if JSBuilder.isValidFieldName(s) then doc".$s"
    else s.toIntOption match
      case S(index) => s"[$index]"
      case N => s"[${JSBuilder.makeStringLiteral(s)}]"
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => summon[Scope].findThis_!(sym)
    case Value.Lit(Tree.StrLit(value)) => makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Value.Ref(l: BuiltinSymbol) =>
      if l.nullary then l.nme
      else errExpr(msg"Illegal reference to builtin symbol '${l.nme}'")
    case Value.Ref(l) => getVar(l)
    
    case Call(Value.Ref(l: BuiltinSymbol), lhs :: rhs :: Nil) if !l.functionLike =>
      if l.binary then
        val res = doc"${operand(lhs)} ${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else errExpr(msg"Cannot call non-binary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), rhs :: Nil) if !l.functionLike =>
      if l.unary then
        val res = doc"${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else errExpr(msg"Cannot call non-unary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol), args) =>
      if l.functionLike then
        val argsDoc = args.map(argument).mkDocument(", ")
        doc"${l.nme}(${argsDoc})"
      else errExpr(msg"Illegal arity for builtin symbol '${l.nme}'")
    
    case Call(s @ Select(_, id), lhs :: rhs :: Nil) =>
      Elaborator.ctx.builtins.getBuiltinOp(id.name) match
        case S(jsOp) =>
          val res = doc"${operand(lhs)} ${jsOp} ${operand(rhs)}"
          if needsParens(jsOp) then doc"(${res})" else res
        case N => doc"${result(s)}(${(argument(lhs) :: argument(rhs) :: Nil).mkDocument(", ")})"
    case c @ Call(fun, args) =>
      val base = subexpression(fun)
      val argsDoc = args.map(argument).mkDocument(", ")
      if c.isMlsFun
      then if checkMLsCalls
        then doc"$runtimeVar.checkCall(${base}(${argsDoc}))"
        else doc"${base}(${argsDoc})"
      else doc"$runtimeVar.safeCall(${base}(${argsDoc}))"
    case Value.Lam(ps, bod) => scope.nest givenIn:
      val (params, bodyDoc) = setupFunction(none, ps, bod)
      doc"($params) => ${ braced(bodyDoc) }"
    case Select(qual, id) =>
      val name = id.name
      doc"${result(qual)}${
        if isValidFieldName(name)
        then doc".$name"
        else name.toIntOption match
          case S(index) => s"[$index]"
          case N => s"[${makeStringLiteral(name)}]"
      }"
    case DynSelect(qual, fld, ai) =>
      doc"${result(qual)}[${result(fld)}]"
    case Instantiate(cls, as) =>
      doc"new ${result(cls)}(${as.map(result).mkDocument(", ")})"
    case Value.Arr(es) if es.isEmpty => doc"[]"
    case Value.Arr(es) =>
      doc"[ #{  # ${es.map(argument).mkDocument(doc", # ")} #}  # ]"
    case Value.Rcd(flds) =>
      doc"{ #  #{ ${
        flds.map:
          case RcdArg(S(idx), v) =>
            doc"${result(idx)}: ${result(v)}"
          case RcdArg(N, v) => doc"...${result(v)}"
        .mkDocument(", ")
      } #}  # }"
  
  def returningTerm(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    def mkSemi = if endSemi then ";" else ""
    t match
    case _: HandleBlock =>
      errStmt(msg"This code requires effect handler instrumentation but was compiled without it.")
    case Assign(l, r, rst) =>
      doc" # ${getVar(l)} = ${result(r)};${returningTerm(rst, endSemi)}"
    case AssignField(p, n, r, rst) =>
      doc" # ${result(p)}${fieldSelect(n.name)} = ${result(r)};${returningTerm(rst, endSemi)}"
    case AssignDynField(p, f, ai, r, rst) =>
      doc" # ${result(p)}[${result(f)}] = ${result(r)};${returningTerm(rst, endSemi)}"
    case Define(defn, rst) =>
      def mkThis(sym: InnerSymbol): Document =
        result(Value.This(sym))
      val resJS = defn match
      case ValDefn(own, k, sym, p) =>
        val sym = defn.sym
        // * Currently we allow `val` outside of object/module scopes,
        // * in which case it has no owner and is just a glorified local variable rather than a field.
        own match
        case N =>
          doc"${getVar(sym)} = ${result(p)};${returningTerm(rst, endSemi)}"
        case S(owner) =>
          doc"${mkThis(owner)}${fieldSelect(sym.nme)} = ${result(p)};${returningTerm(rst, endSemi)}"
      case defn: (FunDefn | ClsLikeDefn) =>
        val outerScope = scope
        val (thisProxy, res) = scope.nestRebindThis(
            // * Either this is an InnerSymbol or this is a Fun,
            // * and we need to rebind `this` to None to shadow it.
            defn.innerSym.collectFirst{ case s: InnerSymbol => s }):
          defn match
          case FunDefn(own, sym, Nil, body) =>
            lastWords("cannot generate function with no parameter list")
          case FunDefn(own, sym, ps :: pss, bod) =>
            val result = pss.foldRight(bod):
              case (ps, block) => 
                Return(Lam(ps, block), false)
            val name = if sym.nameIsMeaningful then S(sym.nme) else N
            val (params, bodyDoc) = setupFunction(name, ps, result)
            if sym.nameIsMeaningful then
              // If the name is not valid JavaScript identifiers, do not use it in the generated function.
              val nme = if isValidIdentifier(sym.nme) then sym.nme else ""
              doc"${getVar(sym)} = function $nme($params) ${ braced(bodyDoc) };"
            else
              // in JS, let name = (0, function (args) => {} ) prevents function's name from being bound to `name`
              doc"${getVar(sym)} = (undefined, function ($params) ${ braced(bodyDoc) });"
          case ClsLikeDefn(ownr, isym, sym, kind, paramsOpt, auxParams, par, mtds, privFlds, _pubFlds, preCtor, ctor) =>
            // * Note: `_pubFlds` is not used because in JS, fields are not declared
            val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
            val ctorParams = clsParams.map(p => p -> scope.allocateName(p))
            val ctorFields = ctorParams.filter: p =>
              p._1.decl match
              case S(Param(flags = FldFlags(value = true))) => true
              case _ => false
            val ctorAuxParams = auxParams.map(ps => ps.params.map(p => p.sym -> scope.allocateName(p.sym)))

            val isModule = kind is syntax.Mod
            val mtdPrefix = if isModule then "static " else ""

            val privs =
              val scp = isym.asInstanceOf[InnerSymbol].privatesScope
              privFlds.map: fld =>
                  val nme = scp.allocateName(fld)
                  doc" # $mtdPrefix#$nme;"
                .mkDocument(doc"")
            val preCtorCode = ctorAuxParams.flatMap(ps => ps).foldLeft(body(preCtor, endSemi = true)):
              case (acc, (sym, nme)) =>
                doc"$acc # this${fieldSelect(sym.name)} = $nme;"
            val ctorCode = doc"$preCtorCode${body(ctor, endSemi = auxParams.nonEmpty)}"

            val ctorAux = if auxParams.isEmpty then
              ctorCode
            else
              val pss = ctorAuxParams.map(_.map(_._2))
              val newCtorCode = doc"$ctorCode # return this;"
              val ctorBraced = doc"${ braced(newCtorCode) }"
              val funBod = pss.foldRight(ctorBraced):
                case (psDoc, doc) => doc"(${psDoc.mkDocument(", ")}) => $doc"

              doc" # return $funBod"
            
            val ctorBod = if isModule then
              ownr match
              case S(owner) =>
                braced(doc" # ${result(Value.Ref(owner))}.${sym.nme} = ${getVar(isym)};$ctorCode")
              case N =>
                braced(doc" # ${getVar(sym)} = ${getVar(isym)};$ctorCode")
            else
              braced(ctorAux)
            
            val ctorOrStatic = if isModule
              then doc"static"
              else doc"constructor(${
                  ctorParams.unzip._2.mkDocument(", ")
                })"
            val clsJS = doc"class ${scope.lookup_!(isym)}${
                par.map(p => s" extends ${result(p)}").getOrElse("")
              } { #{ ${
                privs
              } # $ctorOrStatic $ctorBod${
                if checkSelections && !isModule
                then mtds
                  .flatMap:
                    case td @ FunDefn(_, _, ps :: pss, bod) => S:
                      doc" # get ${td.sym.nme}$$__checkNotMethod() { ${
                        runtimeVar
                      }.deboundMethod(${makeStringLiteral(td.sym.nme)}, ${
                        makeStringLiteral(sym.nme)
                      }); }"
                    case _ => N
                  .mkDocument(" ")
                else doc""
              }${
                mtds.map: 
                  case td @ FunDefn(_, _, ps :: pss, bod) =>
                    val result = pss.foldRight(bod):
                      case (ps, block) => 
                        Return(Lam(ps, block), false)
                    val (params, bodyDoc) = setupFunction(some(td.sym.nme), ps, result)
                    doc" # $mtdPrefix${td.sym.nme}($params) ${ braced(bodyDoc) }"
                  case td @ FunDefn(_, _, Nil, bod) =>
                    doc" # ${mtdPrefix}get ${td.sym.nme}() ${ braced(body(bod, endSemi = true)) }"
                .mkDocument(" ")
              }${
                if mtds.exists(_.sym.nme == "toString")
                then doc""
                else doc""" # ${mtdPrefix}toString() { return "${sym.nme}${
                  if paramsOpt.isEmpty then doc"""""""
                  else doc"""(" + ${
                      ctorFields.headOption.fold("\"\"")(f => "runtime.render(this" + fieldSelect(f._1.name) + ")")
                    }${
                      ctorFields.tailOption.fold("")(_.map(f =>
                        """ + ", " + runtime.render(this""" + fieldSelect(f._1.name) + ")").mkString)
                    } + ")""""
                }; }"""
              } #}  # }"
            if (kind is syntax.Mod) || (kind is syntax.Obj) || (kind is syntax.Pat) then
              lazy val clsTmp = outerScope.allocateName(new semantics.TempSymbol(N, sym.nme+"$class"))
              ownr match
              case S(owner) =>
                assert((kind is syntax.Pat) || paramsOpt.isEmpty)
                // doc"${mkThis(owner)}.${sym.nme} = new ${clsJS}"
                if isModule
                then doc"(${clsJS});"
                else doc"const $clsTmp = ${clsJS}; # ${mkThis(owner)}.${sym.nme} = new ${clsTmp
                  }; # ${mkThis(owner)}.${sym.nme}.class = $clsTmp;"
              case N =>
                val v = getVar(sym)
                if isModule
                then doc"(${clsJS});"
                else doc"const $clsTmp = ${clsJS}; ${v} = new ${clsTmp
                  }; # ${v}.class = $clsTmp;"
            else
              val paramsAll = paramsOpt match
                case None => auxParams
                case Some(value) => value :: auxParams
              
              val fun = paramsAll match
                case ps_ :: pss_ =>
                  val (ps, _) = setupFunction(some(sym.nme), ps_, End())
                  val pss = pss_.map(setupFunction(N, _, End())._1)
                  val paramsDoc = pss.foldLeft(doc"($ps)"):
                    case (doc, ps) => doc"${doc}(${ps})"
                  val extraBrace = if paramsOpt.isDefined then "" else "()"
                  val bod = braced(doc" # return new ${sym.nme}.class$extraBrace$paramsDoc;")
                  val funBod = pss.foldRight(bod):
                    case (psDoc, doc_) => doc"($psDoc) => $doc_"
                  val funBodRet = if pss.isEmpty then funBod else braced(doc" # return $funBod")
                  val nme = if isValidIdentifier(sym.nme) then sym.nme else ""
                  S(doc"function $nme($ps) ${ funBodRet }")
                case Nil => N
              
              ownr match
              case S(owner) =>
                val ths = mkThis(owner)
                fun match
                case S(f) =>
                  doc"${ths}.${sym.nme} = ${f}; # ${ths}.${sym.nme}.class = ${clsJS};"
                case N =>
                  doc"${ths}.${sym.nme} = ${clsJS};"
              case N =>
                fun match
                case S(f) => doc"${getVar(sym)} = ${f}; # ${getVar(sym)}.class = ${clsJS};"
                case N => doc"${getVar(sym)} = ${clsJS};"
        thisProxy match
          case S(proxy) if !scope.thisProxyDefined =>
            scope.thisProxyDefined = true
            doc"const $proxy = this; # $res${returningTerm(rst, endSemi)}"
          case _ => doc"$res${returningTerm(rst, endSemi = false)}"
      doc" # $resJS"
    case Return(Value.Lit(UnitLit(false)), false) => doc" # return${mkSemi}"
    case Return(res, true) => doc" # ${result(res)}${mkSemi}"
    case Return(res, false) => doc" # return ${result(res)}${mkSemi}"
    
    case Match(scrut, Nil, els, rest) =>
      val e = els match
      case S(el) => returningTerm(el, endSemi = true)
      case N => doc""
      e :: returningTerm(rest, endSemi)
    case Match(scrut, hd :: tl, els, rest) =>
      val sd = result(scrut)
      def cond(cse: Case) = cse match
        case Case.Lit(lit) => doc"$sd === ${lit.idStr}"
        case Case.Cls(cls, pth) => cls match
          // case _: semantics.ModuleSymbol => doc"=== ${result(pth)}"
          // [invariant:0] If the class represented by `cls` does not exist at
          // runtime, then `pth` is a dummy value and should be discarded.
          case Elaborator.ctx.builtins.Str => doc"typeof $sd === 'string'"
          case Elaborator.ctx.builtins.Num => doc"typeof $sd === 'number'"
          case Elaborator.ctx.builtins.Bool => doc"typeof $sd === 'boolean'"
          case Elaborator.ctx.builtins.Int => doc"globalThis.Number.isInteger($sd)"
          case _ => doc"$sd instanceof ${result(pth)}"
        case Case.Tup(len, inf) => doc"globalThis.Array.isArray($sd) && $sd.length ${if inf then ">=" else "==="} ${len}"
        case Case.Field(n, safe = false) =>
          doc"""typeof $sd === "object" && $sd !== null && "${n.name}" in $sd"""
        case Case.Field(n, safe = true) =>
          doc""""${n.name}" in $sd"""
      val h = doc" # if (${ cond(hd._1) }) ${ braced(returningTerm(hd._2, endSemi = false)) }"
      val t = tl.foldLeft(h)((acc, arm) =>
        acc :: doc" else if (${ cond(arm._1) }) ${ braced(returningTerm(arm._2, endSemi = false)) }")
      val e = els match
      case S(el) =>
        doc" else ${ braced(returningTerm(el, endSemi = false)) }"
      case N  => doc""
      t :: e :: returningTerm(rest, endSemi)
    
    case Begin(sub, thn) =>
      doc"${returningTerm(sub, endSemi = true)}${returningTerm(thn, endSemi)}"
      
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
      
      // [fixme:0] TODO check scope and allocate local variables here (see: https://github.com/hkust-taco/mlscript/pull/293#issuecomment-2792229849)
      
      doc" # ${getVar(lbl)}: while (true) { #{ ${
        returningTerm(bod, endSemi = false)
      } # break; #}  # }${returningTerm(rst, endSemi)}"
      
    case TryBlock(sub, fin, rst) =>
      doc" # try ${ braced(returningTerm(sub, endSemi = false)) } finally ${
        braced(returningTerm(fin, endSemi = false))
      } # ${
        returningTerm(rst, endSemi).stripBreaks}"
    
    // case _ => ???
  
  /** We want to first reserve the names of all defined classes, object, and modules,
    * as these will be used as the internal names for these things, which may differ from the external name.
    * For instance, `class Foo() { ... Foo ... }` will essentially translate to
    *     `Foo1 = function Foo() { return new Foo1.class }; Foo1.class = class Foo { ... Foo1 ... }`.
    *   Here, we prefer the `class Foo` part to bear the original `Foo` name (and not, say, `Foo1` or `Foo2`),
    *   as it will be visible at JS runtime.
    *   Also note it is crucial here that the inner reference can access the outer definition `Foo1` and not `Foo`
    *   – Foo refers to the inner class in generated code and not to the parameterized Foo class of the source.
    * For modules, we do turn any `this` reference into a reference to the corresponding generated class,
    * since modules represent static members and since we want them to avoid the problem of JS method debinding.
    *   That means we must generate unique inner names, at least in the case of modules;
    *   for instance, consider that `module M with { val x = 1; module M with { val y = x } }`
    *   should generate something like `M2 = class M { static x = 1; static M1 = class M1 { static y = M.x } }`,
    *   where it is crucial that the inner module's inner name M1 not clash with the outer module's inner name M.
    * We do not reserve the names of functions, as we currently just use the source name as the inner name,
    * since any unintentional capture will have no consequence.
    *   For example, consider that `fun foo() = foo()` may generate something like
    *     `foo = function foo() { return foo(); }`
    *   or, if there was already a `foo` defined in some outer scope,
    *     `foo1 = function foo() { return foo1(); }`
    *   but the result has the same semantics.
    *  */
  def reserveNames(p: Program)(using Scope): Unit =
    def go(blk: Block): Unit = tl.trace(s"avoidNames ${blk.toString.take(100)}..."):
      blk match
      case Define(defn, rest) =>
        defn match
          case d: ClsLikeDefn =>
            scope.allocateName(d.isym)
          case _ => //scope.allocateName(defn.sym)
        defn.subBlocks.foreach(go)
        go(rest)
      case _ => blk.subBlocks.foreach(go)
    go(p.main)
  
  def program(p: Program, exprt: Opt[BlockMemberSymbol], wd: os.Path)(using Raise, Scope): Document =
    reserveNames(p)
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    val imps = p.imports.map: i =>
      val path = i._2
      val relPath = if path.startsWith("/")
        then "./" + os.Path(path).relativeTo(wd).toString
        else path
      doc"""import ${getVar(i._1)} from "${relPath}";"""
    imps.mkDocument(doc" # ") :/: block(p.main, endSemi = false).stripBreaks :: (
      exprt match
        case S(sym) => doc"\nlet ${sym.nme} = ${scope.lookup_!(sym)}; export default ${sym.nme};\n"
        case N => doc""
      )
  
  def worksheet(p: Program)(using Raise, Scope): (Document, Document) =
    reserveNames(p)
    lazy val imps = p.imports.map: i =>
      doc"""${getVar(i._1)} = await import("${i._2.toString}").then(m => m.default ?? m);"""
    blockPreamble(p.imports.map(_._1).toSeq ++ p.main.definedVars.toSeq) ->
      (imps.mkDocument(doc" # ") :/: returningTerm(p.main, endSemi = false).stripBreaks)
  
  def blockPreamble(ss: Iterable[Symbol])(using Raise, Scope): Document =
    // TODO document: mutable var assnts require the lookup
    val vars = ss.filter(scope.lookup(_).isEmpty).toArray.sortBy(_.uid).iterator.map(l =>
      l -> scope.allocateName(l))
    if vars.isEmpty then doc"" else
      doc" # let " :: vars.map: (_, nme) =>
        nme
      .toList.mkDocument(", ")
      :: doc";"
  
  def block(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    blockPreamble(t.definedVars) :: returningTerm(t, endSemi)
  
  def body(t: Block, endSemi: Bool)(using Raise, Scope): Document = scope.nest givenIn:
    block(t, endSemi)
  
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
    (paramsList, this.body(body, endSemi = false))



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
    "implements",
    "int",
    "long",
    "native",
    "package",
    "protected",
    "short",
    "static",
    "synchronized",
    "throws",
    "transient",
    "volatile",
    // not a keyword, but cannot be declared as identifier in strict mode
    "arguments",
    "eval",
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


trait JSBuilderArgNumSanityChecks(using Config, Elaborator.State)
    extends JSBuilder:
  
  val instrument: Bool = config.sanityChecks.isDefined
  
  override def checkMLsCalls: Bool = instrument
  override def checkSelections: Bool = instrument
  
  val functionParamVarargSymbol = semantics.TempSymbol(N, "args")
  
  override def setupFunction(name: Option[Str], params: ParamList, body: Block)(using Raise, Scope): (Document, Document) =
    if instrument then
      val paramsList = params.params.map(p => Scope.scope.allocateName(p.sym))
      val paramRest = params.restParam.map(p => Scope.scope.allocateName(p.sym))
      val paramsStr = Scope.scope.allocateName(functionParamVarargSymbol)
      val functionName = JSBuilder.makeStringLiteral(name.fold("")(n => s"${JSBuilder.escapeStringCharacters(n)}"))
      val checkArgsNum = doc"\n$runtimeVar.checkArgs($functionName, ${params.paramCountLB}, ${params.paramCountUB.toString}, $paramsStr.length);"
      val paramsAssign = paramsList.zipWithIndex.map{(nme, i) =>
        doc"\nlet ${nme} = ${paramsStr}[$i];"}.mkDocument("")
      val restAssign = paramRest match
        case N => doc""
        case S(p) => doc"\nlet $p = $runtimeVar.Tuple.slice($paramsStr, ${params.paramCountLB}, 0);"
      (doc"...$paramsStr", doc"$checkArgsNum$paramsAssign$restAssign${this.body(body, endSemi = false)}")
    else
      super.setupFunction(name, params, body)

