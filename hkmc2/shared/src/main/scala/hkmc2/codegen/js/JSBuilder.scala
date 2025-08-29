package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*
import document.Document.{braced, bracketed}

import hkmc2.Message.MessageContext
import hkmc2.syntax.{Tree, MutVal, ImmutVal}
import hkmc2.semantics.*
import Elaborator.{State, Ctx}
import hkmc2.codegen.Value.Lam

import Scope.scope
import hkmc2.syntax.Tree.UnitLit
import hkmc2.semantics.Elaborator.ctx
import hkmc2.syntax.Tree.{IntLit, StrLit}


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
  
  val freeze = "globalThis.Object.freeze"
  
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
  
  def getVar(l: Local, loc: Opt[Loc])(using Raise, Scope): Document = l match
    case ts: semantics.TermSymbol =>
      ts.owner match
      case S(owner) =>
        doc"${getVar(owner, loc)}${
          if (ts.k is syntax.LetBind) && !owner.isInstanceOf[semantics.TopLevelSymbol]
          then ".#" + owner.privatesScope.lookup_!(ts, loc)
          else fieldSelect(ts.id.name)
        }"
      case N => scope.lookup_!(ts, loc)
    case ts: semantics.ModuleOrObjectSymbol if ts.asMod.isDefined => // FIXME: currently, objects have a ModuleSymbol...
      // * Module self-references use the module name itself instead of `this`
      scope.lookup_!(ts, loc)
    case ts: semantics.InnerSymbol =>
      scope.findThis_!(ts)
    case _ => scope.lookup_!(l, loc)
  
  def runtimeVar(using Raise, Scope): Document = getVar(State.runtimeSymbol, N)
  
  def argument(a: Arg)(using Raise, Scope): Document =
    val spd = a.spread match
      case S(true) => doc"..."
      case S(false) => doc"$runtimeVar.Tuple.split, "
      case N => doc""
    doc"${spd}${result(a.value)}"
  
  def operand(a: Arg)(using Raise, Scope): Document =
    if a.spread.nonEmpty then die else subexpression(a.value)
  
  def subexpression(r: Result)(using Raise, Scope): Document = r match
    case _: Value.Lam => doc"(${result(r)})"
    case _ => result(r)
  
  def fieldSelect(s: Str): Document = escapeField(s, ".")
  def escapeField(s: Str, defaultPrefix: Str): Document =
    if JSBuilder.isValidFieldName(s) then doc"$defaultPrefix$s"
    else s.toIntOption match
      case S(index) => doc"[$index]"
      case N => doc"[${JSBuilder.makeStringLiteral(s)}]"
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => scope.findThis_!(sym)
    case Value.Lit(Tree.StrLit(value)) => makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Value.Ref(l: BuiltinSymbol) =>
      if l.nullary then l.nme
      else errExpr(msg"Illegal reference to builtin symbol '${l.nme}'")
    case Value.Ref(l) => getVar(l, r.toLoc)
    
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
          case S(index) => doc"[$index]"
          case N => doc"[${makeStringLiteral(name)}]"
      }"
    case DynSelect(qual, fld, ai) =>
      if ai
      then doc"${result(qual)}.at(${result(fld)})"
      else doc"${result(qual)}[${result(fld)}]"
    case Instantiate(mut, cls, as) =>
      val inner = doc"new ${result(cls)}(${as.map(argument).mkDocument(", ")})"
      if mut then inner else doc"$freeze(${inner})"
    case Value.Arr(mut, es) if es.isEmpty => if mut then "[]" else doc"$freeze([])"
    case Value.Arr(mut, es) =>
      val inner =
        val lazyConcat = es.exists(!_.spread.getOrElse(true))
        if lazyConcat
        then doc"$runtimeVar.Tuple.lazyConcat(${es.map(argument).mkDocument(doc", ")})"
        else bracketed("[", "]", insertBreak = true):
          es.map(argument).mkDocument(doc", # ")
      if mut then inner else doc"$freeze(${inner})"
    case Value.Rcd(mut, Nil) =>
      if mut then "{}" else doc"$freeze({})"
    case Value.Rcd(mut, flds) =>
      val inner = bracketed(pre = "{", post = "}", insertBreak = true):
        flds.map:
          case RcdArg(S(Value.Lit(IntLit(idx))), v) =>
            doc"${idx.toString}: ${result(v)}"
          case RcdArg(S(Value.Lit(StrLit(idx))), v) =>
            doc"${if isValidIdentifier(idx) then idx else s"\"$idx\""}: ${result(v)}"
          case RcdArg(S(idx), v) =>
            doc"[${result(idx)}]: ${result(v)}"
          case RcdArg(N, v) => doc"...${result(v)}"
        .mkDocument(doc", # ")
      if mut then inner else doc"$freeze(${inner})"
  
  def returningTerm(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    def mkSemi = if endSemi then ";" else ""
    t match
    case _: HandleBlock =>
      errStmt(msg"This code requires effect handler instrumentation but was compiled without it.")
    case Assign(l, r, rst) =>
      doc" # ${getVar(l, t.toLoc // TODO: improve location
        )} = ${result(r)};${returningTerm(rst, endSemi)}"
    case AssignField(p, n, r, rst) =>
      doc" # ${result(p)}${fieldSelect(n.name)} = ${result(r)};${returningTerm(rst, endSemi)}"
    case AssignDynField(p, f, ai, r, rst) =>
      doc" # ${result(p)}[${result(f)}] = ${result(r)};${returningTerm(rst, endSemi)}"
    case Define(defn, rst) =>
      def mkThis(sym: InnerSymbol): Document =
        result(Value.This(sym))
      val resJS = defn match
      case ValDefn(tsym, sym, p) =>
        val sym = defn.sym
        // * Currently we allow `val` outside of object/module scopes,
        // * in which case it has no owner and is just a glorified local variable rather than a field.
        tsym.owner match
        case N =>
          doc"${getVar(sym, sym.toLoc)} = ${result(p)};${returningTerm(rst, endSemi)}"
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
              doc"${getVar(sym, sym.toLoc)} = function $nme($params) ${ braced(bodyDoc) };"
            else
              // in JS, let name = (0, function (args) => {} ) prevents function's name from being bound to `name`
              doc"${getVar(sym, sym.toLoc)} = (undefined, function ($params) ${ braced(bodyDoc) });"
            
          case ClsLikeDefn(ownr, isym, sym, kind, paramsOpt, auxParams, par, mtds,
              privFlds, pubFlds, preCtor, ctor, modo)
          =>
            val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
            val ctorParams = clsParams.map(p => p -> scope.allocateName(p))
            val ctorAuxParams = auxParams.map(ps => ps.params.map(p => p.sym -> scope.allocateName(p.sym)))
            
            def mkMethods(mtds: Ls[FunDefn], mtdPrefix: Str)(using Scope): Document =
              mtds.map:
                case td @ FunDefn(_, _, ps :: pss, bod) =>
                  val result = pss.foldRight(bod):
                    case (ps, block) =>
                      Return(Lam(ps, block), false)
                  val (params, bodyDoc) = scope.nest.givenIn:
                    setupFunction(S(td.sym.nme), ps, result)
                  doc" # $mtdPrefix${td.sym.nme}($params) ${ braced(bodyDoc) }"
                case td @ FunDefn(_, _, Nil, bod) =>
                  doc" # ${mtdPrefix}get ${td.sym.nme}() ${ braced(body(bod, endSemi = true)) }"
              .mkDocument(" ")
            
            def mkPrivs(pubFlds: Ls[BlockMemberSymbol -> TermSymbol], privFlds: Ls[TermSymbol],
                  mtdPrefix: Str, isym: InnerSymbol)(using Scope): Document =
              // * Note: the non-mut-val parts of `pubFlds` are not used because in JS, fields are not declared
              val mutPubFields =
                pubFlds.collect:
                  case (_, sym) if sym.k is MutVal =>
                    sym -> TermSymbol(
                      syntax.LetBind, S(isym), Tree.Ident(sym.nme))
              val allPrivFlds = privFlds ++ mutPubFields.map(_._2)
              val privDecls = allPrivFlds.map: fld =>
                val nme = isym.privatesScope.allocateOrGetName(fld)
                doc" # $mtdPrefix#$nme;"
              val accessors = mutPubFields.flatMap: (valSym, letSym) =>
                doc" # ${mtdPrefix}get ${escapeField(valSym.name, "")
                  }() { return ${getVar(letSym, letSym.toLoc)}; }"
                :: doc" # ${mtdPrefix}set ${escapeField(valSym.name, "")
                  }(value) { ${getVar(letSym, letSym.toLoc)} = value; }"
                :: Nil
              (privDecls ::: accessors).mkDocument(doc"")
            
            val modDoc = modo match
              case N => doc""
              case S(mod) =>
                val (thisProxy, res) = outerScope.nestRebindThis(S(mod.isym)):
                  val mtdPrefix = "static "
                  val privs = mkPrivs(mod.publicFields, mod.privateFields, mtdPrefix, mod.isym)
                  val ctorCode = if mod.ctor.isEmpty then doc"" else doc" # static " :: braced:
                    body(mod.ctor, endSemi = true)
                  privs :: ctorCode :: {
                    mkMethods(mod.methods, mtdPrefix)
                  }
                // * Note that `thisProxy` might be defined at this point,
                // * if the module accesses the self-reference of an outer definition.
                // * But in that case, we'll already be creating a proxy through the `nestRebindThis` call above,
                // * and that proxy will return the same symbol, so we don't need to bind it here.
                res
            
            val mtdPrefix = ""
            
            val privs = mkPrivs(pubFlds, privFlds, mtdPrefix, isym)
            
            val preCtorCode = body(preCtor, true)
            val ctorCode = doc"$preCtorCode${body(ctor, endSemi = true)}${
                kind match
                case syntax.Obj =>
                  doc" # ${defineProperty(doc"this", "class", doc"${scope.lookup_!(isym, isym.toLoc)}")}"
                case _ => ""
              }"
            
            // * If there are no ctor params, pop one param list off the aux params
            val (newCtorAuxParams, initialCtorParams) = paramsOpt match
              case None => ctorAuxParams match
                case head :: next => (next, head)
                case Nil => (ctorAuxParams, Nil)
              case Some(_) => (ctorAuxParams, ctorParams)
            
            val ctorAux = if newCtorAuxParams.isEmpty then
              ctorCode
            else
              val pss = newCtorAuxParams.map(_.map(_._2))
              val newCtorCode = doc"$ctorCode # return this;"
              val ctorBraced = doc"${ braced(newCtorCode) }"
              val funBod = pss.foldRight(ctorBraced):
                case (psDoc, doc) => doc"(${psDoc.mkDocument(", ")}) => $doc"
              doc" # return $funBod"
            
            val ctorHead = doc"constructor(${
                  initialCtorParams.unzip._2.mkDocument(", ")
                })"
            
            val ctorBod = {
                val extraPath = if paramsOpt.isDefined then ".class" else ""
                doc" # static " :: braced:
                  val v = getVar(isym, isym.toLoc)
                  val rhs = if (kind is syntax.Obj) || (kind is syntax.Pat)
                    then doc"$freeze(new $v)"
                    else v
                  ownr match
                  case S(owner) =>
                    doc" # ${result(Value.Ref(owner))}.${sym.nme}$extraPath = $rhs"
                  case N =>
                    doc" # ${getVar(sym, sym.toLoc)}$extraPath = $rhs"
              } :/: ctorHead :: " " :: braced(ctorAux)
            
            val clsJS = doc"class ${scope.lookup_!(isym, isym.toLoc)}${
                par.map(p => doc" extends ${
                  val ext = result(p)
                  p match
                  case _: Value.Lam => doc"($ext)"
                  case _ => ext
                }").getOrElse("")
              } " :: braced:
                
                ctorBod :: modDoc :: privs :: {
                  // * Create "debound method" checkers as accessors
                  if checkSelections
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
                } :: {
                  mkMethods(mtds, mtdPrefix)
                } :: {
                  // * If this class has a `toString` implementation, then delegate
                  // * `prettyPrint` to `toString`.
                  if mtds.exists(_.sym.nme == "toString") then doc""" # [${
                    getVar(State.prettyPrintSymbol, N)
                  }]() { return this.toString(); }"""
                  // * Call the `render` function in the default `toString` method.
                  else doc" # ${mtdPrefix}toString() { return $runtimeVar.render(this); }"
                } :: {
                  doc""" # static [${getVar(State.definitionMetadataSymbol, N)}] = [${
                    kind.desc.escaped}, ${sym.nme.escaped}${
                    if (kind is syntax.Cls) && paramsOpt.isDefined then
                      doc", [${ctorParams.map { (p, _) => p.decl match
                        case S(Param(flags = FldFlags(isVal = true))) => doc"${p.name.escaped}"
                        case S(_) | N => doc"null"
                      }.mkDocument(", ")}]"
                    else doc""
                  }]; """
              }
            
            if (kind is syntax.Obj) || (kind is syntax.Pat) then
              ownr match
              case S(owner) =>
                assert((kind is syntax.Pat) || paramsOpt.isEmpty)
                doc"$freeze(${clsJS});"
              case N =>
                doc"$freeze(${clsJS});"
            else
              val paramsAll = paramsOpt match
                case None => auxParams
                case Some(value) => value :: auxParams
              
              val fun = paramsAll match
                case ps_ :: pss_ if paramsOpt.isDefined => outerScope.nest.givenIn:
                  val (ps, _) = setupFunction(some(sym.nme), ps_, End())
                  val pss = pss_.map(setupFunction(N, _, End())._1)
                  val paramsDoc = pss.foldLeft(doc"($ps)"):
                    case (doc, ps) => doc"${doc}(${ps})"
                  val inner = doc"new ${sym.nme}.class$paramsDoc"
                  val bod = braced(doc" # return $freeze($inner);")
                  val funBod = pss.foldRight(bod):
                    case (psDoc, doc_) => doc"($psDoc) => $doc_"
                  val funBodRet = if pss.isEmpty then funBod else braced(doc" # return $funBod")
                  val nme = if isValidIdentifier(sym.nme) then sym.nme else ""
                  S(doc"function $nme($ps) ${ funBodRet }")
                case _ => N
              
              ownr match
              case S(owner) =>
                val ths = mkThis(owner)
                fun match
                case S(f) =>
                  doc"${ths}.${sym.nme} = ${f}; # $freeze($clsJS);"
                case N =>
                  doc"$freeze(${clsJS});"
              case N =>
                fun match
                case S(f) =>
                  doc"${getVar(sym, sym.toLoc)} = ${f}; # $freeze($clsJS);"
                case N =>
                  doc"$freeze(${clsJS});"
        
        thisProxy match
          case S(proxy) if !scope.thisProxyDefined =>
            scope.thisProxyDefined = true
            doc"const $proxy = this; # $res${returningTerm(rst, endSemi)}"
          case _ => doc"$res${returningTerm(rst, endSemi)}"
      
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
          case Elaborator.ctx.builtins.BigInt => doc"typeof $sd === 'bigint'"
          case Elaborator.ctx.builtins.Symbol.module => doc"typeof $sd === 'symbol'"
          case Elaborator.ctx.builtins.TypedArray => doc"globalThis.ArrayBuffer.isView($sd) && !($sd instanceof globalThis.DataView)"
          case _ => doc"$sd instanceof ${result(pth)}"
        case Case.Tup(len, inf) => doc"$runtimeVar.Tuple.isArrayLike($sd) && $sd.length ${if inf then ">=" else "==="} ${len}"
        case Case.Field(name = n, safe = false) =>
          doc"""typeof $sd === "object" && $sd !== null && "${n.name}" in $sd"""
        case Case.Field(name = n, safe = true) =>
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
      doc" # throw ${result(res)}${mkSemi}"
    
    case Break(lbl) =>
      doc" # break ${getVar(lbl, t.toLoc)}${mkSemi}"
      
    case Continue(lbl) =>
      doc" # continue ${getVar(lbl, t.toLoc)}${mkSemi}"
      
    case Label(lbl, bod, rst) =>
      scope.allocateName(lbl)
      
      // [fixme:0] TODO check scope and allocate local variables here (see: https://github.com/hkust-taco/mlscript/pull/293#issuecomment-2792229849)
      
      doc" # ${getVar(lbl, lbl.toLoc)}: while (true) " :: braced {
          returningTerm(bod, endSemi = true) :/: doc"break;"
      } :: returningTerm(rst, endSemi)
      
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
            val nme = scope.allocateName(d.isym)
            d.companion match
            case N => ()
            case S(comp) =>
              // * This is a bit messy.
              // * If there is a companion module, we need to map its inner symbol to the same name
              // * as the class' inner symbol, since in the end they are consolidated into a single definition.
              scope.addToBindings(comp.isym, nme, shadow = false)
          case _ => //scope.allocateName(defn.sym)
        defn.subBlocks.foreach(go)
        go(rest)
      case _ => blk.subBlocks.foreach(go)
    go(p.main)
  
  def program(p: Program, exprt: Opt[BlockMemberSymbol], wd: os.Path)(using Raise, Scope): Document =
    scope.allocateName(State.definitionMetadataSymbol)
    scope.allocateName(State.prettyPrintSymbol)
    doc"""const ${getVar(State.definitionMetadataSymbol, N)} = globalThis.Symbol.for("mlscript.definitionMetadata");"""
      :/: doc"""const ${getVar(State.prettyPrintSymbol, N)} = globalThis.Symbol.for("mlscript.prettyPrint");"""
      :/: programBody(p, exprt, wd)
  
  def programBody(p: Program, exprt: Opt[BlockMemberSymbol], wd: os.Path)(using Raise, Scope): Document =
    reserveNames(p)
    // Allocate names for imported modules.
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    // Generate import statements.
    val imps = p.imports.map: i =>
      val path = i._2
      val relPath = if path.startsWith("/")
        then "./" + os.Path(path).relativeTo(wd).toString
        else path
      doc"""import ${getVar(i._1, N)} from "${relPath}";"""
    imps.mkDocument(doc" # ") :/: block(p.main, endSemi = false).stripBreaks :: (
      exprt match
        case S(sym) => doc"\nlet ${sym.nme} = ${scope.lookup_!(sym, sym.toLoc)}; export default ${sym.nme};\n"
        case N => doc""
      )
  
  def worksheet(p: Program)(using Raise, Scope): (Document, Document) =
    reserveNames(p)
    lazy val imps = p.imports.map: i =>
      doc"""${getVar(i._1, N)} = await import("${i._2.toString}").then(m => m.default ?? m);"""
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
  
  def defineProperty(target: Document, prop: Str, value: Document, enumerable: Bool = false): Document =
    doc"Object.defineProperty(${target}, ${prop.escaped}, ${
      bracketed("{", "}", insertBreak = true):
        (if enumerable then doc"enumerable: true, # " else doc"") :: doc"value: ${value}"
    })"
  
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
      val paramsList = params.params.map(p => scope.allocateName(p.sym))
      val paramRest = params.restParam.map(p => scope.allocateName(p.sym))
      val paramsStr = scope.allocateName(functionParamVarargSymbol, shadow = true)
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

