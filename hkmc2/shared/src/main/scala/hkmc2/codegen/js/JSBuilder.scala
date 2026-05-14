package hkmc2
package codegen
package js

import mlscript.utils.*, shorthands.*
import utils.*
import document.*
import document.Document.{braced, bracketed}

import hkmc2.Message.MessageContext
import hkmc2.syntax.{Tree, MutVal, ImmutVal, SpreadKind}
import hkmc2.semantics.*
import Elaborator.{State, Ctx}
import hkmc2.codegen.Lambda

import Scope.scope
import hkmc2.syntax.Tree.UnitLit
import hkmc2.semantics.Elaborator.ctx
import hkmc2.syntax.Tree.{IntLit, StrLit}
import scala.annotation.tailrec


// TODO factor some logic for other codegen backends
abstract class CodeBuilder:
    
  type Context
  

class JSBuilder(using Config, TL, State, Ctx) extends CodeBuilder:
  import JSBuilder.*
  
  def checkMLsCalls: Bool = false
  def checkSelections: Bool = false
  def freezeDefinitions: Bool = false
  
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
  
  val freeze = if !config.noFreeze then "globalThis.Object.freeze" else ""
  lazy val freezeDefns = if freezeDefinitions && !config.noFreeze then "globalThis.Object.freeze" else ""
  
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
      case S(SpreadKind.Eager) => doc"..."
      case S(SpreadKind.Lazy) => doc"$runtimeVar.Tuple.split, "
      case N => doc""
    doc"${spd}${result(a.value)}"
  
  def operand(a: Arg)(using Raise, Scope): Document =
    if a.spread.nonEmpty then die else subexpression(a.value)
  
  def subexpression(r: Result)(using Raise, Scope): Document = r match
    case _: Lambda => doc"(${result(r)})"
    case _ => result(r)
  
  def fieldSelect(s: Str): Document = escapeField(s, ".")
  def escapeField(s: Str, defaultPrefix: Str): Document =
    if JSBuilder.isValidFieldName(s) then doc"$defaultPrefix$s"
    else s.toIntOption match
      case S(index) => doc"[$index]"
      case N => doc"[${JSBuilder.makeStringLiteral(s)}]"
  
  // For use as the qualifier of a field selection
  def resultQual(r: Result)(using Raise, Scope): Document =
    val res = result(r)
    if r.isInstanceOf[Value.Lit] then doc"(${res})" else res
  
  def result(r: Result)(using Raise, Scope): Document = r match
    case Value.This(sym) => scope.findThis_!(sym)
    case Value.Lit(Tree.StrLit(value)) => makeStringLiteral(value)
    case Value.Lit(lit) => lit.idStr
    case Value.Ref(l: BuiltinSymbol, _) =>
      if l.nullary then l.nme
      else errExpr(msg"Illegal reference to builtin symbol '${l.nme}'")
    case Value.Ref(l, disamb) => l match
      case l: BlockMemberSymbol if disamb.exists(_.shouldBeLifted) =>
        doc"${getVar(l, l.toLoc)}.class"
      case _ =>
        getVar(l, r.toLoc)
    case Call(Value.Ref(l: BuiltinSymbol, _), (lhs :: rhs :: Nil) :: Nil) if !l.functionLike =>
      if l.binary then
        val res = doc"${operand(lhs)} ${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else errExpr(msg"Cannot call non-binary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol, _), (rhs :: Nil) :: Nil) if !l.functionLike =>
      if l.unary then
        val res = doc"${l.nme} ${operand(rhs)}"
        if needsParens(l.nme) then doc"(${res})" else res
      else errExpr(msg"Cannot call non-unary builtin symbol '${l.nme}'")
    case Call(Value.Ref(l: BuiltinSymbol, _), args :: Nil) =>
      if l.functionLike then
        val argsDoc = args.map(argument).mkDocument(", ")
        doc"${l.nme}(${argsDoc})"
      else errExpr(msg"Illegal arity for builtin symbol '${l.nme}'")
    
    case Call(s @ Select(_, Elaborator.ctx.builtins.BuiltInOpIdent(jsOp)), (lhs :: rhs :: Nil) :: Nil) =>
      val res = doc"${operand(lhs)} ${jsOp} ${operand(rhs)}"
      if needsParens(jsOp) then doc"(${res})" else res
    case c @ Call(fun, argss) =>
      val base = subexpression(fun)
      val calls = argss.foldLeft(base): (acc, args) =>
        val argsDoc = args.map(argument).mkDocument(", ")
        doc"${acc}(${argsDoc})"
      if c.isMlsFun
      then if checkMLsCalls
        then doc"$runtimeVar.checkCall(${calls})"
        else doc"${calls}"
      else doc"$runtimeVar.safeCall(${calls})"
    case Lambda(ps, bod) => scope.nest givenIn:
      val (params, bodyDoc) = setupFunction(none, ps, bod, isLambda = true)
      doc"($params) => ${ braced(bodyDoc) }"
    case s @ Select(qual, id) => 
      val dotClass = s.symbol match
        case S(ds) if ds.shouldBeLifted => doc".class"
        case _ => doc""
      val name = id.name
      doc"${resultQual(qual)}${
        if isValidFieldName(name)
        then doc".$name"
        else name.toIntOption match
          case S(index) => doc"[$index]"
          case N => doc"[${makeStringLiteral(name)}]"
      }${dotClass}"
    case DynSelect(qual, fld, ai) =>
      if ai
      then doc"${resultQual(qual)}.at(${result(fld)})"
      else doc"${result(qual)}[${result(fld)}]"
    case Instantiate(mut, cls, argss) =>
      val calls = argss.foldLeft(result(cls)): (acc, args) =>
        doc"${acc}(${args.map(argument).mkDocument(", ")})"
      val inner = doc"new $calls"
      if mut then inner else doc"$freeze(${inner})"
    case Tuple(mut, es) if es.isEmpty => if mut then "[]" else doc"$freeze([])"
    case Tuple(mut, es) =>
      val inner =
        val lazyConcat = es.exists(!_.spread.fold(true)(_.isEager))
        if lazyConcat
        then doc"$runtimeVar.Tuple.lazyConcat(${es.map(argument).mkDocument(doc", ")})"
        else bracketed("[", "]", insertBreak = true):
          es.map(argument).mkDocument(doc", # ")
      if mut then inner else doc"$freeze(${inner})"
    case Record(mut, Nil) =>
      if mut then "{}" else doc"$freeze({})"
    case Record(mut, flds) =>
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
  
  /**
    * Matches the following kind of if statement, where ai are ints:
    * 
    * ```
    * if scrut is a1 do
    *   body1
    *   set scrut = a2
    * if scrut is a2 do
    *   body2
    *   set scrut = a3
    * if scrut is an do
    *   bodyn
    * ```
    * 
    * The intention is that this can be compiled efficiently into a switch statement:
    * 
    * ```js
    * switch (scrut) {
    *   case a1:
    *     body1
    *     scrut = a2;
    *   case a2:
    *     body2
    *     scrut = a3;
    *   ...
    *   case an:
    *     bodyn
    * }
    * ```
    * Note that `scrut` is guaranteed to not change between `set scrut = ai` and `if scrut is ai`,
    * because the JS event loop waits until the entire call stack is cleared before running any other
    * code. Hence, this transformation is safe.
    */
  object IfIntChain:
    @tailrec
    private def lastBlkAssign(b: Block): Opt[Assign] = b match
      case a @ Assign(lhs, rhs, End(_)) => S(a)
      case b: NonBlockTail => lastBlkAssign(b.rest)
      case _: BlockTail => N
    
    @tailrec
    private def unapplyImpl(
      b: Block, 
      acc: List[(BigInt, Block)],
      scrut: Opt[Value.Ref],
      curVal: Opt[BigInt]
    ): Opt[(Value.Ref, List[(BigInt, Block)], Block)] = 
      val scrutSym = scrut.map(_.l)
      b match
      case Match(
        scrut_ @ Value.Ref(scrutSym_, _),                   // The scrutinee is a ref.
        (Case.Lit(Tree.IntLit(curVal_)), b) :: Nil,         // There is only one case matching an int literal.
        S(End(_)) | N, rest                                 // Default case exists and does nothing.
      )
        if scrutSym.map(_ === scrutSym_).getOrElse(true)    // The scrutinee is the same as the one before.
        && curVal.map(_ === curVal_).getOrElse(true)        // The matched int literal is one previously set.
        =>
          lastBlkAssign(b) match
          // the one branch ends by assigning `nextInt` to `scrutSym`
          case S(Assign(`scrutSym_`, Value.Lit(Tree.IntLit(nextInt)), _)) =>
            unapplyImpl(rest, (curVal_, b) :: acc, S(scrut_), S(nextInt))
          case _ =>
            S((scrut_, (curVal_, b) :: acc, rest))
      case _ => scrut match
        case Some(value) => S((value, acc, b))
        case None => N
    
    def unapply(b: Block): Opt[(scrut: Value.Ref, cases: List[(BigInt, Block)], rest: Block)] =
      unapplyImpl(b, Nil, N, N) match
        case Some(value) if value._2.length > 1 => S(value)
        case _ => N
  
  def returningTerm(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    def mkSemi = if endSemi then ";" else ""
    t match
    case Assign(l, r, rst) if l is State.noSymbol =>
      doc" # ${result(r)};${returningTerm(rst, endSemi)}"
    case Assign(l, r, rst) =>
      doc" # ${getVar(l, l.toLoc // TODO: improve location
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
          val thisDoc = mkThis(owner)
          val nme = sym.nme
          owner match 
          case mod: ModuleOrObjectSymbol if (mod.tree.k is syntax.Mod) && (nme == "name" || nme == "length") =>
            // * JavaScript class constructors have built-in non-writable `name` and `length` properties.
            // * Use Object.defineProperty to override them in module/class static contexts.
            doc"Object.defineProperty(${thisDoc}, ${nme.escaped}, { configurable: true, enumerable: true, writable: true, value: ${result(p)} });${returningTerm(rst, endSemi)}"
          case _ =>
            doc"${thisDoc}${fieldSelect(nme)} = ${result(p)};${returningTerm(rst, endSemi)}"
      case defn: (FunDefn | ClsLikeDefn) =>
        
        val outerScope = scope
        val (thisProxy, res) = scope.nestRebindThis(
            // * Either this is an InnerSymbol or this is a Fun,
            // * and we need to rebind `this` to None to shadow it.
            defn.innerSym.collectFirst{ case s: InnerSymbol => s }):
          defn match
            
          case FunDefn(params = Nil) =>
            lastWords("cannot generate function with no parameter list")
          case FunDefn(own, sym, dSym, ps :: pss, bod) =>
            val result = pss.foldRight(bod):
              case (ps, block) =>
                Return(Lambda(ps, block), false)
            val displayName = if sym.nameIsMeaningful then S(dSym.name) else N
            
            // * We may need to set up the function in a nested scope in one case below, so this is marked as lazy.
            lazy val (params, bodyDoc) = setupFunction(displayName, ps, result, isLambda = false)
            
            val symName = sym.nme
            
            // * If the name is a valid JavaScript identifier, use it in the generated function code.
            if sym.nameIsMeaningful && isValidIdentifier(symName)
            then
              val varName = getVar(sym, dSym.toLoc)
              scope.reverseLookup(sym.nme) match
              // * Maybe the function's internal name was already bound in scope;
              // * in that case, we need to forward it to a different variable to avoid unintended capture.
              case S(otherSym) if (otherSym isnt sym) && bod.freeVars.contains(otherSym) => scope.nest.givenIn:
                val externalName = scope.allocateName(otherSym, prefix = "proxy$", shadow = true)
                val (params, bodyDoc) = setupFunction(displayName, ps, result, isLambda = false)
                doc"const $externalName = $symName; ${
                  varName} = function $symName($params) ${ braced(bodyDoc) };"
              case _ =>
                doc"${varName} = function ${sym.nme}($params) ${ braced(bodyDoc) };"
            else
              // * In JS, `let x = (0, function (args) {...})` makes the function anonymous;
              // * otherwise, using `let x = function (args) {...}` would name the function `x`,
              // * which is not meaningful, here.
              doc"${getVar(sym, dSym.toLoc)} = (undefined, function ($params) ${ braced(bodyDoc) });"
            
          case ClsLikeDefn(ownr, isym, sym, ctorSym, kind, paramsOpt, auxParams, par, mtds,
              privFlds, pubFlds, preCtor, ctor, modo, bufferable)
          =>
            val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
            val ctorParams = clsParams.map(p => p -> scope.allocateName(p))
            val ctorAuxParams = auxParams.map(ps => ps.params.map(p => p.sym -> scope.allocateName(p.sym)))
            
            def mkMethods(mtds: Ls[FunDefn], mtdPrefix: Str)(using Scope): Document =
              mtds.map:
                case td @ FunDefn(params = ps :: pss, body = bod) =>
                  val result = pss.foldRight(bod):
                    case (ps, block) =>
                      Return(Lambda(ps, block), false)
                  val (params, bodyDoc) = scope.nest.givenIn:
                    setupFunction(S(td.sym.nme), ps, result, isLambda = false)
                  doc" # $mtdPrefix${td.sym.nme}($params) ${ braced(bodyDoc) }"
                case td @ FunDefn(params = Nil, body = bod) =>
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
            
            val isSingleton = (kind is syntax.Obj) || (kind is syntax.Pat)
            
            val (singletonInit, singletonFreeze) =
              if isSingleton
              then
                val fz = doc" # $freeze(this);"
                ownr match
                case S(owner) =>
                  (doc" # ${result(Value.Ref(owner, N))}.${sym.nme} = this;", fz)
                case N =>
                  (doc" # ${getVar(sym, sym.toLoc)} = this;", fz)
              else (doc"", doc"")
            
            val ctorCode = scope.nest.givenIn:
              val preCtorCode = nonNestedScoped(preCtor)(bd => block(bd, true))
              doc"$preCtorCode$singletonInit${nonNestedScoped(ctor)(bd => block(bd, endSemi = true))}${
                  kind match
                  case syntax.Obj =>
                    doc" # ${defineProperty(doc"this", "class", doc"${scope.lookup_!(isym, isym.toLoc)}")};"
                  case _ => ""
                }$singletonFreeze"
            
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
            
            val ctorBod = {{
                val extraPath = if paramsOpt.isDefined then ".class" else ""
                doc" # static " :: braced:
                  val v = getVar(isym, isym.toLoc)
                  if isSingleton
                  then doc" # new $v"
                  else
                    ownr match
                    case S(owner) =>
                      doc" # ${result(Value.Ref(owner, N))}.${sym.nme}$extraPath = $v"
                    case N =>
                      doc" # ${getVar(sym, sym.toLoc)}$extraPath = $v"
              }} :: (
                if ctorAux.isEmpty then doc""
                else doc" # constructor(${initialCtorParams.unzip._2.mkDocument(", ")}) " :: braced(ctorAux)
              )
            
            val clsJS = doc"class ${scope.lookup_!(isym, isym.toLoc)}${
                par.map(p => doc" extends ${
                  result(p)
                }").getOrElse("")
              } " :: braced:
                
                ctorBod :: modDoc :: privs :: {
                  // * Create "debound method" checkers as accessors
                  if checkSelections
                  then mtds
                    .flatMap:
                      case td @ FunDefn(params = ps :: pss, body = bod) => S:
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
            
            if isSingleton then
              ownr match
              case S(owner) =>
                assert((kind is syntax.Pat) || paramsOpt.isEmpty)
                doc"$freezeDefns(${clsJS});"
              case N =>
                doc"$freezeDefns(${clsJS});"
            else
              val paramsAll = paramsOpt match
                case None => auxParams
                case Some(value) => value :: auxParams
              
              val fun = paramsAll match
                case ps_ :: pss_ if paramsOpt.isDefined => outerScope.nest.givenIn:
                  val (ps, _) = setupFunction(some(sym.nme), ps_, End(), isLambda = false)
                  val pss = pss_.map(setupFunction(N, _, End(), isLambda = false)._1)
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
                  doc"${ths}.${sym.nme} = ${f}; # $freezeDefns($clsJS);"
                case N =>
                  doc"$freezeDefns(${clsJS});"
              case N =>
                fun match
                case S(f) =>
                  doc"${getVar(sym, sym.toLoc)} = ${f}; # $freezeDefns($clsJS);"
                case N =>
                  doc"$freezeDefns(${clsJS});"
        
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
      case S(el) => nonBracedScoped(el)(bod => returningTerm(bod, endSemi = true))
      case N => doc""
      e :: returningTerm(rest, endSemi)
    case Match(scrut, (Case.Lit(lit), End(msg)) :: Nil, S(el), rest) =>
      val sd = result(scrut)
      val e = braced(nonBracedScoped(el)(res => returningTerm(res, endSemi = false)))
      doc" # if ($sd !== ${lit.idStr}) $e" :: returningTerm(rest, endSemi)
    case SpecializedSwitch(scrut, cases, dflt, rest) =>
      val switchBod = cases.foldLeft(doc""): (acc, arm) =>
        val needsBreak = arm.isInstanceOf[SwitchCase.ExplicitBreak]
        acc :: doc" # case ${result(Value.Lit(arm.litValue))}: #{ ${
          // * Note: we use `block` here so that Scoped nodes will create proper brace sections,
          // * necessary since `case` clauses do not create a new scope,
          // * so something like `switch (x) { case 1: let y = 1; break; case 2: let y = 2 }` is ill-formed!
          block(arm.body, endSemi = true)
        }${if needsBreak then doc" # break;" else ""} #} "
      val bodWithDflt = doc"${switchBod}${dflt match
        case Some(bd) => doc" # default: #{ ${nonBracedScoped(bd)(bd => returningTerm(bd, endSemi = true))} #} "
        case None => doc""
      }"
      doc" # switch (${result(scrut)}) { #{ ${bodWithDflt} #}  # }" :: returningTerm(rest, endSemi)
    case Match(scrut, arms @ hd :: tl, els, rest) =>
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
          case _: ModuleOrObjectSymbol => doc"$sd instanceof ${result(pth)}.class"
          case _ => doc"$sd instanceof ${result(pth)}"
        case Case.Tup(len, inf) => doc"$runtimeVar.Tuple.isArrayLike($sd) && $sd.length ${if inf then ">=" else "==="} ${len}"
        case Case.Field(name = n, safe = false) =>
          doc"""typeof $sd === "object" && $sd !== null && "${n.name}" in $sd"""
        case Case.Field(name = n, safe = true) =>
          doc""""${n.name}" in $sd"""
      val h = doc" # if (${ cond(hd._1) }) ${ braced(nonBracedScoped(hd._2)(res => returningTerm(res, endSemi = false))) }"
      val t = tl.foldLeft(h)((acc, arm) =>
        acc :: doc" else if (${ cond(arm._1) }) ${ braced(nonBracedScoped(arm._2)(res => returningTerm(res, endSemi = false))) }")
      val e = els match
        case S(End(_)) => doc""
        case S(el) if arms.forall(_._2.isAbortive) =>
          // * We print the `else` branch outside, after the `if` when all arms are abortive.
          // * This typically results in slightly more concise code.
          // * Not sure it's necessarily a good idea, though. (Does it affect the performance of the generated code?)
          returningTerm(el, endSemi = true)
        case S(el) =>
          doc" else ${ braced(nonBracedScoped(el)(res => returningTerm(res, endSemi = false))) }"
        case N  => doc""
      t :: e :: returningTerm(rest, endSemi)
    
    case Begin(sub, thn) =>
      doc"${returningTerm(sub, endSemi = true)}${returningTerm(thn, endSemi)}"
      
    case End(msg) if config.commentGeneratedCode && msg.nonEmpty =>
      doc" # /* $msg */"
    case End(_) => doc""
    
    case Unreachable(msg) if config.sanityChecks.exists(_.checkUnreachable) =>
      doc" # throw new Error(${makeStringLiteral(s"Reached 'unreachable' code ($msg)")});"
    case Unreachable(msg) if config.commentGeneratedCode =>
      if msg.isEmpty then doc" # /* Unreachable */"
      else doc" # /* Unreachable: $msg */"
    case Unreachable(_) => doc""
    
    case Throw(res) =>
      doc" # throw ${result(res)}${mkSemi}"
    
    case Break(lbl) =>
      doc" # break ${getVar(lbl, lbl.toLoc)}${mkSemi}"
      
    case Continue(lbl) =>
      doc" # continue ${getVar(lbl, lbl.toLoc)}${mkSemi}"
      
    case Label(lbl, loop, bod, rst) =>
      scope.allocateName(lbl)
      
      // [fixme:0] TODO check scope and allocate local variables here (see: https://github.com/hkust-taco/mlscript/pull/293#issuecomment-2792229849)
      
      doc" # ${getVar(lbl, lbl.toLoc)}:${if loop then doc" while (true)" else ""} " :: braced {
          nonBracedScoped(bod)(bd => returningTerm(bd, endSemi = true)) :: (if loop && !bod.isAbortive then doc" # break;" else doc"")
      } :: returningTerm(rst, endSemi)
      
    case TryBlock(sub, fin, rst) =>
      doc" # try ${ braced(returningTerm(sub, endSemi = false)) } finally ${
        braced(returningTerm(fin, endSemi = false))
      } # ${
        returningTerm(rst, endSemi).stripBreaks}"

    // Only nested scopes in unusual positions are handled here.
    case Scoped(syms, body) =>
      doc" # " :: braced:
        scope.nest.givenIn:
          blockPreamble(syms.view.filter(body.freeVars)) :: returningTerm(body, endSemi = endSemi)
    
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
  def reserveNames(p: Program)(using Scope, Raise): Unit =
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
  
  def program(p: Program, exprt: Opt[BlockMemberSymbol], wd: io.Path)(using Raise, Scope): Document =
    scope.allocateName(State.definitionMetadataSymbol)
    scope.allocateName(State.prettyPrintSymbol)
    doc"""const ${getVar(State.definitionMetadataSymbol, N)} = globalThis.Symbol.for("mlscript.definitionMetadata");"""
      :/: doc"""const ${getVar(State.prettyPrintSymbol, N)} = globalThis.Symbol.for("mlscript.prettyPrint");"""
      :/: programBody(p, exprt, wd)
  
  def programBody(p: Program, exprt: Opt[BlockMemberSymbol], wd: io.Path)(using Raise, Scope): Document =
    reserveNames(p)
    // Allocate names for imported modules.
    p.imports.foreach: i =>
      i._1 -> scope.allocateName(i._1)
    // Generate import statements.
    val imps = p.imports.map: i =>
      val path = i._2
      val relPath = if path.startsWith("/")
        then "./" + io.Path(path).relativeTo(wd).map(_.toString).getOrElse(path)
        else path
      doc"""import ${getVar(i._1, N)} from "${relPath}";"""
    imps.mkDocument(doc" # ")
    :/: nonNestedScoped(p.main)(block(_, endSemi = false)).stripBreaks
    :: locally:
      exprt match
      case S(sym) => doc"\nlet ${sym.nme} = ${scope.lookup_!(sym, sym.toLoc)}; export default ${sym.nme};\n"
      case N => doc""
  
  def worksheet(p: Program)(using Raise, Scope): (Document, Document) =
    reserveNames(p)
    lazy val imps = p.imports.map: i =>
      doc"""${getVar(i._1, N)} = await import("${i._2.toString}").then(m => m.default ?? m);"""
    p.main match
    case Scoped(syms, body) =>
      val fvs = body.freeVars
      blockPreamble(p.imports.map(_._1) ++ syms.view.filter(s =>
          !s.isInstanceOf[TempSymbol]
          // ^ VarSymbols and TermSymbols should be kept as their value will be acessed and printed by the worksheet
          || fvs(s))) ->
        (imps.mkDocument(doc" # ") :/: block(body, endSemi = false).stripBreaks)
    case body =>
      blockPreamble(p.imports.map(_._1)) ->
        (imps.mkDocument(doc" # ") :/: returningTerm(body, endSemi = false).stripBreaks)
  
  def genLetDecls(vars: Iterator[(Symbol, Str)]): Document =
    if vars.isEmpty then doc"" else
      doc" # let " :: vars.map: (_, nme) =>
        nme
      .toList.mkDocument(", ")
      :: doc";"
  
  def blockPreamble(ss: Iterable[Symbol])(using Raise, Scope): Document =
    val vars = ss.toArray.sortBy(_.uid).iterator.map: l =>
      whenValidatingIR:
        if scope.lookup(l).isDefined then // * It is invalid to shadow symbols in the IR
          raise:
            WarningReport(msg"var ${l.toString()} in scoped is already allocated" -> N :: Nil)
      l -> scope.allocateName(l)
    genLetDecls(vars)

  /** Specially handle top-level Scoped node: output the bindings, but do not add another pair of braces */
  def nonBracedScoped(blk: Block)(k: Scope ?=> Block => Document)(using Raise, Scope): Document = blk match
    case Scoped(syms, body) =>
      scope.nest.givenIn:
        blockPreamble(syms.view.filter(body.freeVars)) :: k(body)
    case _ => k(blk)
  
  /** Like `nonBracedScoped`, but not not create a nested scope – useful in fringe JS scenarios */
  def nonNestedScoped(blk: Block)(k: Block => Document)(using Raise, Scope): Document = blk match
    case Scoped(syms, body) =>
      blockPreamble(syms.view.filter(body.freeVars)) :: k(body)
    case _ => k(blk)
  
  
  def block(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    returningTerm(t, endSemi)
  
  def body(t: Block, endSemi: Bool)(using Raise, Scope): Document =
    nonBracedScoped(t)(bd => block(bd, endSemi))
  
  def defineProperty(target: Document, prop: Str, value: Document, enumerable: Bool = false): Document =
    doc"Object.defineProperty(${target}, ${prop.escaped}, ${
      bracketed("{", "}", insertBreak = true):
        (if enumerable then doc"enumerable: true, # " else doc"") :: doc"value: ${value}"
    })"
  
  def setupFunction(name: Option[Str], params: ParamList, body: Block, isLambda: Bool)
      (using Raise, Scope): (Document, Document) =
    val paramsList = params.params.map(p => scope.allocateName(p.sym))
      .++(params.restParam.map(p => "..." + scope.allocateName(p.sym)))
      .mkDocument(", ")
    (paramsList, this.body(body, endSemi = false))



object JSBuilder:
  
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
  
  extension (dsym: DefinitionSymbol[?])
    def shouldBeLifted: Bool = 
      val bsym = dsym.asBlkMember
      (
        (dsym.asTrm orElse bsym.flatMap(_.asTrm)).isDefined ||
        (dsym.asCls orElse bsym.flatMap(_.asCls)).flatMap(_.defn).exists(_.paramsOpt.isDefined)
      ) && 
        (dsym.asModOrObj orElse dsym.asCls).isDefined
  
end JSBuilder


trait JSBuilderArgNumSanityChecks(using TL, Config, Elaborator.State)
    extends JSBuilder:
  
  private val doInstrument = config.sanityChecks.isDefined
  private val init = true
  def instrument: Bool =
    require(init, "trait body is not yet initialized")
    doInstrument
  
  override def checkMLsCalls: Bool = instrument
  override def checkSelections: Bool = instrument
  override def freezeDefinitions: Bool = instrument
  
  val functionParamVarargSymbol = semantics.TempSymbol(N, "args")
  
  override def setupFunction(name: Option[Str], params: ParamList, body: Block, isLambda: Bool)(using Raise, Scope): (Document, Document) =
    // * We used to instrument `fun f(x, y) = x + y` into something like
    // * `function f(...args) { runtime.checkArgs("f", 2, true, args.length); let x = args[0]; let y = args[1]; x + y }`
    // * which was very verbose, in addition to possibly making things quite inefficient.
    // * Now, we no longer instrument lambdas (which affects extra parameter lists),
    // * and we instead use the JS builtin `arguments` array to get the number of received arguments, as in
    // * `function f(x, y) { runtime.checkArgs("f", 2, true, arguments.length); x + y }`
    // * The idea is that later on, we'll add a runtime type sanity check as well anyway,
    // * which will check arguments against the erased parameter type,
    // * including checking they are not `undefined`, which should achieve most of the benefit.
    /*
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
    */
    if instrument && !isLambda then
      val functionName = JSBuilder.makeStringLiteral(name.fold("")(n => s"${JSBuilder.escapeStringCharacters(n)}"))
      val checkArgsNum = doc"\n$runtimeVar.checkArgs($functionName, ${params.paramCountLB}, ${params.paramCountUB.toString}, arguments.length);"
      val paramsList = params.params.map(p => scope.allocateName(p.sym))
        .++(params.restParam.map(p => "..." + scope.allocateName(p.sym)))
        .mkDocument(", ")
      (paramsList,
        doc"$checkArgsNum${this.body(body, endSemi = false)}")
    else
      super.setupFunction(name, params, body, isLambda = isLambda)


