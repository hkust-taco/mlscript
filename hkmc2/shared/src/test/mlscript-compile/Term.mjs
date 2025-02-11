import fs from "fs";
import process from "process";
import path from "path";
import url from "url";
import Predef from "./Predef.mjs";
import Str from "./Str.mjs";
let Term2;
Term2 = class Term {
  static #builtinSymbols;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    this.Symbol = function Symbol(name1) { return new Symbol.class(name1); };
    this.Symbol.class = class Symbol {
      constructor(name) {
        this.name = name;
      }
      toString() { return "Symbol(" + globalThis.Predef.render(this.name) + ")"; }
    };
    this.ConstructorLike = class ConstructorLike {
      constructor() {}
      toString() { return "ConstructorLike"; }
    };
    this.SymbolCons = function SymbolCons(symbol1) { return new SymbolCons.class(symbol1); };
    this.SymbolCons.class = class SymbolCons {
      constructor(symbol) {
        this.symbol = symbol;
      }
      toString() { return "SymbolCons(" + globalThis.Predef.render(this.symbol) + ")"; }
    };
    this.StringJoin = class StringJoin {
      constructor() {}
      toString() { return "StringJoin"; }
    };
    this.TupleCapacity = function TupleCapacity(size1, inf1) { return new TupleCapacity.class(size1, inf1); };
    this.TupleCapacity.class = class TupleCapacity {
      constructor(size, inf) {
        this.size = size;
        this.inf = inf;
      }
      toString() { return "TupleCapacity(" + globalThis.Predef.render(this.size) + ", " + globalThis.Predef.render(this.inf) + ")"; }
    };
    this.Instantiation = function Instantiation(symbol1, args1) { return new Instantiation.class(symbol1, args1); };
    this.Instantiation.class = class Instantiation {
      constructor(symbol, args) {
        this.symbol = symbol;
        this.args = args;
      }
      toString() { return "Instantiation(" + globalThis.Predef.render(this.symbol) + ", " + globalThis.Predef.render(this.args) + ")"; }
    };
    this.LocalPattern = function LocalPattern(id1) { return new LocalPattern.class(id1); };
    this.LocalPattern.class = class LocalPattern {
      constructor(id) {
        this.id = id;
      }
      toString() { return "LocalPattern(" + globalThis.Predef.render(this.id) + ")"; }
    };
    this.Parameter = function Parameter(symbol1) { return new Parameter.class(symbol1); };
    this.Parameter.class = class Parameter {
      constructor(symbol) {
        this.symbol = symbol;
      }
      toString() { return "Parameter(" + globalThis.Predef.render(this.symbol) + ")"; }
    };
    this.Nested = function Nested(split1) { return new Nested.class(split1); };
    this.Nested.class = class Nested {
      constructor(split) {
        this.split = split;
      }
      toString() { return "Nested(" + globalThis.Predef.render(this.split) + ")"; }
    };
    this.PatternStub = class PatternStub {
      constructor() {}
      toString() { return "PatternStub"; }
    };
    this.LiteralStub = function LiteralStub(value1) { return new LiteralStub.class(value1); };
    this.LiteralStub.class = class LiteralStub {
      constructor(value) {
        this.value = value;
      }
      toString() { return "LiteralStub(" + globalThis.Predef.render(this.value) + ")"; }
    };
    this.CharClass = function CharClass(start1, end1, inclusive1) { return new CharClass.class(start1, end1, inclusive1); };
    this.CharClass.class = class CharClass {
      constructor(start, end, inclusive) {
        this.start = start;
        this.end = end;
        this.inclusive = inclusive;
      }
      toString() { return "CharClass(" + globalThis.Predef.render(this.start) + ", " + globalThis.Predef.render(this.end) + ", " + globalThis.Predef.render(this.inclusive) + ")"; }
    };
    this.ClassLikeStub = function ClassLikeStub(cons1) { return new ClassLikeStub.class(cons1); };
    this.ClassLikeStub.class = class ClassLikeStub {
      constructor(cons) {
        this.cons = cons;
      }
      toString() { return "ClassLikeStub(" + globalThis.Predef.render(this.cons) + ")"; }
    };
    this.Wildcard = class Wildcard {
      constructor() {}
      toString() { return "Wildcard"; }
    };
    this.DebrujinSplit = class DebrujinSplit {
      constructor() {}
      toString() { return "DebrujinSplit"; }
    };
    this.Binder = function Binder(body1) { return new Binder.class(body1); };
    this.Binder.class = class Binder {
      constructor(body) {
        this.body = body;
      }
      toString() { return "Binder(" + globalThis.Predef.render(this.body) + ")"; }
    };
    this.DebrujinBranch = function DebrujinBranch(scrutinee1, ptrn1, consequent1, alternative1) { return new DebrujinBranch.class(scrutinee1, ptrn1, consequent1, alternative1); };
    this.DebrujinBranch.class = class DebrujinBranch {
      constructor(scrutinee, ptrn, consequent, alternative) {
        this.scrutinee = scrutinee;
        this.ptrn = ptrn;
        this.consequent = consequent;
        this.alternative = alternative;
      }
      toString() { return "DebrujinBranch(" + globalThis.Predef.render(this.scrutinee) + ", " + globalThis.Predef.render(this.ptrn) + ", " + globalThis.Predef.render(this.consequent) + ", " + globalThis.Predef.render(this.alternative) + ")"; }
    };
    this.Accept = function Accept(outcome1) { return new Accept.class(outcome1); };
    this.Accept.class = class Accept {
      constructor(outcome) {
        this.outcome = outcome;
      }
      toString() { return "Accept(" + globalThis.Predef.render(this.outcome) + ")"; }
    };
    this.Reject = class Reject {
      constructor() {}
      toString() { return "Reject"; }
    };
    this.Pattern = class Pattern {
      constructor() {}
      toString() { return "Pattern"; }
    };
    this.LitPattern = function LitPattern(lit1) { return new LitPattern.class(lit1); };
    this.LitPattern.class = class LitPattern {
      constructor(lit) {
        this.lit = lit;
      }
      toString() { return "LitPattern(" + globalThis.Predef.render(this.lit) + ")"; }
    };
    this.Var = function Var(sym1) { return new Var.class(sym1); };
    this.Var.class = class Var {
      constructor(sym) {
        this.sym = sym;
      }
      toString() { return "Var(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.ClassLike = function ClassLike(sym1, trm1, parameters1) { return new ClassLike.class(sym1, trm1, parameters1); };
    this.ClassLike.class = class ClassLike {
      constructor(sym, trm, parameters) {
        this.sym = sym;
        this.trm = trm;
        this.parameters = parameters;
      }
      toString() { return "ClassLike(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.trm) + ", " + globalThis.Predef.render(this.parameters) + ")"; }
    };
    this.Synonym = function Synonym(symbol1, patternArguments1) { return new Synonym.class(symbol1, patternArguments1); };
    this.Synonym.class = class Synonym {
      constructor(symbol, patternArguments) {
        this.symbol = symbol;
        this.patternArguments = patternArguments;
      }
      toString() { return "Synonym(" + globalThis.Predef.render(this.symbol) + ", " + globalThis.Predef.render(this.patternArguments) + ")"; }
    };
    this.Tuple = function Tuple(size1, inf1) { return new Tuple.class(size1, inf1); };
    this.Tuple.class = class Tuple {
      constructor(size, inf) {
        this.size = size;
        this.inf = inf;
      }
      toString() { return "Tuple(" + globalThis.Predef.render(this.size) + ", " + globalThis.Predef.render(this.inf) + ")"; }
    };
    this.Record = function Record(entities1) { return new Record.class(entities1); };
    this.Record.class = class Record {
      constructor(entities) {
        this.entities = entities;
      }
      toString() { return "Record(" + globalThis.Predef.render(this.entities) + ")"; }
    };
    this.Branch = function Branch(scrutinee1, ptrn1, continuation1) { return new Branch.class(scrutinee1, ptrn1, continuation1); };
    this.Branch.class = class Branch {
      constructor(scrutinee, ptrn, continuation) {
        this.scrutinee = scrutinee;
        this.ptrn = ptrn;
        this.continuation = continuation;
      }
      toString() { return "Branch(" + globalThis.Predef.render(this.scrutinee) + ", " + globalThis.Predef.render(this.ptrn) + ", " + globalThis.Predef.render(this.continuation) + ")"; }
    };
    this.Split = class Split {
      constructor() {}
      toString() { return "Split"; }
    };
    this.Cons = function Cons(head1, tail1) { return new Cons.class(head1, tail1); };
    this.Cons.class = class Cons {
      constructor(head, tail) {
        this.head = head;
        this.tail = tail;
      }
      toString() { return "Cons(" + globalThis.Predef.render(this.head) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.Let = function Let(sym1, term1, tail1) { return new Let.class(sym1, term1, tail1); };
    this.Let.class = class Let {
      constructor(sym, term, tail) {
        this.sym = sym;
        this.term = term;
        this.tail = tail;
      }
      toString() { return "Let(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.term) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.Else = function Else(default2) { return new Else.class(default2); };
    this.Else.class = class Else {
      constructor(default1) {
        this.default = default1;
      }
      toString() { return "Else(" + globalThis.Predef.render(this.default) + ")"; }
    };
    this.End = class End {
      constructor() {}
      toString() { return "End"; }
    };
    const KeywordIf$class = class KeywordIf {
      constructor() {}
      toString() { return "KeywordIf"; }
    };
    this.KeywordIf = new KeywordIf$class;
    this.KeywordIf.class = KeywordIf$class;
    const KeywordWhile$class = class KeywordWhile {
      constructor() {}
      toString() { return "KeywordWhile"; }
    };
    this.KeywordWhile = new KeywordWhile$class;
    this.KeywordWhile.class = KeywordWhile$class;
    this.Statement = class Statement {
      constructor() {}
      toString() { return "Statement"; }
    };
    this.LetDecl = function LetDecl(sym1) { return new LetDecl.class(sym1); };
    this.LetDecl.class = class LetDecl {
      constructor(sym) {
        this.sym = sym;
      }
      toString() { return "LetDecl(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.DefineVar = function DefineVar(sym1, rhs1) { return new DefineVar.class(sym1, rhs1); };
    this.DefineVar.class = class DefineVar {
      constructor(sym, rhs) {
        this.sym = sym;
        this.rhs = rhs;
      }
      toString() { return "DefineVar(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.rhs) + ")"; }
    };
    this.Term = class Term1 {
      constructor() {}
      toString() { return "Term"; }
    };
    this.Lit = function Lit(lit1) { return new Lit.class(lit1); };
    this.Lit.class = class Lit {
      constructor(lit) {
        this.lit = lit;
      }
      toString() { return "Lit(" + globalThis.Predef.render(this.lit) + ")"; }
    };
    this.Builtin = function Builtin(name1) { return new Builtin.class(name1); };
    this.Builtin.class = class Builtin {
      constructor(name) {
        this.name = name;
      }
      toString() { return "Builtin(" + globalThis.Predef.render(this.name) + ")"; }
    };
    this.Ref = function Ref(sym1) { return new Ref.class(sym1); };
    this.Ref.class = class Ref {
      constructor(sym) {
        this.sym = sym;
      }
      toString() { return "Ref(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.CSRef = function CSRef(sym1, base1, file1) { return new CSRef.class(sym1, base1, file1); };
    this.CSRef.class = class CSRef {
      constructor(sym, base, file) {
        this.sym = sym;
        this.base = base;
        this.file = file;
      }
      toString() { return "CSRef(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.base) + ", " + globalThis.Predef.render(this.file) + ")"; }
    };
    this.App = function App(lhs1, rhs1) { return new App.class(lhs1, rhs1); };
    this.App.class = class App {
      constructor(lhs, rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
      }
      toString() { return "App(" + globalThis.Predef.render(this.lhs) + ", " + globalThis.Predef.render(this.rhs) + ")"; }
    };
    this.Sel = function Sel(prefix1, nme1) { return new Sel.class(prefix1, nme1); };
    this.Sel.class = class Sel {
      constructor(prefix, nme) {
        this.prefix = prefix;
        this.nme = nme;
      }
      toString() { return "Sel(" + globalThis.Predef.render(this.prefix) + ", " + globalThis.Predef.render(this.nme) + ")"; }
    };
    this.DynSel = function DynSel(prefix1, fld1, arrayIdx1) { return new DynSel.class(prefix1, fld1, arrayIdx1); };
    this.DynSel.class = class DynSel {
      constructor(prefix, fld, arrayIdx) {
        this.prefix = prefix;
        this.fld = fld;
        this.arrayIdx = arrayIdx;
      }
      toString() { return "DynSel(" + globalThis.Predef.render(this.prefix) + ", " + globalThis.Predef.render(this.fld) + ", " + globalThis.Predef.render(this.arrayIdx) + ")"; }
    };
    this.Tup = function Tup(fields1) { return new Tup.class(fields1); };
    this.Tup.class = class Tup {
      constructor(fields) {
        this.fields = fields;
      }
      toString() { return "Tup(" + globalThis.Predef.render(this.fields) + ")"; }
    };
    this.IfLike = function IfLike(kw1, desugared1) { return new IfLike.class(kw1, desugared1); };
    this.IfLike.class = class IfLike {
      constructor(kw, desugared) {
        this.kw = kw;
        this.desugared = desugared;
      }
      toString() { return "IfLike(" + globalThis.Predef.render(this.kw) + ", " + globalThis.Predef.render(this.desugared) + ")"; }
    };
    this.Lam = function Lam(params1, body1) { return new Lam.class(params1, body1); };
    this.Lam.class = class Lam {
      constructor(params, body) {
        this.params = params;
        this.body = body;
      }
      toString() { return "Lam(" + globalThis.Predef.render(this.params) + ", " + globalThis.Predef.render(this.body) + ")"; }
    };
    this.Blk = function Blk(stats1, res1) { return new Blk.class(stats1, res1); };
    this.Blk.class = class Blk {
      constructor(stats, res) {
        this.stats = stats;
        this.res = res;
      }
      toString() { return "Blk(" + globalThis.Predef.render(this.stats) + ", " + globalThis.Predef.render(this.res) + ")"; }
    };
    this.New = function New(cls1, args1) { return new New.class(cls1, args1); };
    this.New.class = class New {
      constructor(cls, args) {
        this.cls = cls;
        this.args = args;
      }
      toString() { return "New(" + globalThis.Predef.render(this.cls) + ", " + globalThis.Predef.render(this.args) + ")"; }
    };
    this.Region = function Region(name1, body1) { return new Region.class(name1, body1); };
    this.Region.class = class Region {
      constructor(name, body) {
        this.name = name;
        this.body = body;
      }
      toString() { return "Region(" + globalThis.Predef.render(this.name) + ", " + globalThis.Predef.render(this.body) + ")"; }
    };
    this.RegRef = function RegRef(reg1, value1) { return new RegRef.class(reg1, value1); };
    this.RegRef.class = class RegRef {
      constructor(reg, value) {
        this.reg = reg;
        this.value = value;
      }
      toString() { return "RegRef(" + globalThis.Predef.render(this.reg) + ", " + globalThis.Predef.render(this.value) + ")"; }
    };
    this.Assgn = function Assgn(lhs1, rhs1) { return new Assgn.class(lhs1, rhs1); };
    this.Assgn.class = class Assgn {
      constructor(lhs, rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
      }
      toString() { return "Assgn(" + globalThis.Predef.render(this.lhs) + ", " + globalThis.Predef.render(this.rhs) + ")"; }
    };
    this.Deref = function Deref(ref1) { return new Deref.class(ref1); };
    this.Deref.class = class Deref {
      constructor(ref) {
        this.ref = ref;
      }
      toString() { return "Deref(" + globalThis.Predef.render(this.ref) + ")"; }
    };
    this.SetRef = function SetRef(ref1, value1) { return new SetRef.class(ref1, value1); };
    this.SetRef.class = class SetRef {
      constructor(ref, value) {
        this.ref = ref;
        this.value = value;
      }
      toString() { return "SetRef(" + globalThis.Predef.render(this.ref) + ", " + globalThis.Predef.render(this.value) + ")"; }
    };
    this.Ret = function Ret(result1) { return new Ret.class(result1); };
    this.Ret.class = class Ret {
      constructor(result) {
        this.result = result;
      }
      toString() { return "Ret(" + globalThis.Predef.render(this.result) + ")"; }
    };
    this.Throw = function Throw(result1) { return new Throw.class(result1); };
    this.Throw.class = class Throw {
      constructor(result) {
        this.result = result;
      }
      toString() { return "Throw(" + globalThis.Predef.render(this.result) + ")"; }
    };
    this.Try = function Try(body1, finallyDo1) { return new Try.class(body1, finallyDo1); };
    this.Try.class = class Try {
      constructor(body, finallyDo) {
        this.body = body;
        this.finallyDo = finallyDo;
      }
      toString() { return "Try(" + globalThis.Predef.render(this.body) + ", " + globalThis.Predef.render(this.finallyDo) + ")"; }
    };
    tmp = new globalThis.Set();
    this.#builtinSymbols = tmp;
    tmp1 = this.#builtinSymbols.add("+") ?? null;
    tmp2 = this.#builtinSymbols.add("-") ?? null;
    tmp3 = this.#builtinSymbols.add("*") ?? null;
    tmp4 = this.#builtinSymbols.add("/") ?? null;
    tmp5 = this.#builtinSymbols.add("==") ?? null;
    tmp6 = this.#builtinSymbols.add("<") ?? null;
    tmp7 = this.#builtinSymbols.add(">") ?? null;
    tmp8 = this.#builtinSymbols.add(">=") ?? null;
    tmp9 = this.#builtinSymbols.add("<=") ?? null;
    const this$Term = this;
    this.Context = function Context(symbols1, dependencies1, printOnly1) { return new Context.class(symbols1, dependencies1, printOnly1); };
    this.Context.class = class Context {
      constructor(symbols, dependencies, printOnly) {
        this.symbols = symbols;
        this.dependencies = dependencies;
        this.printOnly = printOnly;
      }
      isValid(name) {
        let tmp10, tmp11, tmp12;
        tmp10 = this.symbols.has(name) ?? null;
        tmp11 = this$Term.#builtinSymbols.has(name) ?? null;
        tmp12 = tmp10 || tmp11;
        return tmp12 || this.printOnly;
      } 
      get nest() {
        let tmp10;
        tmp10 = new globalThis.Set(this.symbols);
        return Term.Context(tmp10, this.dependencies, this.printOnly);
      } 
      add(name1) {
        return this.symbols.add(name1) ?? null;
      } 
      depends(d) {
        return this.dependencies.add(d) ?? null;
      }
      toString() { return "Context(" + globalThis.Predef.render(this.symbols) + ", " + globalThis.Predef.render(this.dependencies) + ", " + globalThis.Predef.render(this.printOnly) + ")"; }
    };
  }
  static showStmt(s, ctx, indent) {
    let res, param0, param1, param01, name, value, param02, param03, name1, tmp, tmp1, tmp2;
    if (s instanceof Term.LetDecl.class) {
      param02 = s.sym;
      if (param02 instanceof Term.Symbol.class) {
        param03 = param02.name;
        name1 = param03;
        tmp = ctx.add(name1) ?? null;
        tmp1 = Str.concat("let ", name1);
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      if (s instanceof Term.DefineVar.class) {
        param0 = s.sym;
        param1 = s.rhs;
        if (param0 instanceof Term.Symbol.class) {
          param01 = param0.name;
          name = param01;
          value = param1;
          tmp2 = Term.show(value, ctx, "");
          tmp1 = Str.concat(name, " = ", tmp2);
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
    res = tmp1;
    return Str.concat(indent, res);
  } 
  static showPattern(p, ctx1, indent1) {
    let res, param0, lit, tmp;
    if (p instanceof Term.LitPattern.class) {
      param0 = p.lit;
      lit = param0;
      tmp = lit.toString() ?? null;
    } else {
      throw new globalThis.Error("match error");
    }
    res = tmp;
    return Str.concat(indent1, res);
  } 
  static showSplit(s1, ctx2, indent2, isCont) {
    let res, param0, term, param01, param1, param2, sym, term1, split, nest, param02, param11, param03, param12, param21, scrut, ptrn, cont, tail, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (s1 instanceof Term.Cons.class) {
      param02 = s1.head;
      param11 = s1.tail;
      if (param02 instanceof Term.Branch.class) {
        param03 = param02.scrutinee;
        param12 = param02.ptrn;
        param21 = param02.continuation;
        scrut = param03;
        ptrn = param12;
        cont = param21;
        tail = param11;
        tmp = Term.show(scrut, ctx2, "");
        tmp1 = Term.showPattern(ptrn, ctx2, "");
        tmp2 = Term.showSplit(cont, ctx2, "", true);
        tmp3 = Term.showSplit(tail, ctx2, indent2, false);
        tmp4 = Str.concat(tmp, " is ", tmp1, " then ", tmp2, "\n", tmp3);
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      if (s1 instanceof Term.Let.class) {
        param01 = s1.sym;
        param1 = s1.term;
        param2 = s1.tail;
        sym = param01;
        term1 = param1;
        split = param2;
        nest = ctx2.nest;
        tmp5 = nest.add(sym.name) ?? null;
        tmp6 = Term.show(term1, nest, "");
        tmp7 = Term.showSplit(split, nest, indent2, false);
        tmp4 = Str.concat("let ", sym.name, " = ", tmp6, "\n", tmp7);
      } else {
        if (s1 instanceof Term.Else.class) {
          param0 = s1.default;
          term = param0;
          if (isCont === true) {
            tmp8 = Term.show(term, ctx2, "");
          } else {
            tmp9 = Term.show(term, ctx2, "");
            tmp8 = Str.concat("else ", tmp9);
          }
          tmp4 = tmp8;
        } else {
          if (s1 instanceof Term.End) {
            tmp4 = "";
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    }
    res = tmp4;
    return Str.concat(indent2, res);
  } 
  static show(t, ctx3, indent3) {
    let res, param0, param1, split, param01, param11, stats, res1, nest, param02, param12, params, body, nest1, param03, fields, param04, param13, lhs, rhs, param05, param14, prefix, name, param06, lit, param07, param15, param2, param08, name1, baseFile, file, param09, param010, name2, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
    if (t instanceof Term.Ref.class) {
      param09 = t.sym;
      if (param09 instanceof Term.Symbol.class) {
        param010 = param09.name;
        name2 = param010;
        scrut = ctx3.isValid(name2) ?? null;
        if (scrut === true) {
          tmp = name2;
        } else {
          tmp1 = Str.concat("Invalid binding name ", name2);
          throw new globalThis.Error(tmp1);
        }
        tmp2 = tmp;
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      if (t instanceof Term.CSRef.class) {
        param07 = t.sym;
        param15 = t.base;
        param2 = t.file;
        if (param07 instanceof Term.Symbol.class) {
          param08 = param07.name;
          name1 = param08;
          baseFile = param15;
          file = param2;
          if (file === undefined) {
            tmp3 = ctx3.depends(baseFile) ?? null;
          } else {
            tmp4 = path.dirname(baseFile) ?? null;
            tmp5 = path.join(tmp4, file);
            tmp3 = ctx3.depends(tmp5) ?? null;
          }
          tmp2 = name1;
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        if (t instanceof Term.Lit.class) {
          param06 = t.lit;
          lit = param06;
          tmp2 = lit.toString() ?? null;
        } else {
          if (t instanceof Term.Sel.class) {
            param05 = t.prefix;
            param14 = t.nme;
            prefix = param05;
            name = param14;
            tmp6 = Term.show(prefix, ctx3, "");
            tmp2 = Str.concat("(", tmp6, ").", name);
          } else {
            if (t instanceof Term.App.class) {
              param04 = t.lhs;
              param13 = t.rhs;
              lhs = param04;
              rhs = param13;
              tmp7 = Term.show(lhs, ctx3, "");
              tmp8 = Term.show(rhs, ctx3, "");
              tmp2 = Str.concat("(", tmp7, ")(", tmp8, ")");
            } else {
              if (t instanceof Term.Tup.class) {
                param03 = t.fields;
                fields = param03;
                tmp9 = Predef.join(", ");
                tmp10 = Predef.arraymap((t1) => {
                  return Term.show(t1, ctx3, "");
                });
                tmp11 = tmp10(fields) ?? null;
                tmp2 = tmp9(tmp11) ?? null;
              } else {
                if (t instanceof Term.Lam.class) {
                  param02 = t.params;
                  param12 = t.body;
                  params = param02;
                  body = param12;
                  nest1 = ctx3.nest;
                  tmp12 = Predef.arrayforeach((s2) => {
                    return nest1.add(s2.name) ?? null;
                  });
                  tmp13 = tmp12(params) ?? null;
                  tmp14 = Predef.join(", ");
                  tmp15 = Predef.arraymap((s2) => {
                    return s2.name;
                  });
                  tmp16 = tmp15(params) ?? null;
                  tmp17 = tmp14(tmp16) ?? null;
                  tmp18 = Term.show(body, nest1, "");
                  tmp2 = Str.concat("(", tmp17, ") => ", tmp18);
                } else {
                  if (t instanceof Term.Blk.class) {
                    param01 = t.stats;
                    param11 = t.res;
                    stats = param01;
                    res1 = param11;
                    nest = ctx3.nest;
                    tmp19 = Predef.join("\n");
                    tmp20 = Predef.arraymap((s2) => {
                      return Term.showStmt(s2, nest, "");
                    });
                    tmp21 = tmp20(stats) ?? null;
                    tmp22 = tmp19(tmp21) ?? null;
                    tmp23 = Term.show(res1, nest, "");
                    tmp2 = Str.concat(tmp22, "\n", tmp23);
                  } else {
                    if (t instanceof Term.IfLike.class) {
                      param0 = t.kw;
                      param1 = t.desugared;
                      if (param0 instanceof Term.KeywordIf.class) {
                        split = param1;
                        tmp24 = Str.concat(indent3, "  ");
                        tmp25 = Term.showSplit(split, ctx3, tmp24, false);
                        tmp2 = Str.concat("if \n", tmp25);
                      } else {
                        throw new globalThis.Error("match error");
                      }
                    } else {
                      throw new globalThis.Error("match error");
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    res = tmp2;
    return Str.concat(indent3, res);
  } 
  static print(t1) {
    let ctx4, tmp, tmp1, tmp2, tmp3;
    tmp = new globalThis.Set();
    tmp1 = new globalThis.Set();
    tmp2 = Term.Context(tmp, tmp1, true);
    ctx4 = tmp2;
    tmp3 = Term.show(t1, ctx4, "");
    return globalThis.log(tmp3) ?? null;
  } 
  static genImport(base, p1) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = url.fileURLToPath(p1) ?? null;
    tmp1 = path.relative(base, tmp);
    tmp2 = - 4;
    tmp3 = tmp1.slice(0, tmp2);
    return Str.concat("import \"", tmp3, ".mls\"");
  } 
  static codegen(t2, file) {
    let ctx4, moduleName, fullpath, code, dependencies, fp, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
    tmp = new globalThis.Set();
    tmp1 = new globalThis.Set();
    tmp2 = Term.Context(tmp, tmp1, false);
    ctx4 = tmp2;
    tmp3 = path.parse(file) ?? null;
    moduleName = tmp3.name;
    tmp4 = process.cwd() ?? null;
    tmp5 = path.join(tmp4, file);
    fullpath = tmp5;
    tmp6 = Term.show(t2, ctx4, "");
    tmp7 = Str.concat("module ", moduleName, " with ...\nfun res = ", tmp6);
    code = tmp7;
    tmp8 = Predef.arraymap((s2) => {
      let tmp16;
      tmp16 = path.dirname(fullpath) ?? null;
      return Term.genImport(tmp16, s2);
    });
    tmp9 = globalThis.Array.from(ctx4.dependencies) ?? null;
    tmp10 = tmp8(tmp9) ?? null;
    dependencies = tmp10;
    tmp11 = fs.openSync(file, "w");
    fp = tmp11;
    tmp12 = Predef.join("\n");
    tmp13 = tmp12(dependencies) ?? null;
    tmp14 = Str.concat(tmp13, "\n", code);
    tmp15 = fs.writeSync(fp, tmp14);
    return fs.closeSync(fp) ?? null;
  }
  static toString() { return "Term"; }
};
null
let Term = Term2; export default Term;
