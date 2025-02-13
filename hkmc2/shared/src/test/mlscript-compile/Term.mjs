import runtime from "./Runtime.mjs";
import fs from "fs";
import process from "process";
import path from "path";
import url from "url";
import Predef from "./Predef.mjs";
import Str from "./Str.mjs";
let Term2;
Term2 = class Term {
  static #names;
  static {
    let tmp;
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
    this.SymbolCons.class = class SymbolCons extends Term.ConstructorLike {
      constructor(symbol) {
        super();
        this.symbol = symbol;
      }
      toString() { return "SymbolCons(" + globalThis.Predef.render(this.symbol) + ")"; }
    };
    this.StringJoin = class StringJoin extends Term.ConstructorLike {
      constructor() {
        super();
      }
      toString() { return "StringJoin"; }
    };
    this.TupleCapacity = function TupleCapacity(size1, inf1) { return new TupleCapacity.class(size1, inf1); };
    this.TupleCapacity.class = class TupleCapacity extends Term.ConstructorLike {
      constructor(size, inf) {
        super();
        this.size = size;
        this.inf = inf;
      }
      toString() { return "TupleCapacity(" + globalThis.Predef.render(this.size) + ", " + globalThis.Predef.render(this.inf) + ")"; }
    };
    this.Instantiation = function Instantiation(symbol1, args1) { return new Instantiation.class(symbol1, args1); };
    this.Instantiation.class = class Instantiation extends Term.ConstructorLike {
      constructor(symbol, args) {
        super();
        this.symbol = symbol;
        this.args = args;
      }
      toString() { return "Instantiation(" + globalThis.Predef.render(this.symbol) + ", " + globalThis.Predef.render(this.args) + ")"; }
    };
    this.LocalPattern = function LocalPattern(id1) { return new LocalPattern.class(id1); };
    this.LocalPattern.class = class LocalPattern extends Term.ConstructorLike {
      constructor(id) {
        super();
        this.id = id;
      }
      toString() { return "LocalPattern(" + globalThis.Predef.render(this.id) + ")"; }
    };
    this.Parameter = function Parameter(symbol1) { return new Parameter.class(symbol1); };
    this.Parameter.class = class Parameter extends Term.ConstructorLike {
      constructor(symbol) {
        super();
        this.symbol = symbol;
      }
      toString() { return "Parameter(" + globalThis.Predef.render(this.symbol) + ")"; }
    };
    this.Nested = function Nested(split1) { return new Nested.class(split1); };
    this.Nested.class = class Nested extends Term.ConstructorLike {
      constructor(split) {
        super();
        this.split = split;
      }
      toString() { return "Nested(" + globalThis.Predef.render(this.split) + ")"; }
    };
    this.PatternStub = class PatternStub {
      constructor() {}
      toString() { return "PatternStub"; }
    };
    this.LiteralStub = function LiteralStub(value1) { return new LiteralStub.class(value1); };
    this.LiteralStub.class = class LiteralStub extends Term.PatternStub {
      constructor(value) {
        super();
        this.value = value;
      }
      toString() { return "LiteralStub(" + globalThis.Predef.render(this.value) + ")"; }
    };
    this.CharClass = function CharClass(start1, end1, inclusive1) { return new CharClass.class(start1, end1, inclusive1); };
    this.CharClass.class = class CharClass extends Term.PatternStub {
      constructor(start, end, inclusive) {
        super();
        this.start = start;
        this.end = end;
        this.inclusive = inclusive;
      }
      toString() { return "CharClass(" + globalThis.Predef.render(this.start) + ", " + globalThis.Predef.render(this.end) + ", " + globalThis.Predef.render(this.inclusive) + ")"; }
    };
    this.ClassLikeStub = function ClassLikeStub(cons1) { return new ClassLikeStub.class(cons1); };
    this.ClassLikeStub.class = class ClassLikeStub extends Term.PatternStub {
      constructor(cons) {
        super();
        this.cons = cons;
      }
      toString() { return "ClassLikeStub(" + globalThis.Predef.render(this.cons) + ")"; }
    };
    this.Wildcard = class Wildcard extends Term.PatternStub {
      constructor() {
        super();
      }
      toString() { return "Wildcard"; }
    };
    this.DebrujinSplit = class DebrujinSplit {
      constructor() {}
      toString() { return "DebrujinSplit"; }
    };
    this.Binder = function Binder(body1) { return new Binder.class(body1); };
    this.Binder.class = class Binder extends Term.DebrujinSplit {
      constructor(body) {
        super();
        this.body = body;
      }
      toString() { return "Binder(" + globalThis.Predef.render(this.body) + ")"; }
    };
    this.DebrujinBranch = function DebrujinBranch(scrutinee1, ptrn1, consequent1, alternative1) { return new DebrujinBranch.class(scrutinee1, ptrn1, consequent1, alternative1); };
    this.DebrujinBranch.class = class DebrujinBranch extends Term.DebrujinSplit {
      constructor(scrutinee, ptrn, consequent, alternative) {
        super();
        this.scrutinee = scrutinee;
        this.ptrn = ptrn;
        this.consequent = consequent;
        this.alternative = alternative;
      }
      toString() { return "DebrujinBranch(" + globalThis.Predef.render(this.scrutinee) + ", " + globalThis.Predef.render(this.ptrn) + ", " + globalThis.Predef.render(this.consequent) + ", " + globalThis.Predef.render(this.alternative) + ")"; }
    };
    this.Accept = function Accept(outcome1) { return new Accept.class(outcome1); };
    this.Accept.class = class Accept extends Term.DebrujinSplit {
      constructor(outcome) {
        super();
        this.outcome = outcome;
      }
      toString() { return "Accept(" + globalThis.Predef.render(this.outcome) + ")"; }
    };
    this.Reject = class Reject extends Term.DebrujinSplit {
      constructor() {
        super();
      }
      toString() { return "Reject"; }
    };
    this.Pattern = class Pattern {
      constructor() {}
      toString() { return "Pattern"; }
    };
    this.LitPattern = function LitPattern(lit1) { return new LitPattern.class(lit1); };
    this.LitPattern.class = class LitPattern extends Term.Pattern {
      constructor(lit) {
        super();
        this.lit = lit;
      }
      toString() { return "LitPattern(" + globalThis.Predef.render(this.lit) + ")"; }
    };
    this.Var = function Var(sym1) { return new Var.class(sym1); };
    this.Var.class = class Var extends Term.Pattern {
      constructor(sym) {
        super();
        this.sym = sym;
      }
      toString() { return "Var(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.ClassLike = function ClassLike(sym1, trm1, parameters1) { return new ClassLike.class(sym1, trm1, parameters1); };
    this.ClassLike.class = class ClassLike extends Term.Pattern {
      constructor(sym, trm, parameters) {
        super();
        this.sym = sym;
        this.trm = trm;
        this.parameters = parameters;
      }
      toString() { return "ClassLike(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.trm) + ", " + globalThis.Predef.render(this.parameters) + ")"; }
    };
    this.Synonym = function Synonym(symbol1, patternArguments1) { return new Synonym.class(symbol1, patternArguments1); };
    this.Synonym.class = class Synonym extends Term.Pattern {
      constructor(symbol, patternArguments) {
        super();
        this.symbol = symbol;
        this.patternArguments = patternArguments;
      }
      toString() { return "Synonym(" + globalThis.Predef.render(this.symbol) + ", " + globalThis.Predef.render(this.patternArguments) + ")"; }
    };
    this.Tuple = function Tuple(size1, inf1) { return new Tuple.class(size1, inf1); };
    this.Tuple.class = class Tuple extends Term.Pattern {
      constructor(size, inf) {
        super();
        this.size = size;
        this.inf = inf;
      }
      toString() { return "Tuple(" + globalThis.Predef.render(this.size) + ", " + globalThis.Predef.render(this.inf) + ")"; }
    };
    this.Record = function Record(entities1) { return new Record.class(entities1); };
    this.Record.class = class Record extends Term.Pattern {
      constructor(entities) {
        super();
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
    this.Cons.class = class Cons extends Term.Split {
      constructor(head, tail) {
        super();
        this.head = head;
        this.tail = tail;
      }
      toString() { return "Cons(" + globalThis.Predef.render(this.head) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.Let = function Let(sym1, term1, tail1) { return new Let.class(sym1, term1, tail1); };
    this.Let.class = class Let extends Term.Split {
      constructor(sym, term, tail) {
        super();
        this.sym = sym;
        this.term = term;
        this.tail = tail;
      }
      toString() { return "Let(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.term) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.Else = function Else(default2) { return new Else.class(default2); };
    this.Else.class = class Else extends Term.Split {
      constructor(default1) {
        super();
        this.default = default1;
      }
      toString() { return "Else(" + globalThis.Predef.render(this.default) + ")"; }
    };
    this.End = class End extends Term.Split {
      constructor() {
        super();
      }
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
    this.LetDecl.class = class LetDecl extends Term.Statement {
      constructor(sym) {
        super();
        this.sym = sym;
      }
      toString() { return "LetDecl(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.DefineVar = function DefineVar(sym1, rhs1) { return new DefineVar.class(sym1, rhs1); };
    this.DefineVar.class = class DefineVar extends Term.Statement {
      constructor(sym, rhs) {
        super();
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
    this.Lit.class = class Lit extends Term.Term {
      constructor(lit) {
        super();
        this.lit = lit;
      }
      toString() { return "Lit(" + globalThis.Predef.render(this.lit) + ")"; }
    };
    this.Builtin = function Builtin(name1) { return new Builtin.class(name1); };
    this.Builtin.class = class Builtin extends Term.Term {
      constructor(name) {
        super();
        this.name = name;
      }
      toString() { return "Builtin(" + globalThis.Predef.render(this.name) + ")"; }
    };
    this.Ref = function Ref(sym1) { return new Ref.class(sym1); };
    this.Ref.class = class Ref extends Term.Term {
      constructor(sym) {
        super();
        this.sym = sym;
      }
      toString() { return "Ref(" + globalThis.Predef.render(this.sym) + ")"; }
    };
    this.CSRef = function CSRef(sym1, base1, file1) { return new CSRef.class(sym1, base1, file1); };
    this.CSRef.class = class CSRef extends Term.Term {
      constructor(sym, base, file) {
        super();
        this.sym = sym;
        this.base = base;
        this.file = file;
      }
      toString() { return "CSRef(" + globalThis.Predef.render(this.sym) + ", " + globalThis.Predef.render(this.base) + ", " + globalThis.Predef.render(this.file) + ")"; }
    };
    this.App = function App(lhs1, rhs1) { return new App.class(lhs1, rhs1); };
    this.App.class = class App extends Term.Term {
      constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
      }
      toString() { return "App(" + globalThis.Predef.render(this.lhs) + ", " + globalThis.Predef.render(this.rhs) + ")"; }
    };
    this.Sel = function Sel(prefix1, nme1) { return new Sel.class(prefix1, nme1); };
    this.Sel.class = class Sel extends Term.Term {
      constructor(prefix, nme) {
        super();
        this.prefix = prefix;
        this.nme = nme;
      }
      toString() { return "Sel(" + globalThis.Predef.render(this.prefix) + ", " + globalThis.Predef.render(this.nme) + ")"; }
    };
    this.DynSel = function DynSel(prefix1, fld1, arrayIdx1) { return new DynSel.class(prefix1, fld1, arrayIdx1); };
    this.DynSel.class = class DynSel extends Term.Term {
      constructor(prefix, fld, arrayIdx) {
        super();
        this.prefix = prefix;
        this.fld = fld;
        this.arrayIdx = arrayIdx;
      }
      toString() { return "DynSel(" + globalThis.Predef.render(this.prefix) + ", " + globalThis.Predef.render(this.fld) + ", " + globalThis.Predef.render(this.arrayIdx) + ")"; }
    };
    this.Tup = function Tup(fields1) { return new Tup.class(fields1); };
    this.Tup.class = class Tup extends Term.Term {
      constructor(fields) {
        super();
        this.fields = fields;
      }
      toString() { return "Tup(" + globalThis.Predef.render(this.fields) + ")"; }
    };
    this.IfLike = function IfLike(kw1, desugared1) { return new IfLike.class(kw1, desugared1); };
    this.IfLike.class = class IfLike extends Term.Term {
      constructor(kw, desugared) {
        super();
        this.kw = kw;
        this.desugared = desugared;
      }
      toString() { return "IfLike(" + globalThis.Predef.render(this.kw) + ", " + globalThis.Predef.render(this.desugared) + ")"; }
    };
    this.Lam = function Lam(params1, body1) { return new Lam.class(params1, body1); };
    this.Lam.class = class Lam extends Term.Term {
      constructor(params, body) {
        super();
        this.params = params;
        this.body = body;
      }
      toString() { return "Lam(" + globalThis.Predef.render(this.params) + ", " + globalThis.Predef.render(this.body) + ")"; }
    };
    this.Blk = function Blk(stats1, res1) { return new Blk.class(stats1, res1); };
    this.Blk.class = class Blk extends Term.Term {
      constructor(stats, res) {
        super();
        this.stats = stats;
        this.res = res;
      }
      toString() { return "Blk(" + globalThis.Predef.render(this.stats) + ", " + globalThis.Predef.render(this.res) + ")"; }
    };
    this.New = function New(cls1, args1) { return new New.class(cls1, args1); };
    this.New.class = class New extends Term.Term {
      constructor(cls, args) {
        super();
        this.cls = cls;
        this.args = args;
      }
      toString() { return "New(" + globalThis.Predef.render(this.cls) + ", " + globalThis.Predef.render(this.args) + ")"; }
    };
    this.Region = function Region(name1, body1) { return new Region.class(name1, body1); };
    this.Region.class = class Region extends Term.Term {
      constructor(name, body) {
        super();
        this.name = name;
        this.body = body;
      }
      toString() { return "Region(" + globalThis.Predef.render(this.name) + ", " + globalThis.Predef.render(this.body) + ")"; }
    };
    this.RegRef = function RegRef(reg1, value1) { return new RegRef.class(reg1, value1); };
    this.RegRef.class = class RegRef extends Term.Term {
      constructor(reg, value) {
        super();
        this.reg = reg;
        this.value = value;
      }
      toString() { return "RegRef(" + globalThis.Predef.render(this.reg) + ", " + globalThis.Predef.render(this.value) + ")"; }
    };
    this.Assgn = function Assgn(lhs1, rhs1) { return new Assgn.class(lhs1, rhs1); };
    this.Assgn.class = class Assgn extends Term.Term {
      constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
      }
      toString() { return "Assgn(" + globalThis.Predef.render(this.lhs) + ", " + globalThis.Predef.render(this.rhs) + ")"; }
    };
    this.Deref = function Deref(ref1) { return new Deref.class(ref1); };
    this.Deref.class = class Deref extends Term.Term {
      constructor(ref) {
        super();
        this.ref = ref;
      }
      toString() { return "Deref(" + globalThis.Predef.render(this.ref) + ")"; }
    };
    this.SetRef = function SetRef(ref1, value1) { return new SetRef.class(ref1, value1); };
    this.SetRef.class = class SetRef extends Term.Term {
      constructor(ref, value) {
        super();
        this.ref = ref;
        this.value = value;
      }
      toString() { return "SetRef(" + globalThis.Predef.render(this.ref) + ", " + globalThis.Predef.render(this.value) + ")"; }
    };
    this.Ret = function Ret(result1) { return new Ret.class(result1); };
    this.Ret.class = class Ret extends Term.Term {
      constructor(result) {
        super();
        this.result = result;
      }
      toString() { return "Ret(" + globalThis.Predef.render(this.result) + ")"; }
    };
    this.Throw = function Throw(result1) { return new Throw.class(result1); };
    this.Throw.class = class Throw extends Term.Term {
      constructor(result) {
        super();
        this.result = result;
      }
      toString() { return "Throw(" + globalThis.Predef.render(this.result) + ")"; }
    };
    this.Try = function Try(body1, finallyDo1) { return new Try.class(body1, finallyDo1); };
    this.Try.class = class Try extends Term.Term {
      constructor(body, finallyDo) {
        super();
        this.body = body;
        this.finallyDo = finallyDo;
      }
      toString() { return "Try(" + globalThis.Predef.render(this.body) + ", " + globalThis.Predef.render(this.finallyDo) + ")"; }
    };
    tmp = new globalThis.Map();
    Term.#names = tmp;
    this.Context = function Context(symbols1, dependencies1, printOnly1) { return new Context.class(symbols1, dependencies1, printOnly1); };
    this.Context.class = class Context {
      constructor(symbols, dependencies, printOnly) {
        this.symbols = symbols;
        this.dependencies = dependencies;
        this.printOnly = printOnly;
      }
      isValid(name) {
        let tmp1;
        tmp1 = runtime.safeCall(this.symbols.has(name));
        return tmp1 || this.printOnly
      } 
      get nest() {
        let tmp1;
        tmp1 = new globalThis.Set(this.symbols);
        return Term.Context(tmp1, this.dependencies, this.printOnly);
      } 
      add(name1) {
        return runtime.safeCall(this.symbols.add(name1))
      } 
      depends(d) {
        return runtime.safeCall(this.dependencies.add(d))
      }
      toString() { return "Context(" + globalThis.Predef.render(this.symbols) + ", " + globalThis.Predef.render(this.dependencies) + ", " + globalThis.Predef.render(this.printOnly) + ")"; }
    };
  }
  static freshName(name) {
    let scrut, i, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.safeCall(Term.#names.has(name));
    scrut = Predef.not(tmp);
    if (scrut === true) {
      tmp1 = Term.#names.set(name, 0);
    } else {
      tmp1 = runtime.Unit;
    }
    tmp2 = runtime.safeCall(Term.#names.get(name));
    i = tmp2;
    tmp3 = i + 1;
    tmp4 = Term.#names.set(name, tmp3);
    tmp5 = runtime.safeCall(i.toString());
    return Str.concat(name, "_", tmp5)
  } 
  static indent(str, ind, keepLeading) {
    let res, tmp, tmp1, tmp2;
    tmp = runtime.safeCall(str.split("\n"));
    tmp1 = runtime.safeCall(tmp.map((s) => {
      return Str.concat(ind, s)
    }));
    tmp2 = runtime.safeCall(tmp1.join("\n"));
    res = tmp2;
    if (keepLeading === true) {
      return res
    } else {
      return runtime.safeCall(res.substring(ind.length))
    }
  } 
  static showStmt(s, ctx) {
    let param0, param1, param01, name1, value, param02, param03, name2, tmp, tmp1;
    if (s instanceof Term.LetDecl.class) {
      param02 = s.sym;
      if (param02 instanceof Term.Symbol.class) {
        param03 = param02.name;
        name2 = param03;
        tmp = runtime.safeCall(ctx.add(name2));
        return Str.concat("let ", name2)
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (s instanceof Term.DefineVar.class) {
      param0 = s.sym;
      param1 = s.rhs;
      if (param0 instanceof Term.Symbol.class) {
        param01 = param0.name;
        name1 = param01;
        value = param1;
        tmp1 = Term.show(value, ctx);
        return Str.concat(name1, " = ", tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showPattern(p, ctx1) {
    let param0, lit;
    if (p instanceof Term.LitPattern.class) {
      param0 = p.lit;
      lit = param0;
      return runtime.safeCall(lit.toString())
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showSplit(s1, ctx2, isCont) {
    let param0, term, param01, param1, param2, sym, term1, split, nest, param02, param11, param03, param12, param21, scrut, ptrn, cont, tail, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
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
        tmp = Term.show(scrut, ctx2);
        tmp1 = Term.showPattern(ptrn, ctx2);
        tmp2 = Term.showSplit(cont, ctx2, true);
        tmp3 = Term.showSplit(tail, ctx2, false);
        return Str.concat(tmp, " is ", tmp1, " then ", tmp2, "\n", tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (s1 instanceof Term.Let.class) {
      param01 = s1.sym;
      param1 = s1.term;
      param2 = s1.tail;
      sym = param01;
      term1 = param1;
      split = param2;
      nest = ctx2.nest;
      tmp4 = runtime.safeCall(nest.add(sym.name));
      tmp5 = Term.show(term1, nest);
      tmp6 = Term.showSplit(split, nest, false);
      return Str.concat("let ", sym.name, " = ", tmp5, "\n", tmp6)
    } else if (s1 instanceof Term.Else.class) {
      param0 = s1.default;
      term = param0;
      if (isCont === true) {
        return Term.show(term, ctx2)
      } else {
        tmp7 = Term.show(term, ctx2);
        return Str.concat("else ", tmp7)
      }
    } else if (s1 instanceof Term.End) {
      return ""
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static show(t, ctx3) {
    let param0, param1, split, param01, param11, stats, res, nest, param02, param12, params, body, nest1, param03, fields, param04, param13, lhs, rhs, param05, param14, prefix, name1, param06, name2, param07, lit, param08, param15, param2, param09, name3, baseFile, file, param010, param011, name4, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    if (t instanceof Term.Ref.class) {
      param010 = t.sym;
      if (param010 instanceof Term.Symbol.class) {
        param011 = param010.name;
        name4 = param011;
        scrut = runtime.safeCall(ctx3.isValid(name4));
        if (scrut === true) {
          return name4
        } else {
          tmp = Str.concat("Invalid binding name ", name4);
          throw globalThis.Error(tmp);
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (t instanceof Term.CSRef.class) {
      param08 = t.sym;
      param15 = t.base;
      param2 = t.file;
      if (param08 instanceof Term.Symbol.class) {
        param09 = param08.name;
        name3 = param09;
        baseFile = param15;
        file = param2;
        if (file === undefined) {
          tmp1 = runtime.safeCall(ctx3.depends(baseFile));
        } else {
          tmp2 = runtime.safeCall(path.dirname(baseFile));
          tmp3 = path.join(tmp2, file);
          tmp1 = runtime.safeCall(ctx3.depends(tmp3));
        }
        return name3
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (t instanceof Term.Lit.class) {
      param07 = t.lit;
      lit = param07;
      return runtime.safeCall(lit.toString())
    } else if (t instanceof Term.Builtin.class) {
      param06 = t.name;
      name2 = param06;
      return name2
    } else if (t instanceof Term.Sel.class) {
      param05 = t.prefix;
      param14 = t.nme;
      prefix = param05;
      name1 = param14;
      tmp4 = Term.show(prefix, ctx3);
      return Str.concat("(", tmp4, ").", name1)
    } else if (t instanceof Term.App.class) {
      param04 = t.lhs;
      param13 = t.rhs;
      lhs = param04;
      rhs = param13;
      tmp5 = Term.show(lhs, ctx3);
      tmp6 = Term.show(rhs, ctx3);
      return Str.concat("(", tmp5, ")(", tmp6, ")")
    } else if (t instanceof Term.Tup.class) {
      param03 = t.fields;
      fields = param03;
      tmp7 = runtime.safeCall(fields.map((t1) => {
        return Term.show(t1, ctx3)
      }));
      return runtime.safeCall(tmp7.join(", "))
    } else if (t instanceof Term.Lam.class) {
      param02 = t.params;
      param12 = t.body;
      params = param02;
      body = param12;
      nest1 = ctx3.nest;
      tmp8 = runtime.safeCall(params.forEach((s2) => {
        return runtime.safeCall(nest1.add(s2.name))
      }));
      tmp9 = runtime.safeCall(params.map((s2) => {
        return s2.name
      }));
      tmp10 = runtime.safeCall(tmp9.join(", "));
      tmp11 = Term.show(body, nest1);
      tmp12 = Term.indent(tmp11, "  ", true);
      return Str.concat("(", tmp10, ") =>\n", tmp12)
    } else if (t instanceof Term.Blk.class) {
      param01 = t.stats;
      param11 = t.res;
      stats = param01;
      res = param11;
      nest = ctx3.nest;
      tmp13 = runtime.safeCall(stats.map((s2) => {
        return Term.showStmt(s2, nest)
      }));
      tmp14 = runtime.safeCall(tmp13.join("\n"));
      tmp15 = Term.show(res, nest);
      return Str.concat(tmp14, "\n", tmp15)
    } else if (t instanceof Term.IfLike.class) {
      param0 = t.kw;
      param1 = t.desugared;
      if (param0 instanceof Term.KeywordIf.class) {
        split = param1;
        tmp16 = Term.showSplit(split, ctx3, false);
        tmp17 = Term.indent(tmp16, "  ", true);
        return Str.concat("if \n", tmp17)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static print(t1) {
    let ctx4, tmp, tmp1, tmp2, tmp3;
    tmp = new globalThis.Set();
    tmp1 = new globalThis.Set();
    tmp2 = Term.Context(tmp, tmp1, true);
    ctx4 = tmp2;
    tmp3 = Term.show(t1, ctx4);
    return runtime.safeCall(globalThis.console.log(tmp3))
  } 
  static genImport(base, p1) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = runtime.safeCall(url.fileURLToPath(p1));
    tmp1 = path.relative(base, tmp);
    tmp2 = - 4;
    tmp3 = tmp1.slice(0, tmp2);
    return Str.concat("import \"", tmp3, ".mls\"")
  } 
  static codegen(t2, file) {
    let ctx4, moduleName, fullpath, code, dependencies, scrut, originData, newData, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
    tmp = new globalThis.Set();
    tmp1 = new globalThis.Set();
    tmp2 = Term.Context(tmp, tmp1, false);
    ctx4 = tmp2;
    tmp3 = runtime.safeCall(path.parse(file));
    moduleName = tmp3.name;
    tmp4 = runtime.safeCall(process.cwd());
    tmp5 = path.join(tmp4, file);
    fullpath = tmp5;
    tmp6 = Term.show(t2, ctx4);
    tmp7 = Term.indent(tmp6, "  ", true);
    tmp8 = Str.concat("module ", moduleName, " with ...\nfun res =\n", tmp7, "\n");
    code = tmp8;
    tmp9 = runtime.safeCall(globalThis.Array.from(ctx4.dependencies));
    tmp10 = runtime.safeCall(tmp9.map((s2) => {
      let tmp16;
      tmp16 = runtime.safeCall(path.dirname(fullpath));
      return Term.genImport(tmp16, s2)
    }));
    dependencies = tmp10;
    tmp11 = runtime.safeCall(fs.existsSync(file));
    scrut = Predef.not(tmp11);
    if (scrut === true) {
      tmp12 = runtime.safeCall(fs.writeFileSync(file, "", "utf8"));
    } else {
      tmp12 = runtime.Unit;
    }
    tmp13 = fs.readFileSync(file, "utf8");
    originData = tmp13;
    tmp14 = runtime.safeCall(dependencies.join("\n"));
    tmp15 = Str.concat(tmp14, "\n", code);
    newData = tmp15;
    scrut1 = newData != originData;
    if (scrut1 === true) {
      return runtime.safeCall(fs.writeFileSync(file, newData, "utf8"))
    } else {
      return runtime.Unit
    }
  }
  static toString() { return "Term"; }
};
let Term = Term2; export default Term;
