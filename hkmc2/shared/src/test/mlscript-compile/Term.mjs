let Term2;
Term2 = class Term {
  static {
    this.Symbol = function Symbol(name1) { return new Symbol.class(name1); };
    this.Symbol.class = class Symbol {
      constructor(name) {
        this.name = name;
      }
      toString() { return "Symbol(" + globalThis.Predef.render(this.name) + ")"; }
    };
    this.Literal = function Literal(value1) { return new Literal.class(value1); };
    this.Literal.class = class Literal {
      constructor(value) {
        this.value = value;
      }
      toString() { return "Literal(" + globalThis.Predef.render(this.value) + ")"; }
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
  }
  static toString() { return "Term"; }
};
null
let Term = Term2; export default Term;
