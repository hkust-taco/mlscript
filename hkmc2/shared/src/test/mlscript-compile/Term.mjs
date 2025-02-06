import Predef from "./Predef.mjs";
import Str from "./Str.mjs";
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
  static showStmt(s, indent) {
    let res, param0, param1, param01, name, value, param02, param03, name1, tmp, tmp1;
    if (s instanceof Term.LetDecl.class) {
      param02 = s.sym;
      if (param02 instanceof Term.Symbol.class) {
        param03 = param02.name;
        name1 = param03;
        tmp = Str.concat("let ", name1);
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
          tmp1 = Term.show(value, "");
          tmp = Str.concat(name, " = ", tmp1);
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
    res = tmp;
    return Str.concat(indent, res);
  } 
  static showPattern(p, indent1) {
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
  static showSplit(s1, indent2, isCont) {
    let res, param0, term, param01, param1, param2, sym, term1, split, param02, param11, param03, param12, param21, scrut, ptrn, cont, tail, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
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
        tmp = Term.show(scrut, "");
        tmp1 = Term.showPattern(ptrn, "");
        tmp2 = Term.showSplit(cont, "", true);
        tmp3 = Term.showSplit(tail, indent2, false);
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
        tmp5 = Term.show(term1, "");
        tmp6 = Term.showSplit(split, indent2, false);
        tmp4 = Str.concat("let ", sym.name, " = ", tmp5, "\n", tmp6);
      } else {
        if (s1 instanceof Term.Else.class) {
          param0 = s1.default;
          term = param0;
          if (isCont === true) {
            tmp7 = Term.show(term, "");
          } else {
            tmp8 = Term.show(term, "");
            tmp7 = Str.concat("else ", tmp8);
          }
          tmp4 = tmp7;
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
  static show(t, indent3) {
    let res, param0, param1, split, param01, param11, stats, res1, param02, param12, params, body, param03, fields, param04, param13, lhs, rhs, param05, lit, param06, param07, name, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    if (t instanceof Term.Ref.class) {
      param06 = t.sym;
      if (param06 instanceof Term.Symbol.class) {
        param07 = param06.name;
        name = param07;
        tmp = name;
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      if (t instanceof Term.Lit.class) {
        param05 = t.lit;
        lit = param05;
        tmp = lit.toString() ?? null;
      } else {
        if (t instanceof Term.App.class) {
          param04 = t.lhs;
          param13 = t.rhs;
          lhs = param04;
          rhs = param13;
          tmp1 = Term.show(lhs, "");
          tmp2 = Term.show(rhs, "");
          tmp = Str.concat("(", tmp1, ")(", tmp2, ")");
        } else {
          if (t instanceof Term.Tup.class) {
            param03 = t.fields;
            fields = param03;
            tmp3 = Predef.join(", ");
            tmp4 = Predef.arraymap((t1) => {
              return Term.show(t1, "");
            });
            tmp5 = tmp4(fields) ?? null;
            tmp = tmp3(tmp5) ?? null;
          } else {
            if (t instanceof Term.Lam.class) {
              param02 = t.params;
              param12 = t.body;
              params = param02;
              body = param12;
              tmp6 = Predef.join(", ");
              tmp7 = Predef.arraymap((s2) => {
                return s2.name;
              });
              tmp8 = tmp7(params) ?? null;
              tmp9 = tmp6(tmp8) ?? null;
              tmp10 = Term.show(body, "");
              tmp = Str.concat("(", tmp9, ") => ", tmp10);
            } else {
              if (t instanceof Term.Blk.class) {
                param01 = t.stats;
                param11 = t.res;
                stats = param01;
                res1 = param11;
                tmp11 = Predef.join("\n");
                tmp12 = Predef.arraymap((s2) => {
                  return Term.showStmt(s2, "");
                });
                tmp13 = tmp12(stats) ?? null;
                tmp14 = tmp11(tmp13) ?? null;
                tmp15 = Term.show(res1, "");
                tmp = Str.concat(tmp14, "\n", tmp15);
              } else {
                if (t instanceof Term.IfLike.class) {
                  param0 = t.kw;
                  param1 = t.desugared;
                  if (param0 instanceof Term.KeywordIf.class) {
                    split = param1;
                    tmp16 = Str.concat(indent3, "  ");
                    tmp17 = Term.showSplit(split, tmp16, false);
                    tmp = Str.concat("if \n", tmp17);
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
    res = tmp;
    return Str.concat(indent3, res);
  } 
  static print(t1) {
    let tmp;
    tmp = Term.show(t1, "");
    return globalThis.log(tmp) ?? null;
  }
  static toString() { return "Term"; }
};
null
let Term = Term2; export default Term;
