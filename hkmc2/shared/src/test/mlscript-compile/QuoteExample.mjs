import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
let QuoteExample1;
QuoteExample1 = class QuoteExample {
  static {}
  static foo() {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new globalThis.Predef.term.Symbol("+");
    tmp1 = new globalThis.Predef.term.Lit(1);
    tmp2 = new globalThis.Predef.term.Lit(2);
    tmp3 = new globalThis.Predef.term.Ref(tmp);
    tmp4 = new globalThis.Predef.term.Tup([
      tmp1,
      tmp2
    ]);
    return new globalThis.Predef.term.App(tmp3, tmp4)
  } 
  static inc() {
    let x, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    x = new globalThis.Predef.term.Symbol("x");
    tmp = new globalThis.Predef.term.Symbol("+");
    tmp1 = new globalThis.Predef.term.Ref(x);
    tmp2 = new globalThis.Predef.term.Lit(1);
    tmp3 = new globalThis.Predef.term.Ref(tmp);
    tmp4 = new globalThis.Predef.term.Tup([
      tmp1,
      tmp2
    ]);
    tmp5 = new globalThis.Predef.term.App(tmp3, tmp4);
    return new globalThis.Predef.term.Lam([
      x
    ], tmp5)
  }
  static toString() { return "QuoteExample"; }
};
let QuoteExample = QuoteExample1; export default QuoteExample;
