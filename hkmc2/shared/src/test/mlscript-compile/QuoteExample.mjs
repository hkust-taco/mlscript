import Predef from "./Predef.mjs";
let QuoteExample1;
QuoteExample1 = class QuoteExample {
  static {}
  static test() {
    return 123;
  } 
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
    return new globalThis.Predef.term.App(tmp3, tmp4);
  } 
  static inc() {
    let x, tmp;
    x = new globalThis.Predef.term.Symbol("x");
    tmp = new globalThis.Predef.term.Ref(x);
    return new globalThis.Predef.term.Lam([
      x
    ], tmp);
  }
  static toString() { return "QuoteExample"; }
};
null
let QuoteExample = QuoteExample1; export default QuoteExample;
