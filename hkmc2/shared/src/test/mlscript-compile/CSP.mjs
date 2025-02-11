import runtime from "./Runtime.mjs";
import Example from "./Example.mjs";
let CSP1;
CSP1 = class CSP {
  static {}
  static test() {
    return 123
  } 
  static foo() {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = new globalThis.Predef.term.Symbol("+");
    tmp1 = new globalThis.Predef.term.Symbol("CSP");
    tmp2 = new globalThis.Predef.term.CSRef(tmp1, import.meta.url, undefined);
    tmp3 = new globalThis.Predef.term.Sel(tmp2, "test");
    tmp4 = new globalThis.Predef.term.Tup([]);
    tmp5 = new globalThis.Predef.term.App(tmp3, tmp4);
    tmp6 = new globalThis.Predef.term.Lit(1);
    tmp7 = new globalThis.Predef.term.Ref(tmp);
    tmp8 = new globalThis.Predef.term.Tup([
      tmp5,
      tmp6
    ]);
    return new globalThis.Predef.term.App(tmp7, tmp8)
  } 
  static bar() {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new globalThis.Predef.term.Symbol("Example");
    tmp1 = new globalThis.Predef.term.CSRef(tmp, import.meta.url, "Example.mls");
    tmp2 = new globalThis.Predef.term.Lit(0);
    tmp3 = new globalThis.Predef.term.Sel(tmp1, "inc");
    tmp4 = new globalThis.Predef.term.Tup([
      tmp2
    ]);
    return new globalThis.Predef.term.App(tmp3, tmp4)
  }
  static toString() { return "CSP"; }
};
let CSP = CSP1; export default CSP;
