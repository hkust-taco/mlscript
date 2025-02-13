import runtime from "./Runtime.mjs";
import Example from "./Example.mjs";
let CSP1;
CSP1 = class CSP {
  static {}
  static test() {
    return 123
  } 
  static foo() {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    tmp = new runtime.term.Symbol("CSP");
    tmp1 = new runtime.term.CSRef(tmp, import.meta.url, undefined);
    tmp2 = new runtime.term.Sel(tmp1, "test");
    tmp3 = new runtime.term.Tup([]);
    tmp4 = new runtime.term.App(tmp2, tmp3);
    tmp5 = new runtime.term.Lit(1);
    tmp6 = new runtime.term.Builtin("+");
    tmp7 = new runtime.term.Tup([
      tmp4,
      tmp5
    ]);
    return new runtime.term.App(tmp6, tmp7)
  } 
  static bar() {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new runtime.term.Symbol("Example");
    tmp1 = new runtime.term.CSRef(tmp, import.meta.url, "Example.mls");
    tmp2 = new runtime.term.Lit(0);
    tmp3 = new runtime.term.Sel(tmp1, "inc");
    tmp4 = new runtime.term.Tup([
      tmp2
    ]);
    return new runtime.term.App(tmp3, tmp4)
  }
  static toString() { return "CSP"; }
};
let CSP = CSP1; export default CSP;
