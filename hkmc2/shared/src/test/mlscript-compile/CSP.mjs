import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import Example from "./Example.mjs";
import CSPNest from "./quotes/CSPNest.mjs";
let CSP1;
(class CSP {
  static {
    CSP1 = CSP;
  }
  static test() {
    return 123
  } 
  static foo() {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    tmp = new Term.Symbol("CSP");
    tmp1 = new Term.CSRef(tmp, import.meta.url, undefined);
    tmp2 = new Term.Sel(tmp1, "test");
    tmp3 = new Term.Tup([]);
    tmp4 = new Term.App(tmp2, tmp3);
    tmp5 = new Term.Lit(1);
    tmp6 = new Term.Builtin("+");
    tmp7 = new Term.Tup([
      tmp4,
      tmp5
    ]);
    return new Term.App(tmp6, tmp7)
  } 
  static bar() {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new Term.Symbol("Example");
    tmp1 = new Term.CSRef(tmp, import.meta.url, "Example.mls");
    tmp2 = new Term.Lit(0);
    tmp3 = new Term.Sel(tmp1, "inc");
    tmp4 = new Term.Tup([
      tmp2
    ]);
    return new Term.App(tmp3, tmp4)
  } 
  static baz() {
    let tmp, tmp1, tmp2, tmp3;
    tmp = new Term.Symbol("CSPNest");
    tmp1 = new Term.CSRef(tmp, import.meta.url, "quotes/CSPNest.mls");
    tmp2 = new Term.Sel(tmp1, "nest_f");
    tmp3 = new Term.Tup([]);
    return new Term.App(tmp2, tmp3)
  }
  static toString() { return "CSP"; }
});
let CSP = CSP1; export default CSP;
