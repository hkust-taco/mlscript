import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
import QuoteExample from "./QuoteExample.mjs";
let QuoteExample21;
QuoteExample21 = class QuoteExample2 {
  static {}
  static codegen() {
    let tmp, tmp1, tmp2;
    tmp = QuoteExample.foo();
    tmp1 = Predef.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteFoo.mls");
    tmp2 = QuoteExample.inc();
    return Predef.term.codegen(tmp2, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteInc.mls")
  } 
  static genCubic() {
    let x, tmp, tmp1, tmp2, tmp3;
    x = new globalThis.Predef.term.Symbol("x");
    tmp = new globalThis.Predef.term.Ref(x);
    tmp1 = QuoteExample.power(tmp);
    tmp2 = runtime.safeCall(tmp1(3));
    tmp3 = new globalThis.Predef.term.Lam([
      x
    ], tmp2);
    return Predef.term.codegen(tmp3, "./hkmc2/shared/src/test/mlscript-compile/quotes/Cubic.mls")
  }
  static toString() { return "QuoteExample2"; }
};
let QuoteExample2 = QuoteExample21; export default QuoteExample2;
