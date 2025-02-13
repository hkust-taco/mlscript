import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
import QuoteExample from "./QuoteExample.mjs";
let QuoteExample21;
QuoteExample21 = class QuoteExample2 {
  static {}
  static codegen() {
    let tmp, tmp1, tmp2;
    tmp = QuoteExample.foo();
    tmp1 = Runtime.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteFoo.mls");
    tmp2 = QuoteExample.inc();
    return Runtime.term.codegen(tmp2, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteInc.mls")
  } 
  static genCubic() {
    let tmp, x, tmp1, tmp2, tmp3, tmp4;
    tmp = runtime.term.freshName("x");
    x = new runtime.term.Symbol(tmp);
    tmp1 = new runtime.term.Ref(x);
    tmp2 = QuoteExample.power(tmp1);
    tmp3 = runtime.safeCall(tmp2(3));
    tmp4 = new runtime.term.Lam([
      x
    ], tmp3);
    return Runtime.term.codegen(tmp4, "./hkmc2/shared/src/test/mlscript-compile/quotes/Cubic.mls")
  } 
  static genGib12() {
    let tmp;
    tmp = QuoteExample.gib(12);
    return Runtime.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/Gib12.mls")
  } 
  static genSafeDiv() {
    let tmp;
    tmp = QuoteExample.safeDiv();
    return Runtime.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/SafeDiv.mls")
  }
  static toString() { return "QuoteExample2"; }
};
let QuoteExample2 = QuoteExample21; export default QuoteExample2;
