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
    let tmp, x, tmp1, tmp2, tmp3, tmp4;
    tmp = globalThis.Predef.term.freshName("x");
    x = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = new globalThis.Predef.term.Ref(x);
    tmp2 = QuoteExample.power(tmp1);
    tmp3 = runtime.safeCall(tmp2(3));
    tmp4 = new globalThis.Predef.term.Lam([
      x
    ], tmp3);
    return Predef.term.codegen(tmp4, "./hkmc2/shared/src/test/mlscript-compile/quotes/Cubic.mls")
  } 
  static genGib12() {
    let tmp;
    tmp = QuoteExample.gib(12);
    return Predef.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/Gib12.mls")
  } 
  static genSafeDiv() {
    let tmp;
    tmp = QuoteExample.safeDiv();
    return Predef.term.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/SafeDiv.mls")
  }
  static toString() { return "QuoteExample2"; }
};
let QuoteExample2 = QuoteExample21; export default QuoteExample2;
