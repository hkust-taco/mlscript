import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import Term1 from "./Term.mjs";
import QuoteExample from "./QuoteExample.mjs";
let QuoteExample21;
(class QuoteExample2 {
  static {
    QuoteExample21 = QuoteExample2;
  }
  static codegen() {
    let tmp, tmp1, tmp2;
    tmp = QuoteExample.foo();
    tmp1 = Term1.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteFoo.mls");
    tmp2 = QuoteExample.inc();
    return Term1.codegen(tmp2, "./hkmc2/shared/src/test/mlscript-compile/quotes/QuoteInc.mls")
  } 
  static genCubic() {
    let x, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Term.freshName("x");
    tmp1 = new Term.Symbol(tmp);
    x = new Term.Ref(tmp1);
    tmp2 = QuoteExample.power(x);
    tmp3 = runtime.safeCall(tmp2(3));
    tmp4 = new Term.Lam([
      tmp1
    ], tmp3);
    return Term1.codegen(tmp4, "./hkmc2/shared/src/test/mlscript-compile/quotes/Cubic.mls")
  } 
  static genGib12() {
    let tmp;
    tmp = QuoteExample.gib(12);
    return Term1.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/Gib12.mls")
  } 
  static genSafeDiv() {
    let tmp;
    tmp = QuoteExample.safeDiv();
    return Term1.codegen(tmp, "./hkmc2/shared/src/test/mlscript-compile/quotes/SafeDiv.mls")
  }
  static toString() { return "QuoteExample2"; }
});
let QuoteExample2 = QuoteExample21; export default QuoteExample2;
