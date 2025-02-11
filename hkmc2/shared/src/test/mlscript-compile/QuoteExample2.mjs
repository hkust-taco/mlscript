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
  static toString() { return "QuoteExample2"; }
};
let QuoteExample2 = QuoteExample21; export default QuoteExample2;
