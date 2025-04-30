import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let QuoteInc1;
(class QuoteInc {
  static {
    QuoteInc1 = QuoteInc;
  }
  static get res() {
    let lambda;
    lambda = (undefined, function (x_0) {
      return x_0 + 1
    });
    return lambda
  }
  static toString() { return "QuoteInc"; }
});
let QuoteInc = QuoteInc1; export default QuoteInc;
