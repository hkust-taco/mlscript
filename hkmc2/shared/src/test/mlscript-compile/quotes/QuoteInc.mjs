import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let QuoteInc1;
(class QuoteInc {
  static {
    QuoteInc1 = QuoteInc;
  }
  static get res() {
    let lambda;
    lambda = (undefined, function (x_4) {
      return x_4 + 1
    });
    return lambda
  }
  static toString() { return "QuoteInc"; }
});
let QuoteInc = QuoteInc1; export default QuoteInc;
