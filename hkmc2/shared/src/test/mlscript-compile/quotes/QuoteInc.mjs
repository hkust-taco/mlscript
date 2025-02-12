import runtime from "./../Runtime.mjs";
let QuoteInc1;
QuoteInc1 = class QuoteInc {
  static {}
  static get res() {
    return (x_11) => {
      return x_11 + 1
    };
  }
  static toString() { return "QuoteInc"; }
};
let QuoteInc = QuoteInc1; export default QuoteInc;
