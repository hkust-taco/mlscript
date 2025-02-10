let QuoteInc1;
QuoteInc1 = class QuoteInc {
  static {}
  static get res() {
    return (x) => {
      return x + 1;
    };
  }
  static toString() { return "QuoteInc"; }
};
null
let QuoteInc = QuoteInc1; export default QuoteInc;
