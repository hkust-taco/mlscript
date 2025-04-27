import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let QuoteFoo1;
(class QuoteFoo {
  static {
    QuoteFoo1 = QuoteFoo;
  }
  static get res() {
    return 1 + 1;
  }
  static toString() { return "QuoteFoo"; }
});
let QuoteFoo = QuoteFoo1; export default QuoteFoo;
