import runtime from "./../Runtime.mjs";
let QuoteFoo1;
QuoteFoo1 = class QuoteFoo {
  static {}
  static get res() {
    return 1 + 1;
  }
  static toString() { return "QuoteFoo"; }
};
let QuoteFoo = QuoteFoo1; export default QuoteFoo;
