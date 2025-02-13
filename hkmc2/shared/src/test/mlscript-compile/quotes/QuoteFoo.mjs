import runtime from "./../Runtime.mjs";
let QuoteFoo1;
QuoteFoo1 = class QuoteFoo {
  static {}
  static get res() {
    let tmp;
    tmp = 1 + 1;
    return ((x_0) => {
      return x_0
    })(tmp);
  }
  static toString() { return "QuoteFoo"; }
};
let QuoteFoo = QuoteFoo1; export default QuoteFoo;
