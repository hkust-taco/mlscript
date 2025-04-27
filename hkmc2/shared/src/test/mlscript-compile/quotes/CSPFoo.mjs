import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
import CSP from "./../CSP.mjs";
let CSPFoo1;
(class CSPFoo {
  static {
    CSPFoo1 = CSPFoo;
  }
  static get res() {
    let tmp;
    tmp = CSP.test();
    return tmp + 1;
  }
  static toString() { return "CSPFoo"; }
});
let CSPFoo = CSPFoo1; export default CSPFoo;
