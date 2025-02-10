import CSP from "./../CSP.mjs";
let CSPFoo1;
CSPFoo1 = class CSPFoo {
  static {}
  static get res() {
    let tmp;
    tmp = CSP.test();
    return tmp + 1;
  }
  static toString() { return "CSPFoo"; }
};
null
let CSPFoo = CSPFoo1; export default CSPFoo;
