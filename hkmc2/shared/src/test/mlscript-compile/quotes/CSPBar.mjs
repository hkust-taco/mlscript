import Example from "./../Example.mjs";
let CSPBar1;
CSPBar1 = class CSPBar {
  static {}
  static get res() {
    return Example.inc(0);
  }
  static toString() { return "CSPBar"; }
};
null
let CSPBar = CSPBar1; export default CSPBar;
