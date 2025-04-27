import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
import Example from "./../Example.mjs";
let CSPBar1;
(class CSPBar {
  static {
    CSPBar1 = CSPBar;
  }
  static get res() {
    return Example.inc(0);
  }
  static toString() { return "CSPBar"; }
});
let CSPBar = CSPBar1; export default CSPBar;
