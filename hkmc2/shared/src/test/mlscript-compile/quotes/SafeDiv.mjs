import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let SafeDiv1;
(class SafeDiv {
  static {
    SafeDiv1 = SafeDiv;
  }
  static get res() {
    let lambda;
    lambda = (undefined, function (x_0, y_0, d_0) {
      let scrut_0;
      scrut_0 = y_0 == 0;
      if (scrut_0 === true) {
        return d_0
      } else {
        return x_0 / y_0
      }
    });
    return lambda
  }
  static toString() { return "SafeDiv"; }
});
let SafeDiv = SafeDiv1; export default SafeDiv;
