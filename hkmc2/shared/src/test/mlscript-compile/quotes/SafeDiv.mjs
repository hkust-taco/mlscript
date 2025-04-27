import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let SafeDiv1;
(class SafeDiv {
  static {
    SafeDiv1 = SafeDiv;
  }
  static get res() {
    let lambda;
    lambda = (undefined, function (x_18, y_2, d_0) {
      let scrut_2;
      scrut_2 = y_2 == 0;
      if (scrut_2 === true) {
        return d_0
      } else {
        return x_18 / y_2
      }
    });
    return lambda
  }
  static toString() { return "SafeDiv"; }
});
let SafeDiv = SafeDiv1; export default SafeDiv;
