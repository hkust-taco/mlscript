import runtime from "./../Runtime.mjs";
import Term from "./../Term.mjs";
let Cubic1;
(class Cubic {
  static {
    Cubic1 = Cubic;
  }
  static get res() {
    let lambda;
    lambda = (undefined, function (x_5) {
      let tmp, tmp1;
      tmp = x_5 * 1;
      tmp1 = x_5 * tmp;
      return x_5 * tmp1
    });
    return lambda
  }
  static toString() { return "Cubic"; }
});
let Cubic = Cubic1; export default Cubic;
