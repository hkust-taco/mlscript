import runtime from "./../Runtime.mjs";
let Cubic1;
Cubic1 = class Cubic {
  static {}
  static get res() {
    return (x_12) => {
      let tmp, tmp1;
      tmp = x_12 * 1;
      tmp1 = x_12 * tmp;
      return x_12 * tmp1
    };
  }
  static toString() { return "Cubic"; }
};
let Cubic = Cubic1; export default Cubic;
