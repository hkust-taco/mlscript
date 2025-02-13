import runtime from "./../Runtime.mjs";
let Cubic1;
Cubic1 = class Cubic {
  static {}
  static get res() {
    return (x_5) => {
      let tmp, tmp1;
      tmp = x_5 * 1;
      tmp1 = x_5 * tmp;
      return x_5 * tmp1
    };
  }
  static toString() { return "Cubic"; }
};
let Cubic = Cubic1; export default Cubic;
