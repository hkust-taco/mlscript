import runtime from "./../Runtime.mjs";
let Cubic1;
Cubic1 = class Cubic {
  static {}
  static get res() {
    return (x_2) => {
      let tmp, tmp1;
      tmp = x_2 * 1;
      tmp1 = x_2 * tmp;
      return x_2 * tmp1
    };
  }
  static toString() { return "Cubic"; }
};
let Cubic = Cubic1; export default Cubic;
