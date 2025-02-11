import runtime from "./../Runtime.mjs";
let Cubic1;
Cubic1 = class Cubic {
  static {}
  static get res() {
    return (x) => {
      let tmp, tmp1;
      tmp = x * 1;
      tmp1 = x * tmp;
      return x * tmp1
    };
  }
  static toString() { return "Cubic"; }
};
let Cubic = Cubic1; export default Cubic;
