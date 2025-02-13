import runtime from "./../Runtime.mjs";
let SafeDiv1;
SafeDiv1 = class SafeDiv {
  static {}
  static get res() {
    return (x_14, y_1, d_0) => {
      let scrut_0;
      scrut_0 = y_1 == 0;
      if (scrut_0 === true) {
        return d_0
      } else {
        return x_14 / y_1
      }
    };
  }
  static toString() { return "SafeDiv"; }
};
let SafeDiv = SafeDiv1; export default SafeDiv;
