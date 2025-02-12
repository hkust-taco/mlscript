import runtime from "./../Runtime.mjs";
let SafeDiv1;
SafeDiv1 = class SafeDiv {
  static {}
  static get res() {
    return (x_25, y_2, d_0) => {
      let scrut_4;
      scrut_4 = y_2 == 0;
      if (scrut_4 === true) {
        return d_0
      } else {
        return x_25 / y_2
      }
    };
  }
  static toString() { return "SafeDiv"; }
};
let SafeDiv = SafeDiv1; export default SafeDiv;
