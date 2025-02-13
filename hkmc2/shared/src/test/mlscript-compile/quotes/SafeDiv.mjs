import runtime from "./../Runtime.mjs";
let SafeDiv1;
SafeDiv1 = class SafeDiv {
  static {}
  static get res() {
    return (x_18, y_2, d_0) => {
      let scrut_2;
      scrut_2 = y_2 == 0;
      if (scrut_2 === true) {
        return d_0
      } else {
        return x_18 / y_2
      }
    };
  }
  static toString() { return "SafeDiv"; }
};
let SafeDiv = SafeDiv1; export default SafeDiv;
