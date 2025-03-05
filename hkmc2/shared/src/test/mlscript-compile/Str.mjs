import runtime from "./Runtime.mjs";
let Str1;
Str1 = class Str {
  static {}
  static concat2(a, b) {
    return a + b
  } 
  static concat(...xs) {
    return runtime.safeCall(xs.join(""))
  } 
  static from(value) {
    return runtime.safeCall(globalThis.String(value))
  } 
  static parenthesizedIf(x, cond) {
    let tmp;
    if (cond === true) {
      tmp = "(" + x;
      return tmp + ")"
    } else {
      return x
    }
  }
  static toString() { return "Str"; }
};
let Str = Str1; export default Str;
