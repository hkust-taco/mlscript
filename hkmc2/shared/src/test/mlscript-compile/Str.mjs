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
  static toString() { return "Str"; }
};
let Str = Str1; export default Str;
