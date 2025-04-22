import runtime from "./Runtime.mjs";
let Str1;
const Str$class = class Str {
  constructor() {}
  concat2(a, b) {
    return a + b
  } 
  concat(...xs) {
    return runtime.safeCall(xs.join(""))
  } 
  from(value) {
    return runtime.safeCall(globalThis.String(value))
  } 
  parenthesizedIf(x, cond) {
    let tmp;
    if (cond === true) {
      tmp = "(" + x;
      return tmp + ")"
    } else {
      return x
    }
  }
  toString() { return "Str"; }
}; Str1 = new Str$class;
Str1.class = Str$class;
let Str = Str1; export default Str;
