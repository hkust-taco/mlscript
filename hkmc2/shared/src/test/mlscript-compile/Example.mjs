import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
let privFun, Example1;
privFun = function privFun() {
  return "hi"
};
Example1 = class Example {
  static {}
  static get pubFun() {
    let tmp;
    tmp = privFun();
    return tmp;
  } 
  static funnySlash(f, arg) {
    return runtime.safeCall(f(arg))
  } 
  static inc(x) {
    return x + 1
  } 
  static test(x1) {
    if (globalThis.Number.isInteger(x1)) {
      return "int"
    } else if (typeof x1 === 'number') {
      return "num"
    } else if (typeof x1 === 'string') {
      return "str"
    } else {
      return "other"
    }
  }
  static toString() { return "Example"; }
};
let Example = Example1; export default Example;
