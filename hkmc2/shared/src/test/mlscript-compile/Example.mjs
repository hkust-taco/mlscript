import Predef from "./Predef.mjs";
let Example1;
Example1 = class Example {
  static {}
  static funnySlash(f, arg) {
    return f(arg) ?? null;
  } 
  static inc(x) {
    return x + 1;
  } 
  static test(x1) {
    if (globalThis.Number.isInteger(x1)) {
      return "int";
    } else {
      if (typeof x1 === 'number') {
        return "num";
      } else {
        if (typeof x1 === 'string') {
          return "str";
        } else {
          return "other";
        }
      }
    }
  }
  static toString() { return "Example"; }
};
null
let Example = Example1; export default Example;
