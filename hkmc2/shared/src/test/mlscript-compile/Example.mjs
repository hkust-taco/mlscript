import Predef from "./Predef.mjs";
let Example1;
const Example$class = class Example {
  constructor() {}
  funnySlash(f, arg) {
    return f(arg) ?? null;
  } 
  inc(x) {
    return x + 1;
  } 
  test(x1) {
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
  toString() { return "Example"; }
}; Example1 = new Example$class;
Example1.class = Example$class;
null
let Example = Example1; export default Example;
