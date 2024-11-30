import Predef from "./Predef.mjs";
const Example$class = class Example {
  constructor() {
    
  }
  funnySlash(f, arg) {
    return f(arg);
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
}; const Example = new Example$class;
Example.class = Example$class;
undefined
export default Example;
