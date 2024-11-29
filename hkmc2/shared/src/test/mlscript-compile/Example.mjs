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
  toString() { return "Example"; }
}; const Example = new Example$class;
Example.class = Example$class;
undefined
export default Example;
