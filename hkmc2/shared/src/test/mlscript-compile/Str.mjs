const Str$class = class Str {
  constructor() {
    
  }
  concat(a, b) {
    return a + b;
  } 
  string(value) {
    return globalThis.String(value);
  }
  toString() { return "Str"; }
}; const Str = new Str$class;
Str.class = Str$class;
undefined
export default Str;
