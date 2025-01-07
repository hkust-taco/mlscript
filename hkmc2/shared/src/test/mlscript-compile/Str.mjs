const Str$class = class Str {
  constructor() {}
  concat2(a, b) {
    return a + b;
  } 
  concat(...xs) {
    return xs.join("") ?? null;
  } 
  from(value) {
    return globalThis.String(value) ?? null;
  }
  toString() { return "Str"; }
}; const Str = new Str$class;
Str.class = Str$class;
null
export default Str;
