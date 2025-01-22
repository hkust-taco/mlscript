let Str1;
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
}; Str1 = new Str$class;
Str1.class = Str$class;
null
let Str = Str1; export default Str;
