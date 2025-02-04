let Str1;
Str1 = class Str {
  static {}
  static concat2(a, b) {
    return a + b
  } 
  static concat(...xs) {
    return xs.join("") ?? null
  } 
  static from(value) {
    return globalThis.String(value) ?? null
  }
  static toString() { return "Str"; }
};
null
let Str = Str1; export default Str;
