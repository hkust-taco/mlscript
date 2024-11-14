const String$class = class String {
  constructor() {
    
  }
  concat(lhs, rhs) {
    return globalThis.String.prototype.concat.call(lhs, rhs);
  } 
  toString(value) {
    return globalThis.String(value);
  }
}; const String = new String$class;
String.class = String$class;
undefined
export default String;
