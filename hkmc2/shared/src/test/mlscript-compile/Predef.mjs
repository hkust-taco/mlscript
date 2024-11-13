const Predef$class = class Predef {
  constructor() {
    
  }
  id(x) {
    return x;
  } 
  pipe(x1, f) {
    return f(x1);
  } 
  call(receiver, f1) {
    return (arg) => {
      return f1.call(receiver, arg);
    };
  } 
  print(x2) {
    let tmp;
    tmp = String(x2);
    return console.log(tmp);
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
