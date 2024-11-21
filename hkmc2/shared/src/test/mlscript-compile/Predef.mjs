const Predef$class = class Predef {
  constructor() {
    
  }
  id(x) {
    return x;
  } 
  not(x1) {
    if (x1 === false) {
      return true;
    } else {
      return false;
    }
  } 
  pipe(x2, f) {
    return f(x2);
  } 
  call(receiver, f1) {
    return (arg) => {
      return f1.call(receiver, arg);
    };
  } 
  print(x3) {
    let tmp;
    tmp = String(x3);
    return console.log(tmp);
  } 
  tupleSlice(xs, i, j) {
    let tmp;
    tmp = xs.length - j;
    return globalThis.Array.prototype.slice.call(xs, i, tmp);
  } 
  tupleGet(xs1, i1) {
    return globalThis.Array.prototype.at.call(xs1, i1);
  } 
  checkArgs(functionName, expected, got) {
    let scrut, name, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    scrut = got != expected;
    if (scrut) {
      scrut1 = functionName.length > 0;
      if (scrut1) {
        tmp = " '" + functionName;
        tmp1 = tmp + "'";
      } else {
        tmp1 = "";
      }
      name = tmp1;
      tmp2 = "Function" + name;
      tmp3 = tmp2 + " expected ";
      tmp4 = tmp3 + expected;
      tmp5 = tmp4 + " arguments but got ";
      tmp6 = tmp5 + got;
      throw globalThis.Error(tmp6);
    } else {
      return undefined;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
