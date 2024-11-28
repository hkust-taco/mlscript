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
    return ((f(x2)) ?? null);
  } 
  call(receiver, f1) {
    return (arg) => {
      return ((f1.call(receiver, arg)) ?? null);
    };
  } 
  print(x3) {
    let tmp;
    tmp = ((String(x3)) ?? null);
    return ((console.log(tmp)) ?? null);
  } 
  tupleSlice(xs, i, j) {
    let selRes, tmp, selRes1, tmp1, selRes2, tmp2, selRes3, tmp3, tmp4;
    selRes = globalThis.Array;
    if (selRes === undefined) {
      throw new globalThis.Error("Access to required field 'Array' yielded 'undefined'");
    } else {
      tmp = selRes;
    }
    selRes1 = tmp.prototype;
    if (selRes1 === undefined) {
      throw new globalThis.Error("Access to required field 'prototype' yielded 'undefined'");
    } else {
      tmp1 = selRes1;
    }
    selRes2 = tmp1.slice;
    if (selRes2 === undefined) {
      throw new globalThis.Error("Access to required field 'slice' yielded 'undefined'");
    } else {
      tmp2 = selRes2;
    }
    selRes3 = xs.length;
    if (selRes3 === undefined) {
      throw new globalThis.Error("Access to required field 'length' yielded 'undefined'");
    } else {
      tmp3 = selRes3;
    }
    tmp4 = tmp3 - j;
    return ((tmp2.call(xs, i, tmp4)) ?? null);
  } 
  tupleGet(xs1, i1) {
    let selRes, tmp, selRes1, tmp1, selRes2, tmp2;
    selRes = globalThis.Array;
    if (selRes === undefined) {
      throw new globalThis.Error("Access to required field 'Array' yielded 'undefined'");
    } else {
      tmp = selRes;
    }
    selRes1 = tmp.prototype;
    if (selRes1 === undefined) {
      throw new globalThis.Error("Access to required field 'prototype' yielded 'undefined'");
    } else {
      tmp1 = selRes1;
    }
    selRes2 = tmp1.at;
    if (selRes2 === undefined) {
      throw new globalThis.Error("Access to required field 'at' yielded 'undefined'");
    } else {
      tmp2 = selRes2;
    }
    return ((tmp2.call(xs1, i1)) ?? null);
  } 
  checkArgs(functionName, expected, got) {
    let scrut, name, scrut1, selRes, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    scrut = got != expected;
    if (scrut) {
      selRes = functionName.length;
      if (selRes === undefined) {
        throw new globalThis.Error("Access to required field 'length' yielded 'undefined'");
      } else {
        tmp = selRes;
      }
      scrut1 = tmp > 0;
      if (scrut1) {
        tmp1 = " '" + functionName;
        tmp2 = tmp1 + "'";
      } else {
        tmp2 = "";
      }
      name = tmp2;
      tmp3 = "Function" + name;
      tmp4 = tmp3 + " expected ";
      tmp5 = tmp4 + expected;
      tmp6 = tmp5 + " arguments but got ";
      tmp7 = tmp6 + got;
      throw ((globalThis.Error(tmp7)) ?? null);
    } else {
      return null;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
