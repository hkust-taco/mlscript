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
      let scrutSelChk;
      scrutSelChk = f1.call === undefined;
      if (scrutSelChk) {
        throw new globalThis.Error("call not found");
      } else {
        return ((f1.call(receiver, arg)) ?? null);
      }
    };
  } 
  print(x3) {
    let scrutSelChk, tmp;
    scrutSelChk = console.log === undefined;
    if (scrutSelChk) {
      throw new globalThis.Error("log not found");
    } else {
      tmp = ((String(x3)) ?? null);
      return ((console.log(tmp)) ?? null);
    }
  } 
  tupleSlice(xs, i, j) {
    let scrutSelChk, scrutSelChk1, scrutSelChk2, scrutSelChk3, scrutSelChk4, tmp;
    scrutSelChk = globalThis.Array === undefined;
    if (scrutSelChk) {
      throw new globalThis.Error("Array not found");
    } else {
      scrutSelChk1 = globalThis.Array.prototype === undefined;
      if (scrutSelChk1) {
        throw new globalThis.Error("prototype not found");
      } else {
        scrutSelChk2 = globalThis.Array.prototype.slice === undefined;
        if (scrutSelChk2) {
          throw new globalThis.Error("slice not found");
        } else {
          scrutSelChk3 = globalThis.Array.prototype.slice.call === undefined;
          if (scrutSelChk3) {
            throw new globalThis.Error("call not found");
          } else {
            scrutSelChk4 = xs.length === undefined;
            if (scrutSelChk4) {
              throw new globalThis.Error("length not found");
            } else {
              tmp = xs.length - j;
              return ((globalThis.Array.prototype.slice.call(xs, i, tmp)) ?? null);
            }
          }
        }
      }
    }
  } 
  tupleGet(xs1, i1) {
    let scrutSelChk, scrutSelChk1, scrutSelChk2, scrutSelChk3;
    scrutSelChk = globalThis.Array === undefined;
    if (scrutSelChk) {
      throw new globalThis.Error("Array not found");
    } else {
      scrutSelChk1 = globalThis.Array.prototype === undefined;
      if (scrutSelChk1) {
        throw new globalThis.Error("prototype not found");
      } else {
        scrutSelChk2 = globalThis.Array.prototype.at === undefined;
        if (scrutSelChk2) {
          throw new globalThis.Error("at not found");
        } else {
          scrutSelChk3 = globalThis.Array.prototype.at.call === undefined;
          if (scrutSelChk3) {
            throw new globalThis.Error("call not found");
          } else {
            return ((globalThis.Array.prototype.at.call(xs1, i1)) ?? null);
          }
        }
      }
    }
  } 
  checkArgs(functionName, expected, got) {
    let scrut, name, scrut1, scrutSelChk, tmp, tmp1, scrutSelChk1, tmp2, tmp3, tmp4, tmp5, tmp6;
    scrut = got != expected;
    if (scrut) {
      scrutSelChk = functionName.length === undefined;
      if (scrutSelChk) {
        throw new globalThis.Error("length not found");
      } else {
        scrut1 = functionName.length > 0;
        if (scrut1) {
          tmp = " '" + functionName;
          tmp1 = tmp + "'";
        } else {
          tmp1 = "";
        }
      }
      name = tmp1;
      scrutSelChk1 = globalThis.Error === undefined;
      if (scrutSelChk1) {
        throw new globalThis.Error("Error not found");
      } else {
        tmp2 = "Function" + name;
        tmp3 = tmp2 + " expected ";
        tmp4 = tmp3 + expected;
        tmp5 = tmp4 + " arguments but got ";
        tmp6 = tmp5 + got;
        throw ((globalThis.Error(tmp6)) ?? null);
      }
    } else {
      return null;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
