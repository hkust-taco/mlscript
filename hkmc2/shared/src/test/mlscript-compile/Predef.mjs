const Predef$class = class Predef {
  constructor() {
    const TraceLogger$class = class TraceLogger {
      constructor() {
        this.indentLvl = 0;
      }
      indent() {
        let prev, tmp;
        prev = this.indentLvl;
        tmp = prev + 1;
        this.indentLvl = tmp;
        return prev;
      } 
      resetIndent(n) {
        this.indentLvl = n;
        return undefined;
      } 
      log(msg) {
        let tmp, tmp1, tmp2, tmp3, tmp4;
        tmp = "| ".repeat(this.indentLvl);
        tmp1 = "  ".repeat(this.indentLvl);
        tmp2 = "\n" + tmp1;
        tmp3 = msg.replaceAll("\n", tmp2);
        tmp4 = tmp + tmp3;
        return console.log(tmp4);
      }
      toString() { return "TraceLogger"; }
    };
    this.TraceLogger = new TraceLogger$class;
    this.TraceLogger.class = TraceLogger$class;
    this.Test = class Test {
      constructor() {
        this.y = 1;
      }
      toString() { return "Test"; }
    };
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
  apply(receiver, f1) {
    return (...args) => {
      return f1(receiver, ...args);
    };
  } 
  call(receiver1, f2) {
    return (...args) => {
      return f2.call(receiver1, ...args);
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
  checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp = got < expected;
    tmp1 = got > expected;
    tmp2 = isUB && tmp1;
    scrut = tmp || tmp2;
    if (scrut) {
      scrut1 = functionName.length > 0;
      if (scrut1) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      name = tmp4;
      tmp5 = "Function" + name;
      tmp6 = tmp5 + " expected ";
      tmp7 = tmp6 + expected;
      tmp8 = tmp7 + " arguments but got ";
      tmp9 = tmp8 + got;
      throw globalThis.Error(tmp9);
    } else {
      return undefined;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
