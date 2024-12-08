const Predef$class = class Predef {
  constructor() {
    this.MatchResult = function MatchResult(captures1) { return new MatchResult.class(captures1); };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
        
      }
      toString() { return "MatchResult(" + this.captures + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) { return new MatchFailure.class(errors1); };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
        
      }
      toString() { return "MatchFailure(" + this.errors + ")"; }
    };
    const TraceLogger$class = class TraceLogger {
      constructor() {
        this.enabled = false;
        this.indentLvl = 0;
      }
      indent() {
        let scrut, prev, tmp;
        scrut = this.enabled;
        if (scrut) {
          prev = this.indentLvl;
          tmp = prev + 1;
          this.indentLvl = tmp;
          return prev;
        } else {
          return null;
        }
      } 
      resetIndent(n) {
        let scrut;
        scrut = this.enabled;
        if (scrut) {
          this.indentLvl = n;
          return null;
        } else {
          return null;
        }
      } 
      log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = this.enabled;
        if (scrut) {
          tmp = "| ".repeat(this.indentLvl) ?? null;
          tmp1 = "  ".repeat(this.indentLvl) ?? null;
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return console.log(tmp4) ?? null;
        } else {
          return null;
        }
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
    return f(x2) ?? null;
  } 
  apply(receiver, f1) {
    return (...args) => {
      return f1(receiver, ...args) ?? null;
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
    return console.log(tmp) ?? null;
  } 
  tupleSlice(xs, i, j) {
    let tmp;
    tmp = xs.length - j;
    return globalThis.Array.prototype.slice.call(xs, i, tmp) ?? null;
  } 
  tupleGet(xs1, i1) {
    return globalThis.Array.prototype.at.call(xs1, i1);
  } 
  stringStartsWith(string, prefix) {
    return string.startsWith(prefix) ?? null;
  } 
  stringGet(string1, i2) {
    return string1.at(i2) ?? null;
  } 
  stringDrop(string2, n) {
    return string2.slice(n) ?? null;
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
      throw globalThis.Error(tmp9) ?? null;
    } else {
      return null;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
