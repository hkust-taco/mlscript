import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
import Rendering from "./Rendering.mjs";
let Predef1;
Predef1 = class Predef {
  static {
    this.pass1 = Rendering.pass1;
    this.pass2 = Rendering.pass2;
    this.pass3 = Rendering.pass3;
    this.passing = Rendering.passing;
    this.map = Rendering.map;
    this.fold = Rendering.fold;
    this.interleave = Rendering.interleave;
    this.render = Rendering.render;
    this.assert = globalThis.console.assert;
    this.foldl = Predef.fold;
    this.TraceLogger = class TraceLogger {
      static {
        this.enabled = false;
        this.indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp = prev + 1;
          TraceLogger.indentLvl = tmp;
          return prev
        } else {
          return runtime.Unit
        }
      } 
      static resetIndent(n) {
        let scrut;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          TraceLogger.indentLvl = n;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      } 
      static log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return runtime.safeCall(globalThis.console.log(tmp4))
        } else {
          return runtime.Unit
        }
      }
      static toString() { return "TraceLogger"; }
    };
    this.Test = class Test {
      constructor() {
        let tmp;
        tmp = Predef.print("Test");
        this.y = 1;
      }
      toString() { return "Test"; }
    };
  }
  static id(x) {
    return x
  } 
  static not(x1) {
    if (x1 === false) {
      return true
    } else {
      return false
    }
  } 
  static apply(f, ...args) {
    return runtime.safeCall(f(...args))
  } 
  static pipeInto(x2, f1) {
    return runtime.safeCall(f1(x2))
  } 
  static pipeFrom(f2, x3) {
    return runtime.safeCall(f2(x3))
  } 
  static tap(x4, f3) {
    let tmp;
    tmp = runtime.safeCall(f3(x4));
    return (tmp , x4)
  } 
  static pat(f4, x5) {
    let tmp;
    tmp = runtime.safeCall(f4(x5));
    return (tmp , x5)
  } 
  static andThen(f5, g) {
    return (x6) => {
      let tmp;
      tmp = runtime.safeCall(f5(x6));
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f6, g1) {
    return (x6) => {
      let tmp;
      tmp = runtime.safeCall(g1(x6));
      return runtime.safeCall(f6(tmp))
    }
  } 
  static passTo(receiver, f7) {
    return (...args1) => {
      return runtime.safeCall(f7(receiver, ...args1))
    }
  } 
  static call(receiver1, f8) {
    return (...args1) => {
      return f8.call(receiver1, ...args1)
    }
  } 
  static print(...xs) {
    let tmp, tmp1;
    tmp = runtime.safeCall(Predef.map(Predef.renderAsStr));
    tmp1 = runtime.safeCall(tmp(...xs));
    return runtime.safeCall(globalThis.console.log(...tmp1))
  } 
  static printRaw(x6) {
    let tmp;
    tmp = runtime.safeCall(Predef.render(x6));
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static renderAsStr(arg) {
    if (typeof arg === 'string') {
      return arg
    } else {
      return runtime.safeCall(Predef.render(arg))
    }
  } 
  static notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw globalThis.Error(tmp);
  } 
  static get notImplementedError() {
    throw globalThis.Error("Not implemented");
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static tupleSlice(xs2, i, j) {
    let tmp;
    tmp = xs2.length - j;
    return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
  } 
  static tupleGet(xs3, i1) {
    return globalThis.Array.prototype.at.call(xs3, i1)
  } 
  static foldr(f9) {
    return (first, ...rest) => {
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp = len - 1;
        i2 = tmp;
        tmp1 = runtime.safeCall(rest.at(i2));
        init = tmp1;
        tmp6: while (true) {
          scrut = i2 > 0;
          if (scrut === true) {
            tmp2 = i2 - 1;
            i2 = tmp2;
            tmp3 = runtime.safeCall(rest.at(i2));
            tmp4 = runtime.safeCall(f9(tmp3, init));
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6;
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f9(first, init))
      }
    }
  } 
  static mkStr(...xs4) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (acc, x7) {
      let tmp2, tmp3, tmp4;
      if (typeof x7 === 'string') {
        tmp2 = true;
      } else {
        tmp2 = false;
      }
      tmp3 = runtime.safeCall(Predef.assert(tmp2));
      tmp4 = acc + x7;
      return (tmp3 , tmp4)
    });
    tmp = lambda;
    tmp1 = runtime.safeCall(Predef.fold(tmp));
    return runtime.safeCall(tmp1(...xs4))
  } 
  static stringStartsWith(string, prefix) {
    return runtime.safeCall(string.startsWith(prefix))
  } 
  static stringGet(string1, i2) {
    return runtime.safeCall(string1.at(i2))
  } 
  static stringDrop(string2, n) {
    return runtime.safeCall(string2.slice(n))
  } 
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, lambda;
    tmp = got < expected;
    tmp1 = got > expected;
    tmp2 = isUB && tmp1;
    scrut = tmp || tmp2;
    if (scrut === true) {
      scrut1 = functionName.length > 0;
      if (scrut1 === true) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      name = tmp4;
      lambda = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp5 = runtime.safeCall(Predef.fold(lambda));
      if (isUB === true) {
        tmp6 = "";
      } else {
        tmp6 = "at least ";
      }
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp7 = "";
      } else {
        tmp7 = "s";
      }
      tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
      throw globalThis.Error(tmp8);
    } else {
      return runtime.Unit
    }
  } 
  static enterHandleBlock(handler, body) {
    return Runtime.enterHandleBlock(handler, body)
  } 
  static raiseUnhandledEffect() {
    return Runtime.mkEffect(Runtime.FatalEffect, null)
  }
  static toString() { return "Predef"; }
};
let Predef = Predef1; export default Predef;
