import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
import Rendering from "./Rendering.mjs";
let Predef1;
(class Predef {
  static {
    Predef1 = Predef;
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
  static pipeIntoHi(x4, f3) {
    return runtime.safeCall(f3(x4))
  } 
  static pipeFromHi(f4, x5) {
    return runtime.safeCall(f4(x5))
  } 
  static tap(x6, f5) {
    let tmp;
    tmp = runtime.safeCall(f5(x6));
    return (tmp , x6)
  } 
  static pat(f6, x7) {
    let tmp;
    tmp = runtime.safeCall(f6(x7));
    return (tmp , x7)
  } 
  static andThen(f7, g) {
    return (x8) => {
      let tmp;
      tmp = runtime.safeCall(f7(x8));
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f8, g1) {
    return (x8) => {
      let tmp;
      tmp = runtime.safeCall(g1(x8));
      return runtime.safeCall(f8(tmp))
    }
  } 
  static passTo(receiver, f9) {
    return (...args1) => {
      return runtime.safeCall(f9(receiver, ...args1))
    }
  } 
  static passToLo(receiver1, f10) {
    return (...args1) => {
      return runtime.safeCall(f10(receiver1, ...args1))
    }
  } 
  static call(receiver2, f11) {
    return (...args1) => {
      return f11.call(receiver2, ...args1)
    }
  } 
  static print(...xs) {
    let tmp, tmp1;
    tmp = runtime.safeCall(Predef.map(Predef.renderAsStr));
    tmp1 = runtime.safeCall(tmp(...xs));
    return runtime.safeCall(globalThis.console.log(...tmp1))
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
  static foldr(f12) {
    return (first, ...rest) => {
      let len, i, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp = len - 1;
        i = tmp;
        tmp1 = runtime.safeCall(rest.at(i));
        init = tmp1;
        tmp6: while (true) {
          scrut = i > 0;
          if (scrut === true) {
            tmp2 = i - 1;
            i = tmp2;
            tmp3 = runtime.safeCall(rest.at(i));
            tmp4 = runtime.safeCall(f12(tmp3, init));
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6;
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f12(first, init))
      }
    }
  } 
  static mkStr(...xs2) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (acc, x8) {
      let tmp2, tmp3, tmp4;
      if (typeof x8 === 'string') {
        tmp2 = true;
      } else {
        tmp2 = false;
      }
      tmp3 = runtime.safeCall(Predef.assert(tmp2));
      tmp4 = acc + x8;
      return (tmp3 , tmp4)
    });
    tmp = lambda;
    tmp1 = runtime.safeCall(Predef.fold(tmp));
    return runtime.safeCall(tmp1(...xs2))
  } 
  static enterHandleBlock(handler, body) {
    return Runtime.enterHandleBlock(handler, body)
  } 
  static raiseUnhandledEffect() {
    return Runtime.mkEffect(Runtime.FatalEffect, null)
  }
  static toString() { return "Predef"; }
});
let Predef = Predef1; export default Predef;
