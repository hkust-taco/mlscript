import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import Runtime from "./Runtime.mjs";
import Rendering from "./Rendering.mjs";
let definitionMetadata, Predef1, tmp;
tmp = globalThis.Symbol.for("mlscript.definitionMetadata");
definitionMetadata = tmp;
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
    let tmp1;
    tmp1 = runtime.safeCall(f5(x6));
    return (tmp1 , x6)
  } 
  static pat(f6, x7) {
    let tmp1;
    tmp1 = runtime.safeCall(f6(x7));
    return (tmp1 , x7)
  } 
  static alsoDo(x8, eff) {
    return x8
  } 
  static andThen(f7, g) {
    return (x9) => {
      let tmp1;
      tmp1 = runtime.safeCall(f7(x9));
      return runtime.safeCall(g(tmp1))
    }
  } 
  static compose(f8, g1) {
    return (x9) => {
      let tmp1;
      tmp1 = runtime.safeCall(g1(x9));
      return runtime.safeCall(f8(tmp1))
    }
  } 
  static passTo(receiver, f9) {
    return (...args1) => {
      return runtime.safeCall(f9(receiver, ...args1))
    }
  } 
  static passTo2(receiver1, f10) {
    return (...args1) => {
      return runtime.safeCall(f10(receiver1, ...args1))
    }
  } 
  static passToLo(receiver2, f11) {
    return (...args1) => {
      return runtime.safeCall(f11(receiver2, ...args1))
    }
  } 
  static call(receiver3, f12) {
    return (...args1) => {
      return f12.call(receiver3, ...args1)
    }
  } 
  static print(...xs) {
    let tmp1, tmp2;
    tmp1 = runtime.safeCall(Predef.map(Predef.renderAsStr));
    tmp2 = runtime.safeCall(tmp1(...xs));
    return runtime.safeCall(globalThis.console.log(...tmp2))
  } 
  static renderAsStr(arg) {
    if (typeof arg === 'string') {
      return arg
    } else {
      return runtime.safeCall(Predef.render(arg))
    }
  } 
  static notImplemented(msg) {
    let tmp1;
    tmp1 = "Not implemented: " + msg;
    throw globalThis.Error(tmp1);
  } 
  static get notImplementedError() {
    throw globalThis.Error("Not implemented");
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static foldr(f13) {
    return (first, ...rest) => {
      let len, i, init, scrut, scrut1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp1 = len - 1;
        i = tmp1;
        tmp2 = runtime.safeCall(rest.at(i));
        init = tmp2;
        tmp7: while (true) {
          scrut = i > 0;
          if (scrut === true) {
            tmp3 = i - 1;
            i = tmp3;
            tmp4 = runtime.safeCall(rest.at(i));
            tmp5 = runtime.safeCall(f13(tmp4, init));
            init = tmp5;
            tmp6 = runtime.Unit;
            continue tmp7;
          } else {
            tmp6 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f13(first, init))
      }
    }
  } 
  static mkStr(...xs2) {
    let tmp1, tmp2, lambda;
    lambda = (undefined, function (acc, x9) {
      let tmp3, tmp4, tmp5;
      if (typeof x9 === 'string') {
        tmp3 = true;
      } else {
        tmp3 = false;
      }
      tmp4 = runtime.safeCall(Predef.assert(tmp3));
      tmp5 = acc + x9;
      return (tmp4 , tmp5)
    });
    tmp1 = lambda;
    tmp2 = runtime.safeCall(Predef.fold(tmp1));
    return runtime.safeCall(tmp2(...xs2))
  } 
  static enterHandleBlock(handler, body) {
    return Runtime.enterHandleBlock(handler, body)
  } 
  static raiseUnhandledEffect() {
    return Runtime.mkEffect(Runtime.FatalEffect, null)
  } 
  static use(instance) {
    return instance
  }
  static [definitionMetadata] = ["module", "Predef"]; 
});
let Predef = Predef1; export default Predef;
