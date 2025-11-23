const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Runtime from "./Runtime.mjs";
import Rendering from "./Rendering.mjs";
let Predef1;
globalThis.Object.freeze(class Predef {
  static {
    Predef1 = this
  }
  constructor() {
    runtime.Unit;
  }
  static {
    globalThis.Object.freeze(class Symbols {
      static {
        Predef.Symbols = globalThis.Object.freeze(new this)
      }
      constructor() {
        this.prettyPrint = RuntimeJS.symbols.prettyPrint;
        Object.defineProperty(this, "class", {
          value: Symbols
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Symbols"]; 
    });
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
  static apply(f, ...args) {
    return runtime.safeCall(f(...args))
  } 
  static pipeInto(x, f) {
    return runtime.safeCall(f(x))
  } 
  static pipeFrom(f, x) {
    return runtime.safeCall(f(x))
  } 
  static pipeIntoHi(x, f) {
    return runtime.safeCall(f(x))
  } 
  static pipeFromHi(f, x) {
    return runtime.safeCall(f(x))
  } 
  static tap(x, f) {
    let tmp;
    tmp = runtime.safeCall(f(x));
    return (tmp , x)
  } 
  static pat(f, x) {
    let tmp;
    tmp = runtime.safeCall(f(x));
    return (tmp , x)
  } 
  static alsoDo(x, eff) {
    return x
  } 
  static andThen(f, g) {
    return (x) => {
      let tmp;
      tmp = runtime.safeCall(f(x));
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f, g) {
    return (x) => {
      let tmp;
      tmp = runtime.safeCall(g(x));
      return runtime.safeCall(f(tmp))
    }
  } 
  static passTo(receiver, f) {
    return (...args) => {
      return runtime.safeCall(f(receiver, ...args))
    }
  } 
  static passToLo(receiver, f) {
    return (...args) => {
      return runtime.safeCall(f(receiver, ...args))
    }
  } 
  static call(receiver, f) {
    return (...args) => {
      return f.call(receiver, ...args)
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
    throw globalThis.Error(tmp)
  } 
  static get notImplementedError() {
    throw globalThis.Error("Not implemented");
  } 
  static tuple(...xs) {
    return xs
  } 
  static foldr(f) {
    return (first, ...rest) => {
      let len, scrut, i, init, scrut1, tmp, tmp1, tmp2, tmp3;
      len = rest.length;
      scrut = len == 0;
      if (scrut === true) {
        return first
      } else {
        i = len - 1;
        init = runtime.safeCall(rest.at(i));
        tmp4: while (true) {
          scrut1 = i > 0;
          if (scrut1 === true) {
            tmp = i - 1;
            i = tmp;
            tmp1 = runtime.safeCall(rest.at(i));
            tmp2 = runtime.safeCall(f(tmp1, init));
            init = tmp2;
            tmp3 = runtime.Unit;
            continue tmp4
          } else {
            tmp3 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f(first, init))
      }
    }
  } 
  static mkStr(...xs) {
    let lambda, tmp;
    lambda = (undefined, function (acc, x) {
      let tmp1, tmp2, tmp3;
      if (typeof x === 'string') {
        tmp1 = true;
      } else {
        tmp1 = false;
      }
      tmp2 = runtime.safeCall(Predef.assert(tmp1));
      tmp3 = acc + x;
      return (tmp2 , tmp3)
    });
    tmp = runtime.safeCall(Predef.fold(lambda));
    return runtime.safeCall(tmp(...xs))
  } 
  static use(instance) {
    return instance
  } 
  static enterHandleBlock(handler, body) {
    return Runtime.enterHandleBlock(handler, body)
  } 
  static raiseUnhandledEffect() {
    return Runtime.mkEffect(Runtime.FatalEffect, null)
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Predef"]; 
});
let Predef = Predef1; export default Predef;
