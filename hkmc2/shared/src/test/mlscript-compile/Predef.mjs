const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Runtime from "./Runtime.mjs";
import Rendering from "./Rendering.mjs";
let Predef1;
(class Predef {
  static {
    Predef1 = Predef;
    const Symbols$class = class Symbols {
      constructor() {
        this.prettyPrint = RuntimeJS.symbols.prettyPrint;
        Object.defineProperty(this, "class", {
          value: Symbols
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Symbols"]; 
    };
    this.Symbols = globalThis.Object.freeze(new Symbols$class);
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
            tmp4 = runtime.safeCall(f(tmp3, init));
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f(first, init))
      }
    }
  } 
  static mkStr(...xs) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (acc, x) {
      let tmp2, tmp3, tmp4;
      if (typeof x === 'string') {
        tmp2 = true;
      } else {
        tmp2 = false;
      }
      tmp3 = runtime.safeCall(Predef.assert(tmp2));
      tmp4 = acc + x;
      return (tmp3 , tmp4)
    });
    tmp = lambda;
    tmp1 = runtime.safeCall(Predef.fold(tmp));
    return runtime.safeCall(tmp1(...xs))
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
  static toString() { return runtime.render(this); }
  static [definitionMetadata] = ["module", "Predef"]; 
});
let Predef = Predef1; export default Predef;
