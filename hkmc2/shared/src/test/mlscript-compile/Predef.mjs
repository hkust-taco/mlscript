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
        this.definitionMetadata = RuntimeJS.symbols.definitionMetadata;
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
  static equals(a, b) {
    let scrut, scrut1, scrut2, ac, scrut3, md, scrut4, scrut5, scrut6, scrut7, scrut8, scrut9, scrut10, scrut11, tmp, lambda, lambda1, tmp1, tmp2, tmp3;
    split_root$: {
      split_1$: {
        scrut = a === b;
        switch (scrut) {
          case true:
            tmp = true;
            break split_root$;
            break;
          default:
            if (a instanceof globalThis.Array) {
              if (b instanceof globalThis.Array) {
                scrut1 = a.length === b.length;
                switch (scrut1) {
                  case true:
                    lambda = (undefined, function (a1, i) {
                      let tmp4;
                      tmp4 = runtime.safeCall(b.at(i));
                      return Predef.equals(a1, tmp4)
                    });
                    tmp = runtime.safeCall(a.every(lambda));
                    break split_root$;
                    break;
                  default:
                    break split_1$;
                    break;
                }
              } else {
                break split_1$
              }
            } else {
              break split_1$
            }
            break;
        }
      }
      split_root$1: {
        split_1$1: {
          scrut2 = a !== undefined;
          switch (scrut2) {
            case true:
              scrut11 = a !== null;
              switch (scrut11) {
                case true:
                  scrut10 = b !== undefined;
                  switch (scrut10) {
                    case true:
                      scrut9 = b !== null;
                      switch (scrut9) {
                        case true:
                          ac = a.constructor;
                          split_root$2: {
                            split_1$2: {
                              scrut3 = ac !== undefined;
                              switch (scrut3) {
                                case true:
                                  scrut7 = ac === b.constructor;
                                  switch (scrut7) {
                                    case true:
                                      md = ac[Predef.Symbols.definitionMetadata];
                                      split_root$3: {
                                        split_1$3: {
                                          scrut4 = md !== undefined;
                                          switch (scrut4) {
                                            case true:
                                              lambda1 = (undefined, function (field) {
                                                let scrut12, scrut13, tmp4;
                                                split_root$4: {
                                                  split_1$4: {
                                                    scrut12 = field !== null;
                                                    switch (scrut12) {
                                                      case true:
                                                        scrut13 = Predef.equals(a[field], b[field]);
                                                        switch (scrut13) {
                                                          case true:
                                                            tmp4 = true;
                                                            break split_root$4;
                                                            break;
                                                          default:
                                                            break split_1$4;
                                                            break;
                                                        }
                                                        break;
                                                      default:
                                                        break split_1$4;
                                                        break;
                                                    }
                                                  }
                                                  tmp4 = false;
                                                }
                                                return tmp4
                                              });
                                              scrut5 = runtime.safeCall(md[2].every(lambda1));
                                              switch (scrut5) {
                                                case true:
                                                  tmp1 = true;
                                                  break split_root$3;
                                                  break;
                                                default:
                                                  break split_1$3;
                                                  break;
                                              }
                                              break;
                                            default:
                                              break split_1$3;
                                              break;
                                          }
                                        }
                                        tmp1 = false;
                                      }
                                      scrut6 = tmp1;
                                      switch (scrut6) {
                                        case true:
                                          tmp2 = true;
                                          break split_root$2;
                                          break;
                                        default:
                                          break split_1$2;
                                          break;
                                      }
                                      break;
                                    default:
                                      break split_1$2;
                                      break;
                                  }
                                  break;
                                default:
                                  break split_1$2;
                                  break;
                              }
                            }
                            tmp2 = false;
                          }
                          scrut8 = tmp2;
                          switch (scrut8) {
                            case true:
                              tmp3 = true;
                              break split_root$1;
                              break;
                            default:
                              break split_1$1;
                              break;
                          }
                          break;
                        default:
                          break split_1$1;
                          break;
                      }
                      break;
                    default:
                      break split_1$1;
                      break;
                  }
                  break;
                default:
                  break split_1$1;
                  break;
              }
              break;
            default:
              break split_1$1;
              break;
          }
        }
        tmp3 = false;
      }
      tmp = tmp3;
    }
    return tmp
  } 
  static nequals(a, b) {
    let tmp;
    tmp = Predef.equals(a, b);
    return ! tmp
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
      scrut = len === 0;
      switch (scrut) {
        case true:
          return first;
          break;
        default:
          i = len - 1;
          init = runtime.safeCall(rest.at(i));
          tmp4: while (true) {
            scrut1 = i > 0;
            switch (scrut1) {
              case true:
                tmp = i - 1;
                i = tmp;
                tmp1 = runtime.safeCall(rest.at(i));
                tmp2 = runtime.safeCall(f(tmp1, init));
                init = tmp2;
                tmp3 = runtime.Unit;
                continue tmp4;
                break;
              default:
                tmp3 = runtime.Unit;
                break;
            }
            break;
          }
          return runtime.safeCall(f(first, init));
          break;
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
