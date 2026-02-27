const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let Runtime1;
(class Runtime {
  static {
    Runtime1 = this
  }
  constructor() {
    runtime.Unit;
  }
  static #curEffect;
  static #resumeValue;
  static #resumeArr;
  static #resumeIdx;
  static #resumePc;
  static #stackLimit;
  static #stackDepth;
  static #stackHandler;
  static #stackResume;
  static get curEffect() { return Runtime.#curEffect; }
  static set curEffect(value) { Runtime.#curEffect = value; }
  static get resumeValue() { return Runtime.#resumeValue; }
  static set resumeValue(value) { Runtime.#resumeValue = value; }
  static get resumeArr() { return Runtime.#resumeArr; }
  static set resumeArr(value) { Runtime.#resumeArr = value; }
  static get resumeIdx() { return Runtime.#resumeIdx; }
  static set resumeIdx(value) { Runtime.#resumeIdx = value; }
  static get resumePc() { return Runtime.#resumePc; }
  static set resumePc(value) { Runtime.#resumePc = value; }
  static get stackLimit() { return Runtime.#stackLimit; }
  static set stackLimit(value) { Runtime.#stackLimit = value; }
  static get stackDepth() { return Runtime.#stackDepth; }
  static set stackDepth(value) { Runtime.#stackDepth = value; }
  static get stackHandler() { return Runtime.#stackHandler; }
  static set stackHandler(value) { Runtime.#stackHandler = value; }
  static get stackResume() { return Runtime.#stackResume; }
  static set stackResume(value) { Runtime.#stackResume = value; }
  static {
    let tmp;
    (class Unit {
      static {
        new this
      }
      constructor() {
        Runtime.Unit = this;
        Object.defineProperty(this, "class", {
          value: Unit
        });
        globalThis.Object.freeze(this);
      }
      toString() {
        return "()"
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["object", "Unit"]; 
    });
    (class LoopEnd {
      static {
        new this
      }
      constructor() {
        Runtime.LoopEnd = this;
        Object.defineProperty(this, "class", {
          value: LoopEnd
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "LoopEnd"]; 
    });
    this.short_and = RuntimeJS.short_and;
    this.short_or = RuntimeJS.short_or;
    this.bitand = RuntimeJS.bitand;
    this.bitnot = RuntimeJS.bitnot;
    this.bitor = RuntimeJS.bitor;
    this.shl = RuntimeJS.shl;
    this.try_catch = RuntimeJS.try_catch;
    this.EffectHandle = function EffectHandle(_reified) {
      return globalThis.Object.freeze(new EffectHandle.class(_reified));
    };
    (class EffectHandle {
      static {
        Runtime.EffectHandle.class = this
      }
      constructor(_reified) {
        this.#_reified = _reified;
        this.reified = this.#_reified;
      }
      #_reified;
      resumeWith(value) {
        let lambda;
        const this$EffectHandle = this;
        lambda = (undefined, function () {
          let tmp1;
          tmp1 = Runtime.resume(this$EffectHandle.reified.contTrace);
          return runtime.safeCall(tmp1(value))
        });
        return Runtime1.try(lambda)
      } 
      raise() {
        Runtime.curEffect = this.reified;
        return runtime.Unit
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectHandle", [null]]; 
    });
    this.MatchSuccess = function MatchSuccess(output, bindings) {
      return globalThis.Object.freeze(new MatchSuccess.class(output, bindings));
    };
    (class MatchSuccess {
      static {
        Runtime.MatchSuccess.class = this
      }
      constructor(output, bindings) {
        this.output = output;
        this.bindings = bindings;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "MatchSuccess", ["output", "bindings"]]; 
    });
    this.MatchFailure = function MatchFailure(errors) {
      return globalThis.Object.freeze(new MatchFailure.class(errors));
    };
    (class MatchFailure {
      static {
        Runtime.MatchFailure.class = this
      }
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "MatchFailure", ["errors"]]; 
    });
    (class Tuple {
      static {
        Runtime.Tuple = this
      }
      constructor() {
        runtime.Unit;
      }
      static {
        this.split = LazyArray.__split;
      }
      static slice(xs, i, j) {
        let tmp1;
        tmp1 = xs.length - j;
        return xs.slice(i, tmp1)
      } 
      static lazySlice(xs, i, j) {
        let tmp1;
        tmp1 = LazyArray.dropLeftRight(i, j);
        return runtime.safeCall(tmp1(xs))
      } 
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      } 
      static get(xs, i) {
        let scrut, scrut1, tmp1, tmp2, tmp3;
        scrut = i >= xs.length;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: index out of bounds"))
        } else {
          tmp1 = runtime.Unit;
        }
        tmp2 = - xs.length;
        scrut1 = i < tmp2;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: negative index out of bounds"))
        } else {
          tmp3 = runtime.Unit;
        }
        return xs.at(i)
      } 
      static isArrayLike(xs) {
        return runtime.safeCall(Iter.isArrayLike(xs))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Tuple"]; 
    });
    (class Str {
      static {
        Runtime.Str = this
      }
      constructor() {
        runtime.Unit;
      }
      static startsWith(string, prefix) {
        return runtime.safeCall(string.startsWith(prefix))
      } 
      static get(string, i) {
        let scrut;
        scrut = i >= string.length;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Str.get: index out of bounds"))
        } else {
          return runtime.safeCall(string.at(i))
        }
      } 
      static take(string, n) {
        return string.slice(0, n)
      } 
      static leave(string, n) {
        return runtime.safeCall(string.slice(n))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Str"]; 
    });
    this.render = Rendering.render;
    (class TraceLogger {
      static {
        Runtime.TraceLogger = this
      }
      constructor() {
        runtime.Unit;
      }
      static #enabled;
      static #indentLvl;
      static get enabled() { return TraceLogger.#enabled; }
      static set enabled(value) { TraceLogger.#enabled = value; }
      static get indentLvl() { return TraceLogger.#indentLvl; }
      static set indentLvl(value) { TraceLogger.#indentLvl = value; }
      static {
        this.enabled = false;
        this.indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp1;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp1 = prev + 1;
          TraceLogger.indentLvl = tmp1;
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
        let scrut, tmp1, tmp2, tmp3, tmp4, tmp5;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp1 = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          tmp2 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          tmp3 = "\n" + tmp2;
          tmp4 = msg.replaceAll("\n", tmp3);
          tmp5 = tmp1 + tmp4;
          return runtime.safeCall(globalThis.console.log(tmp5))
        } else {
          return runtime.Unit
        }
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "TraceLogger"]; 
    });
    this.curEffect = null;
    this.resumeValue = null;
    this.resumeArr = null;
    this.resumeIdx = null;
    tmp = - 1;
    this.resumePc = tmp;
    (class FatalEffect {
      static {
        new this
      }
      constructor() {
        Runtime.FatalEffect = this;
        Object.defineProperty(this, "class", {
          value: FatalEffect
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "FatalEffect"]; 
    });
    (class PrintStackEffect {
      static {
        new this
      }
      constructor() {
        Runtime.PrintStackEffect = this;
        Object.defineProperty(this, "class", {
          value: PrintStackEffect
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "PrintStackEffect"]; 
    });
    this.FunctionContFrame = function FunctionContFrame(next, saved) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next, saved));
    };
    (class FunctionContFrame {
      static {
        Runtime.FunctionContFrame.class = this
      }
      constructor(next, saved) {
        this.next = next;
        this.saved = saved;
      }
      resume(value) {
        let i, f, argListsLength, currentArgList, scrut, argListLength, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
        i = 0;
        f = this.saved.at(0);
        argListsLength = this.saved.at(5);
        currentArgList = 6;
        Runtime.resumeValue = value;
        Runtime.resumeArr = this.saved;
        Runtime.resumePc = this.saved.at(1);
        scrut = argListsLength === 0;
        if (scrut === true) {
          tmp1 = runtime.safeCall(globalThis.console.log("cannot resume getters"));
        } else {
          tmp1 = runtime.Unit;
        }
        lbl: while (true) {
          let scrut1, argListLength1, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
          tmp9 = argListsLength - 1;
          scrut1 = i < tmp9;
          if (scrut1 === true) {
            argListLength1 = this.saved.at(currentArgList);
            tmp10 = currentArgList + 1;
            tmp11 = currentArgList + 1;
            tmp12 = tmp11 + argListLength1;
            tmp13 = this.saved.slice(tmp10, tmp12);
            tmp14 = f.apply(this.saved.at(4), tmp13);
            f = tmp14;
            tmp15 = argListLength1 + 1;
            tmp16 = currentArgList + tmp15;
            currentArgList = tmp16;
            tmp17 = i + 1;
            i = tmp17;
            tmp2 = runtime.Unit;
            continue lbl
          } else {
            tmp2 = runtime.Unit;
          }
          break;
        }
        argListLength = this.saved.at(currentArgList);
        tmp3 = currentArgList + argListLength;
        tmp4 = tmp3 + 2;
        Runtime.resumeIdx = tmp4;
        tmp5 = currentArgList + 1;
        tmp6 = currentArgList + 1;
        tmp7 = tmp6 + argListLength;
        tmp8 = this.saved.slice(tmp5, tmp7);
        return f.apply(this.saved.at(4), tmp8)
      } 
      get getLocals() {
        let debugInfo, i, cur, res, i1, tmp1, tmp2;
        debugInfo = this.saved.at(3);
        i = 0;
        cur = 6;
        lbl: while (true) {
          let scrut, tmp3, tmp4, tmp5;
          scrut = i < this.saved.at(5);
          if (scrut === true) {
            tmp3 = this.saved.at(cur) + 1;
            tmp4 = cur + tmp3;
            cur = tmp4;
            tmp5 = i + 1;
            i = tmp5;
            tmp1 = runtime.Unit;
            continue lbl
          } else {
            tmp1 = runtime.Unit;
          }
          break;
        }
        res = [];
        i1 = 1;
        lbl1: while (true) {
          let scrut1, tmp6, tmp7, tmp8, tmp9, tmp10;
          scrut1 = i1 < debugInfo.length;
          if (scrut1 === true) {
            tmp6 = i1 + 1;
            tmp7 = cur + 1;
            tmp8 = tmp7 + debugInfo.at(i1);
            tmp9 = globalThis.Object.freeze(new Runtime.LocalVarInfo.class(debugInfo.at(tmp6), this.saved.at(tmp8)));
            runtime.safeCall(res.push(tmp9));
            tmp10 = i1 + 2;
            i1 = tmp10;
            tmp2 = runtime.Unit;
            continue lbl1
          } else {
            tmp2 = runtime.Unit;
          }
          break;
        }
        return res;
      } 
      get getNme() {
        return this.saved.at(3).at(0);
      } 
      get getLoc() {
        let loc;
        loc = this.saved.at(2);
        if (loc === null) {
          return "pc=" + this.saved.at(1)
        } else {
          return loc
        }
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunctionContFrame", ["next", "saved"]]; 
    });
    this.HandlerContFrame = function HandlerContFrame(next, nextHandler, handler) {
      return globalThis.Object.freeze(new HandlerContFrame.class(next, nextHandler, handler));
    };
    (class HandlerContFrame {
      static {
        Runtime.HandlerContFrame.class = this
      }
      constructor(next, nextHandler, handler) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.handler = handler;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "HandlerContFrame", ["next", "nextHandler", "handler"]]; 
    });
    this.ContTrace = function ContTrace(next, last, nextHandler, lastHandler, resumed) {
      return globalThis.Object.freeze(new ContTrace.class(next, last, nextHandler, lastHandler, resumed));
    };
    (class ContTrace {
      static {
        Runtime.ContTrace.class = this
      }
      constructor(next, last, nextHandler, lastHandler, resumed) {
        this.next = next;
        this.last = last;
        this.nextHandler = nextHandler;
        this.lastHandler = lastHandler;
        this.resumed = resumed;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "ContTrace", ["next", "last", "nextHandler", "lastHandler", "resumed"]]; 
    });
    this.EffectSig = function EffectSig(contTrace, handler, handlerFun) {
      return globalThis.Object.freeze(new EffectSig.class(contTrace, handler, handlerFun));
    };
    (class EffectSig {
      static {
        Runtime.EffectSig.class = this
      }
      constructor(contTrace, handler, handlerFun) {
        this.contTrace = contTrace;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectSig", ["contTrace", "handler", "handlerFun"]]; 
    });
    (class NonLocalReturn {
      static {
        Runtime.NonLocalReturn = this
      }
      constructor() {}
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "NonLocalReturn"]; 
    });
    this.FnLocalsInfo = function FnLocalsInfo(fnName, locals) {
      return globalThis.Object.freeze(new FnLocalsInfo.class(fnName, locals));
    };
    (class FnLocalsInfo {
      static {
        Runtime.FnLocalsInfo.class = this
      }
      constructor(fnName, locals) {
        this.fnName = fnName;
        this.locals = locals;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FnLocalsInfo", ["fnName", "locals"]]; 
    });
    this.LocalVarInfo = function LocalVarInfo(localName, value) {
      return globalThis.Object.freeze(new LocalVarInfo.class(localName, value));
    };
    (class LocalVarInfo {
      static {
        Runtime.LocalVarInfo.class = this
      }
      constructor(localName, value) {
        this.localName = localName;
        this.value = value;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "LocalVarInfo", ["localName", "value"]]; 
    });
    this.CustomStackError = function CustomStackError(stack) {
      return globalThis.Object.freeze(new CustomStackError.class(stack));
    };
    (class CustomStackError {
      static {
        Runtime.CustomStackError.class = this
      }
      constructor(stack) {
        this.stack = stack;
      }
      toString() {
        return this.stack
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["class", "CustomStackError", ["stack"]]; 
    });
    this.stackLimit = 0;
    this.stackDepth = 0;
    this.stackHandler = null;
    this.stackResume = null;
    (class StackDelayHandler {
      static {
        new this
      }
      constructor() {
        Runtime.StackDelayHandler = this;
        Object.defineProperty(this, "class", {
          value: StackDelayHandler
        });
        globalThis.Object.freeze(this);
      }
      delay() {
        let lambda;
        lambda = (undefined, function (k) {
          Runtime.stackResume = k;
          return runtime.Unit
        });
        return Runtime.mkEffect(this, lambda)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "StackDelayHandler"]; 
    });
    this.Int31 = function Int31(v) {
      return globalThis.Object.freeze(new Int31.class(v));
    };
    (class Int31 {
      static {
        Runtime.Int31.class = this
      }
      constructor(v) {
        this.#v = v;
      }
      #v;
      zext() {
        let tmp1, tmp2;
        tmp1 = Runtime.shl(1, 31);
        tmp2 = runtime.safeCall(Runtime.bitnot(tmp1));
        return Runtime.bitand(this.#v, tmp2)
      } 
      sext() {
        let tmp1;
        tmp1 = Runtime.shl(1, 31);
        return Runtime.bitor(this.#v, tmp1)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Int31", [null]]; 
    });
  }
  static get unreachable() {
    throw runtime.safeCall(globalThis.Error("unreachable"));
  } 
  static assertFail(file, line) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = "Assertion failed (" + file;
    tmp1 = tmp + ":";
    tmp2 = tmp1 + line;
    tmp3 = tmp2 + ")";
    throw runtime.safeCall(globalThis.Error(tmp3))
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, lambda, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    tmp = got < expected;
    lambda = (undefined, function () {
      let lambda1;
      lambda1 = (undefined, function () {
        return got > expected
      });
      return runtime.short_and(isUB, lambda1)
    });
    scrut = runtime.short_or(tmp, lambda);
    if (scrut === true) {
      scrut1 = functionName.length > 0;
      if (scrut1 === true) {
        tmp1 = " '" + functionName;
        tmp2 = tmp1 + "'";
      } else {
        tmp2 = "";
      }
      name = tmp2;
      tmp3 = "Function" + name;
      tmp4 = tmp3 + " expected ";
      if (isUB === true) {
        tmp5 = "";
      } else {
        tmp5 = "at least ";
      }
      tmp6 = tmp4 + tmp5;
      tmp7 = tmp6 + expected;
      tmp8 = tmp7 + " argument";
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp9 = "";
      } else {
        tmp9 = "s";
      }
      tmp10 = tmp8 + tmp9;
      tmp11 = tmp10 + " but got ";
      tmp12 = tmp11 + got;
      throw runtime.safeCall(globalThis.Error(tmp12))
    } else {
      return runtime.Unit
    }
  } 
  static safeCall(x) {
    if (x === undefined) {
      return runtime.Unit
    } else {
      return x
    }
  } 
  static checkCall(x) {
    if (x === undefined) {
      throw runtime.safeCall(globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value."))
    } else {
      return x
    }
  } 
  static deboundMethod(mtdName, clsName) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = "[debinding error] Method '" + mtdName;
    tmp1 = tmp + "' of class '";
    tmp2 = tmp1 + clsName;
    tmp3 = tmp2 + "' was accessed without being called.";
    throw runtime.safeCall(globalThis.Error(tmp3))
  } 
  static try(f) {
    let res, scrut, tmp;
    res = runtime.safeCall(f());
    scrut = Runtime.curEffect !== null;
    if (scrut === true) {
      tmp = Runtime.curEffect;
      Runtime.curEffect = null;
      return Runtime.EffectHandle(tmp)
    } else {
      return res
    }
  } 
  static printRaw(x) {
    let rcd, tmp;
    rcd = globalThis.Object.freeze({
      indent: 2,
      breakLength: 76
    });
    tmp = Runtime.render(x, rcd);
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static raisePrintStackEffect(showLocals) {
    return Runtime.mkEffect(Runtime.PrintStackEffect, showLocals)
  } 
  static topLevelEffect(debug) {
    let tr, v, tmp, tmp1, tmp2;
    tr = Runtime.curEffect;
    v = null;
    lbl: while (true) {
      let scrut, tmp3, tmp4, tmp5;
      split_root$: {
        split_1$: {
          if (tr instanceof Runtime.EffectSig.class) {
            scrut = tr.handler === Runtime.PrintStackEffect;
            if (scrut === true) {
              tmp3 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
              runtime.safeCall(globalThis.console.log(tmp3));
              Runtime.curEffect = null;
              tmp4 = Runtime.resume(tr.contTrace);
              tmp5 = runtime.safeCall(tmp4(runtime.Unit));
              v = tmp5;
              tr = Runtime.curEffect;
              tmp = runtime.Unit;
              continue lbl
            } else {
              break split_1$
            }
          } else {
            break split_1$
          }
        }
        tmp = runtime.Unit;
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      Runtime.curEffect = null;
      tmp1 = "Error: Unhandled effect " + tr.handler.constructor.name;
      tmp2 = Runtime.showStackTrace(tmp1, tr, debug, false);
      throw Runtime.CustomStackError(tmp2)
    } else {
      return v
    }
  } 
  static illegalEffect(position) {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Runtime.curEffect;
    Runtime.curEffect = null;
    tmp1 = "Error: Effect " + tmp.handler.constructor.name;
    tmp2 = tmp1 + " is raised ";
    tmp3 = tmp2 + position;
    tmp4 = Runtime.showStackTrace(tmp3, tmp, false, false);
    throw Runtime.CustomStackError(tmp4)
  } 
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail, tmp, tmp1, tmp2, tmp3;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      lbl: while (true) {
        let scrut, cur, scrut1, tmp4, tmp5, tmp6, tmp7;
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          lbl1: while (true) {
            let scrut2, curLocals, loc, localsMsg, scrut3, lambda, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
            scrut2 = cur !== null;
            if (scrut2 === true) {
              curLocals = cur.getLocals;
              loc = cur.getLoc;
              split_root$: {
                split_1$: {
                  if (showLocals === true) {
                    scrut3 = curLocals.length > 0;
                    if (scrut3 === true) {
                      lambda = (undefined, function (l) {
                        let tmp17, tmp18;
                        tmp17 = l.localName + "=";
                        tmp18 = Rendering.render(l.value);
                        return tmp17 + tmp18
                      });
                      tmp8 = runtime.safeCall(curLocals.map(lambda));
                      tmp9 = runtime.safeCall(tmp8.join(", "));
                      tmp10 = " with locals: " + tmp9;
                      break split_root$
                    } else {
                      break split_1$
                    }
                  } else {
                    break split_1$
                  }
                }
                tmp10 = "";
              }
              localsMsg = tmp10;
              tmp11 = "\n\tat " + cur.getNme;
              tmp12 = tmp11 + " (";
              tmp13 = tmp12 + loc;
              tmp14 = tmp13 + ")";
              tmp15 = msg + tmp14;
              msg = tmp15;
              tmp16 = msg + localsMsg;
              msg = tmp16;
              cur = cur.next;
              atTail = false;
              tmp4 = runtime.Unit;
              continue lbl1
            } else {
              tmp4 = runtime.Unit;
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut1 = curHandler !== null;
          if (scrut1 === true) {
            tmp5 = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp6 = msg + tmp5;
            msg = tmp6;
            atTail = false;
            tmp7 = runtime.Unit;
          } else {
            tmp7 = runtime.Unit;
          }
          tmp = tmp7;
          continue lbl
        } else {
          tmp = runtime.Unit;
        }
        break;
      }
      if (atTail === true) {
        tmp1 = msg + "\n\tat tail position";
        msg = tmp1;
        tmp2 = runtime.Unit;
      } else {
        tmp2 = runtime.Unit;
      }
      tmp3 = tmp2;
    } else {
      tmp3 = runtime.Unit;
    }
    return msg
  } 
  static showFunctionContChain(cont, hl, vis, reps) {
    let result, scrut, scrut1, scrut2, tmp, lambda, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont.constructor.name + "(pc=";
      result = tmp + cont.saved.at(1);
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp7, tmp8;
        scrut3 = runtime.safeCall(m.has(cont));
        if (scrut3 === true) {
          tmp7 = ", " + marker;
          tmp8 = result + tmp7;
          result = tmp8;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      runtime.safeCall(hl.forEach(lambda));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp1 = reps + 1;
        reps = tmp1;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        } else {
          tmp2 = runtime.Unit;
        }
        tmp3 = result + ", REPEAT";
        result = tmp3;
        tmp4 = runtime.Unit;
      } else {
        tmp4 = runtime.safeCall(vis.add(cont));
      }
      tmp5 = result + ") -> ";
      tmp6 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp5 + tmp6
    } else {
      scrut2 = cont === null;
      if (scrut2 === true) {
        return "(null)"
      } else {
        return "(NOT CONT)"
      }
    }
  } 
  static showHandlerContChain(cont, hl, vis, reps) {
    let result, scrut, scrut1, scrut2, lambda, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (cont instanceof Runtime.HandlerContFrame.class) {
      result = cont.handler.constructor.name;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp6, tmp7;
        scrut3 = runtime.safeCall(m.has(cont));
        if (scrut3 === true) {
          tmp6 = ", " + marker;
          tmp7 = result + tmp6;
          result = tmp7;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      runtime.safeCall(hl.forEach(lambda));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp = reps + 1;
        reps = tmp;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        } else {
          tmp1 = runtime.Unit;
        }
        tmp2 = result + ", REPEAT";
        result = tmp2;
        tmp3 = runtime.Unit;
      } else {
        tmp3 = runtime.safeCall(vis.add(cont));
      }
      tmp4 = result + " -> ";
      tmp5 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp4 + tmp5
    } else {
      scrut2 = cont === null;
      if (scrut2 === true) {
        return "(null)"
      } else {
        return "(NOT HANDLER CONT)"
      }
    }
  } 
  static debugCont(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showFunctionContChain(cont, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  } 
  static debugHandler(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showHandlerContChain(cont, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  } 
  static debugContTrace(contTrace) {
    let scrut, scrut1, vis, hl, cur, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (contTrace instanceof Runtime.ContTrace.class) {
      globalThis.console.log("resumed: ", contTrace.resumed);
      scrut = contTrace.last === contTrace;
      if (scrut === true) {
        tmp = runtime.safeCall(globalThis.console.log("<last is self>"));
      } else {
        tmp = runtime.Unit;
      }
      scrut1 = contTrace.lastHandler === contTrace;
      if (scrut1 === true) {
        tmp1 = runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      } else {
        tmp1 = runtime.Unit;
      }
      vis = globalThis.Object.freeze(new globalThis.Set());
      hl = globalThis.Object.freeze(new globalThis.Map());
      tmp2 = globalThis.Object.freeze([
        contTrace.last
      ]);
      tmp3 = globalThis.Object.freeze(new globalThis.Set(tmp2));
      hl.set("last", tmp3);
      tmp4 = globalThis.Object.freeze([
        contTrace.lastHandler
      ]);
      tmp5 = globalThis.Object.freeze(new globalThis.Set(tmp4));
      hl.set("last-handler", tmp5);
      tmp6 = Runtime.showFunctionContChain(contTrace.next, hl, vis, 0);
      runtime.safeCall(globalThis.console.log(tmp6));
      cur = contTrace.nextHandler;
      lbl: while (true) {
        let scrut2, tmp8;
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp8 = Runtime.showHandlerContChain(cur, hl, vis, 0);
          runtime.safeCall(globalThis.console.log(tmp8));
          cur = cur.nextHandler;
          tmp7 = runtime.Unit;
          continue lbl
        } else {
          tmp7 = runtime.Unit;
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    } else {
      runtime.safeCall(globalThis.console.log("Not a cont trace:"));
      return runtime.safeCall(globalThis.console.log(contTrace))
    }
  } 
  static debugEff(eff) {
    if (eff instanceof Runtime.EffectSig.class) {
      runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      globalThis.console.log("handler: ", eff.handler.constructor.name);
      globalThis.console.log("handlerFun: ", eff.handlerFun);
      return Runtime.debugContTrace(eff.contTrace)
    } else {
      runtime.safeCall(globalThis.console.log("Not an effect:"));
      return runtime.safeCall(globalThis.console.log(eff))
    }
  } 
  static unwind(...saved) {
    let tmp;
    tmp = new Runtime.FunctionContFrame.class(null, saved);
    Runtime.curEffect.contTrace.last.next = tmp;
    Runtime.curEffect.contTrace.last = Runtime.curEffect.contTrace.last.next;
    return runtime.Unit
  } 
  static mkEffect(handler, handlerFun) {
    let res, tmp;
    tmp = new Runtime.ContTrace.class(null, null, null, null, false);
    res = new Runtime.EffectSig.class(tmp, handler, handlerFun);
    res.contTrace.last = res.contTrace;
    res.contTrace.lastHandler = res.contTrace;
    Runtime.curEffect = res;
    return runtime.Unit
  } 
  static handleBlockImpl(cur, handler) {
    let handlerFrame;
    handlerFrame = new Runtime.HandlerContFrame.class(null, null, handler);
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  } 
  static enterHandleBlock(handler, body) {
    let tmp, scrut;
    tmp = runtime.safeCall(body());
    scrut = Runtime.curEffect === null;
    if (scrut === true) {
      return tmp
    } else {
      return Runtime.handleBlockImpl(Runtime.curEffect, handler)
    }
  } 
  static handleEffects(cur) {
    let tmp;
    lbl: while (true) {
      let nxt, scrut, tmp1;
      if (cur instanceof Runtime.EffectSig.class) {
        nxt = Runtime.handleEffect(cur);
        scrut = cur === nxt;
        if (scrut === true) {
          Runtime.curEffect = cur;
          return null
        } else {
          cur = nxt;
          tmp1 = runtime.Unit;
        }
        tmp = tmp1;
        continue lbl
      } else {
        return cur
      }
      break;
    }
    return tmp
  } 
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, handlerFrame, saved, tmp, scrut1, scrut2, scrut3, tmp1, tmp2, tmp3, tmp4, tmp5;
    prevHandlerFrame = cur.contTrace;
    lbl: while (true) {
      let scrut4, scrut5;
      split_root$: {
        split_1$: {
          scrut4 = prevHandlerFrame.nextHandler !== null;
          if (scrut4 === true) {
            scrut5 = prevHandlerFrame.nextHandler.handler !== cur.handler;
            if (scrut5 === true) {
              prevHandlerFrame = prevHandlerFrame.nextHandler;
              tmp1 = runtime.Unit;
              continue lbl
            } else {
              break split_1$
            }
          } else {
            break split_1$
          }
        }
        tmp1 = runtime.Unit;
      }
      break;
    }
    scrut = prevHandlerFrame.nextHandler === null;
    if (scrut === true) {
      return cur
    } else {
      tmp2 = runtime.Unit;
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    saved = new Runtime.ContTrace.class(handlerFrame.next, cur.contTrace.last, handlerFrame.nextHandler, cur.contTrace.lastHandler, false);
    cur.contTrace.last = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    Runtime.curEffect = null;
    tmp3 = Runtime.resume(cur.contTrace);
    tmp = runtime.safeCall(cur.handlerFun(tmp3));
    scrut1 = Runtime.curEffect !== null;
    if (scrut1 === true) {
      cur = Runtime.curEffect;
      scrut2 = saved.next !== null;
      if (scrut2 === true) {
        cur.contTrace.last.next = saved.next;
        cur.contTrace.last = saved.last;
        tmp4 = runtime.Unit;
      } else {
        tmp4 = runtime.Unit;
      }
      scrut3 = saved.nextHandler !== null;
      if (scrut3 === true) {
        cur.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur.contTrace.lastHandler = saved.lastHandler;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.Unit;
      }
      return cur
    } else {
      return Runtime.resumeContTrace(saved, tmp)
    }
  } 
  static resume(contTrace) {
    return (value) => {
      let scrut, tmp, tmp1;
      scrut = contTrace.resumed;
      if (scrut === true) {
        throw runtime.safeCall(globalThis.Error("Multiple resumption"))
      } else {
        tmp = runtime.Unit;
      }
      contTrace.resumed = true;
      tmp1 = Runtime.resumeContTrace(contTrace, value);
      return Runtime.handleEffects(tmp1)
    }
  } 
  static resumeContTrace(contTrace, value) {
    let cont, handlerCont, curDepth, tmp;
    cont = contTrace.next;
    handlerCont = contTrace.nextHandler;
    curDepth = Runtime.stackDepth;
    lbl: while (true) {
      let scrut, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5;
      if (cont instanceof Runtime.FunctionContFrame.class) {
        Runtime.curEffect = null;
        tmp1 = runtime.safeCall(cont.resume(value));
        value = tmp1;
        scrut = Runtime.curEffect !== null;
        if (scrut === true) {
          value = Runtime.curEffect;
          tmp2 = runtime.Unit;
        } else {
          tmp2 = runtime.Unit;
        }
        Runtime.stackDepth = curDepth;
        if (value instanceof Runtime.EffectSig.class) {
          value.contTrace.last.next = cont.next;
          value.contTrace.lastHandler.nextHandler = handlerCont;
          scrut1 = contTrace.last !== cont;
          if (scrut1 === true) {
            value.contTrace.last = contTrace.last;
            tmp3 = runtime.Unit;
          } else {
            tmp3 = runtime.Unit;
          }
          scrut2 = handlerCont !== null;
          if (scrut2 === true) {
            value.contTrace.lastHandler = contTrace.lastHandler;
            tmp4 = runtime.Unit;
          } else {
            tmp4 = runtime.Unit;
          }
          return value
        } else {
          cont = cont.next;
          tmp5 = runtime.Unit;
        }
        tmp = tmp5;
        continue lbl
      } else {
        if (handlerCont instanceof Runtime.HandlerContFrame.class) {
          cont = handlerCont.next;
          handlerCont = handlerCont.nextHandler;
          tmp = runtime.Unit;
          continue lbl
        } else {
          return value
        }
      }
      break;
    }
    return tmp
  } 
  static checkDepth() {
    let scrut, tmp, lambda;
    tmp = Runtime.stackDepth >= Runtime.stackLimit;
    lambda = (undefined, function () {
      return Runtime.stackHandler !== null
    });
    scrut = runtime.short_and(tmp, lambda);
    if (scrut === true) {
      return runtime.safeCall(Runtime.stackHandler.delay())
    } else {
      return runtime.Unit
    }
  } 
  static runStackSafe(limit, f) {
    let result, tmp;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
    Runtime.stackDepth = 1;
    lbl: while (true) {
      let scrut, saved, tmp1;
      scrut = Runtime.stackResume !== null;
      if (scrut === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        tmp1 = runtime.safeCall(saved());
        result = tmp1;
        Runtime.stackDepth = 1;
        tmp = runtime.Unit;
        continue lbl
      } else {
        tmp = runtime.Unit;
      }
      break;
    }
    Runtime.stackLimit = 0;
    Runtime.stackDepth = 0;
    Runtime.stackHandler = null;
    return result
  } 
  static plus_impl(lhs, rhs) {
    let tmp;
    split_root$: {
      split_1$: {
        if (lhs instanceof Runtime.Int31.class) {
          if (rhs instanceof Runtime.Int31.class) {
            tmp = lhs + rhs;
            break split_root$
          } else {
            break split_1$
          }
        } else {
          break split_1$
        }
      }
      tmp = Runtime.unreachable();
    }
    return tmp
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Runtime"]; 
});
let Runtime = Runtime1; export default Runtime;
