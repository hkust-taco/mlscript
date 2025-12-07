const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let Runtime1;
globalThis.Object.freeze(class Runtime {
  static {
    Runtime1 = this
  }
  constructor() {
    runtime.Unit;
  }
  static #isResuming;
  static #resumeValue;
  static #resumeArr;
  static #resumeIdx;
  static #resumePc;
  static #stackLimit;
  static #stackDepth;
  static #stackHandler;
  static #stackResume;
  static get isResuming() { return Runtime.#isResuming; }
  static set isResuming(value) { Runtime.#isResuming = value; }
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
    globalThis.Object.freeze(class Unit {
      static {
        Runtime.Unit = globalThis.Object.freeze(new this)
      }
      constructor() {
        Object.defineProperty(this, "class", {
          value: Unit
        })
      }
      toString() {
        return "()"
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["object", "Unit"]; 
    });
    globalThis.Object.freeze(class LoopEnd {
      static {
        Runtime.LoopEnd = globalThis.Object.freeze(new this)
      }
      constructor() {
        Object.defineProperty(this, "class", {
          value: LoopEnd
        })
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
    globalThis.Object.freeze(class EffectHandle {
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
          let tmp;
          tmp = Runtime.resume(this$EffectHandle.reified.contTrace);
          return runtime.safeCall(tmp(value))
        });
        return Runtime1.try(lambda)
      } 
      raise() {
        return Runtime.topLevelEffect(this.reified, false)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectHandle", [null]]; 
    });
    this.MatchSuccess = function MatchSuccess(output, bindings) {
      return globalThis.Object.freeze(new MatchSuccess.class(output, bindings));
    };
    globalThis.Object.freeze(class MatchSuccess {
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
    globalThis.Object.freeze(class MatchFailure {
      static {
        Runtime.MatchFailure.class = this
      }
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "MatchFailure", ["errors"]]; 
    });
    globalThis.Object.freeze(class Tuple {
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
        let tmp;
        tmp = xs.length - j;
        return xs.slice(i, tmp)
      } 
      static lazySlice(xs, i, j) {
        let tmp;
        tmp = LazyArray.dropLeftRight(i, j);
        return runtime.safeCall(tmp(xs))
      } 
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      } 
      static get(xs, i) {
        let scrut, scrut1, tmp, tmp1, tmp2;
        scrut = i >= xs.length;
        if (scrut === true) {
          throw globalThis.RangeError("Tuple.get: index out of bounds")
        } else {
          tmp = runtime.Unit;
        }
        tmp1 = - xs.length;
        scrut1 = i < tmp1;
        if (scrut1 === true) {
          throw globalThis.RangeError("Tuple.get: negative index out of bounds")
        } else {
          tmp2 = runtime.Unit;
        }
        return xs.at(i)
      } 
      static isArrayLike(xs) {
        return runtime.safeCall(Iter.isArrayLike(xs))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Tuple"]; 
    });
    globalThis.Object.freeze(class Str {
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
          throw globalThis.RangeError("Str.get: index out of bounds")
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
    globalThis.Object.freeze(class TraceLogger {
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
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "TraceLogger"]; 
    });
    this.isResuming = false;
    this.resumeValue = null;
    this.resumeArr = null;
    this.resumeIdx = null;
    this.resumePc = null;
    globalThis.Object.freeze(class FatalEffect {
      static {
        Runtime.FatalEffect = globalThis.Object.freeze(new this)
      }
      constructor() {
        Object.defineProperty(this, "class", {
          value: FatalEffect
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "FatalEffect"]; 
    });
    globalThis.Object.freeze(class PrintStackEffect {
      static {
        Runtime.PrintStackEffect = globalThis.Object.freeze(new this)
      }
      constructor() {
        Object.defineProperty(this, "class", {
          value: PrintStackEffect
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "PrintStackEffect"]; 
    });
    this.FunctionContFrame = function FunctionContFrame(next, saved) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next, saved));
    };
    globalThis.Object.freeze(class FunctionContFrame {
      static {
        Runtime.FunctionContFrame.class = this
      }
      constructor(next, saved) {
        this.next = next;
        this.saved = saved;
      }
      resume(value) {
        let scrut, f, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = this.saved.at(0) == 0;
        if (scrut === true) {
          tmp = runtime.safeCall(globalThis.console.log("cannot resume getters"));
        } else {
          tmp = runtime.Unit;
        }
        f = this.saved.at(1);
        tmp5: while (true) {
          scrut1 = this.saved.at(0) > 1;
          if (scrut1 === true) {
            tmp1 = runtime.safeCall(f());
            f = tmp1;
            tmp2 = this.saved.at(0) - 1;
            this.saved[0] = tmp2;
            tmp3 = runtime.Unit;
            continue tmp5
          } else {
            tmp3 = runtime.Unit;
          }
          break;
        }
        Runtime.isResuming = true;
        Runtime.resumeValue = value;
        Runtime.resumeArr = this.saved;
        Runtime.resumeIdx = 7;
        Runtime.resumePc = this.saved.at(4);
        tmp4 = globalThis.Object.freeze([]);
        return f.apply(this.saved.at(5), tmp4)
      } 
      get getLocal() {
        let debugInfo, res, i, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
        debugInfo = this.saved.at(2);
        res = [];
        i = 1;
        tmp6: while (true) {
          scrut = i < debugInfo.length;
          if (scrut === true) {
            tmp = i + 1;
            tmp1 = 7 + debugInfo.at(i);
            tmp2 = globalThis.Object.freeze(new Runtime.LocalVarInfo.class(debugInfo.at(tmp), this.saved.at(tmp1)));
            tmp3 = runtime.safeCall(res.push(tmp2));
            tmp4 = i + 2;
            i = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        return res;
      } 
      get getNme() {
        return this.saved.at(2).at(0);
      } 
      get getLoc() {
        return this.saved.at(3);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunctionContFrame", ["next", "saved"]]; 
    });
    this.FunctionContFrameOld = function FunctionContFrameOld(next) {
      return globalThis.Object.freeze(new FunctionContFrameOld.class(next));
    };
    globalThis.Object.freeze(class FunctionContFrameOld {
      static {
        Runtime.FunctionContFrameOld.class = this
      }
      constructor(next) {
        this.next = next;
      }
      doUnwind(res1, newPc) {
        this.pc = newPc;
        res1.contTrace.last.next = this;
        res1.contTrace.last = this;
        return res1
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunctionContFrameOld", ["next"]]; 
    });
    this.HandlerContFrame = function HandlerContFrame(next, nextHandler, handler) {
      return globalThis.Object.freeze(new HandlerContFrame.class(next, nextHandler, handler));
    };
    globalThis.Object.freeze(class HandlerContFrame {
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
    globalThis.Object.freeze(class ContTrace {
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
    globalThis.Object.freeze(class EffectSig {
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
    globalThis.Object.freeze(class NonLocalReturn {
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
    globalThis.Object.freeze(class FnLocalsInfo {
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
    globalThis.Object.freeze(class LocalVarInfo {
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
    this.FakeError = function FakeError(stack) {
      return globalThis.Object.freeze(new FakeError.class(stack));
    };
    globalThis.Object.freeze(class FakeError {
      static {
        Runtime.FakeError.class = this
      }
      constructor(stack) {
        this.stack = stack;
      }
      toString() {
        return this.stack
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["class", "FakeError", ["stack"]]; 
    });
    this.stackLimit = 0;
    this.stackDepth = 0;
    this.stackHandler = null;
    this.stackResume = null;
    globalThis.Object.freeze(class StackDelayHandler {
      static {
        Runtime.StackDelayHandler = globalThis.Object.freeze(new this)
      }
      constructor() {
        Object.defineProperty(this, "class", {
          value: StackDelayHandler
        })
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
    globalThis.Object.freeze(class Int31 {
      static {
        Runtime.Int31.class = this
      }
      constructor(v) {
        this.#v = v;
      }
      #v;
      zext() {
        let tmp, tmp1;
        tmp = Runtime.shl(1, 31);
        tmp1 = runtime.safeCall(Runtime.bitnot(tmp));
        return Runtime.bitand(this.#v, tmp1)
      } 
      sext() {
        let tmp;
        tmp = Runtime.shl(1, 31);
        return Runtime.bitor(this.#v, tmp)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Int31", [null]]; 
    });
  }
  static get unreachable() {
    throw globalThis.Error("unreachable");
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
      throw globalThis.Error(tmp12)
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
      throw globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value.")
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
    throw globalThis.Error(tmp3)
  } 
  static try(f) {
    let res;
    res = runtime.safeCall(f());
    if (res instanceof Runtime.EffectSig.class) {
      return Runtime.EffectHandle(res)
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
  static topLevelEffect(tr, debug) {
    let scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp7: while (true) {
      scrut = tr.handler === Runtime.PrintStackEffect;
      if (scrut === true) {
        tmp = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
        tmp1 = runtime.safeCall(globalThis.console.log(tmp));
        tmp2 = Runtime.resume(tr.contTrace);
        tmp3 = runtime.safeCall(tmp2(runtime.Unit));
        tr = tmp3;
        tmp4 = runtime.Unit;
        continue tmp7
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      tmp5 = "Error: Unhandled effect " + tr.handler.constructor.name;
      tmp6 = Runtime.showStackTrace(tmp5, tr, debug, false);
      throw Runtime.FakeError(tmp6)
    } else {
      return tr
    }
  } 
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail, scrut, cur, scrut1, curLocals, loc, loc1, localsMsg, scrut2, scrut3, tmp, lambda, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      tmp18: while (true) {
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          tmp19: while (true) {
            scrut1 = cur !== null;
            if (scrut1 === true) {
              curLocals = cur.getLocal;
              loc = cur.getLoc;
              if (loc === null) {
                tmp = "pc=" + cur.pc;
              } else {
                tmp = loc;
              }
              loc1 = tmp;
              split_root$: {
                split_1$: {
                  if (showLocals === true) {
                    scrut2 = curLocals.length > 0;
                    if (scrut2 === true) {
                      lambda = (undefined, function (l) {
                        let tmp20, tmp21;
                        tmp20 = l.localName + "=";
                        tmp21 = Rendering.render(l.value);
                        return tmp20 + tmp21
                      });
                      tmp1 = runtime.safeCall(curLocals.map(lambda));
                      tmp2 = runtime.safeCall(tmp1.join(", "));
                      tmp3 = " with locals: " + tmp2;
                      break split_root$
                    } else {
                      break split_1$
                    }
                  } else {
                    break split_1$
                  }
                }
                tmp3 = "";
              }
              localsMsg = tmp3;
              tmp4 = "\n\tat " + cur.getNme;
              tmp5 = tmp4 + " (";
              tmp6 = tmp5 + loc1;
              tmp7 = tmp6 + ")";
              tmp8 = msg + tmp7;
              msg = tmp8;
              tmp9 = msg + localsMsg;
              msg = tmp9;
              cur = cur.next;
              atTail = false;
              tmp10 = runtime.Unit;
              continue tmp19
            } else {
              tmp10 = runtime.Unit;
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut3 = curHandler !== null;
          if (scrut3 === true) {
            tmp11 = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp12 = msg + tmp11;
            msg = tmp12;
            atTail = false;
            tmp13 = runtime.Unit;
          } else {
            tmp13 = runtime.Unit;
          }
          tmp14 = tmp13;
          continue tmp18
        } else {
          tmp14 = runtime.Unit;
        }
        break;
      }
      if (atTail === true) {
        tmp15 = msg + "\n\tat tail position";
        msg = tmp15;
        tmp16 = runtime.Unit;
      } else {
        tmp16 = runtime.Unit;
      }
      tmp17 = tmp16;
    } else {
      tmp17 = runtime.Unit;
    }
    return msg
  } 
  static showFunctionContChain(cont, hl, vis, reps) {
    let result, scrut, scrut1, scrut2, tmp, lambda, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont.constructor.name + "(pc=";
      result = tmp + cont.pc;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp8, tmp9;
        scrut3 = runtime.safeCall(m.has(cont));
        if (scrut3 === true) {
          tmp8 = ", " + marker;
          tmp9 = result + tmp8;
          result = tmp9;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      tmp1 = runtime.safeCall(hl.forEach(lambda));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp2 = reps + 1;
        reps = tmp2;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)")
        } else {
          tmp3 = runtime.Unit;
        }
        tmp4 = result + ", REPEAT";
        result = tmp4;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.safeCall(vis.add(cont));
      }
      tmp6 = result + ") -> ";
      tmp7 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp6 + tmp7
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
    let result, scrut, scrut1, scrut2, lambda, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (cont instanceof Runtime.HandlerContFrame.class) {
      result = cont.handler.constructor.name;
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
      tmp = runtime.safeCall(hl.forEach(lambda));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp1 = reps + 1;
        reps = tmp1;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)")
        } else {
          tmp2 = runtime.Unit;
        }
        tmp3 = result + ", REPEAT";
        result = tmp3;
        tmp4 = runtime.Unit;
      } else {
        tmp4 = runtime.safeCall(vis.add(cont));
      }
      tmp5 = result + " -> ";
      tmp6 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp5 + tmp6
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
    let scrut, scrut1, vis, hl, cur, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    if (contTrace instanceof Runtime.ContTrace.class) {
      tmp = globalThis.console.log("resumed: ", contTrace.resumed);
      scrut = contTrace.last === contTrace;
      if (scrut === true) {
        tmp1 = runtime.safeCall(globalThis.console.log("<last is self>"));
      } else {
        tmp1 = runtime.Unit;
      }
      scrut1 = contTrace.lastHandler === contTrace;
      if (scrut1 === true) {
        tmp2 = runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      } else {
        tmp2 = runtime.Unit;
      }
      vis = globalThis.Object.freeze(new globalThis.Set());
      hl = globalThis.Object.freeze(new globalThis.Map());
      tmp3 = globalThis.Object.freeze([
        contTrace.last
      ]);
      tmp4 = globalThis.Object.freeze(new globalThis.Set(tmp3));
      tmp5 = hl.set("last", tmp4);
      tmp6 = globalThis.Object.freeze([
        contTrace.lastHandler
      ]);
      tmp7 = globalThis.Object.freeze(new globalThis.Set(tmp6));
      tmp8 = hl.set("last-handler", tmp7);
      tmp9 = Runtime.showFunctionContChain(contTrace.next, hl, vis, 0);
      tmp10 = runtime.safeCall(globalThis.console.log(tmp9));
      cur = contTrace.nextHandler;
      tmp15: while (true) {
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp11 = Runtime.showHandlerContChain(cur, hl, vis, 0);
          tmp12 = runtime.safeCall(globalThis.console.log(tmp11));
          cur = cur.nextHandler;
          tmp13 = runtime.Unit;
          continue tmp15
        } else {
          tmp13 = runtime.Unit;
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    } else {
      tmp14 = runtime.safeCall(globalThis.console.log("Not a cont trace:"));
      return runtime.safeCall(globalThis.console.log(contTrace))
    }
  } 
  static debugEff(eff) {
    let tmp, tmp1, tmp2, tmp3;
    if (eff instanceof Runtime.EffectSig.class) {
      tmp = runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      tmp1 = globalThis.console.log("handler: ", eff.handler.constructor.name);
      tmp2 = globalThis.console.log("handlerFun: ", eff.handlerFun);
      return Runtime.debugContTrace(eff.contTrace)
    } else {
      tmp3 = runtime.safeCall(globalThis.console.log("Not an effect:"));
      return runtime.safeCall(globalThis.console.log(eff))
    }
  } 
  static unwind(cur, ...saved) {
    let tmp;
    tmp = new Runtime.FunctionContFrame.class(null, saved);
    cur.contTrace.last.next = tmp;
    cur.contTrace.last = cur.contTrace.last.next;
    return cur
  } 
  static mkEffect(handler, handlerFun) {
    let res, tmp;
    tmp = new Runtime.ContTrace.class(null, null, null, null, false);
    res = new Runtime.EffectSig.class(tmp, handler, handlerFun);
    res.contTrace.last = res.contTrace;
    res.contTrace.lastHandler = res.contTrace;
    return res
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
    let cur;
    cur = runtime.safeCall(body());
    if (cur instanceof Runtime.EffectSig.class) {
      return Runtime.handleBlockImpl(cur, handler)
    } else {
      return cur
    }
  } 
  static handleEffects(cur) {
    let nxt, scrut, tmp, tmp1;
    tmp2: while (true) {
      if (cur instanceof Runtime.EffectSig.class) {
        nxt = Runtime.handleEffect(cur);
        scrut = cur === nxt;
        if (scrut === true) {
          return cur
        } else {
          cur = nxt;
          tmp = runtime.Unit;
        }
        tmp1 = tmp;
        continue tmp2
      } else {
        return cur
      }
      break;
    }
    return tmp1
  } 
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, scrut1, scrut2, handlerFrame, saved, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    prevHandlerFrame = cur.contTrace;
    tmp6: while (true) {
      split_root$: {
        split_1$: {
          scrut = prevHandlerFrame.nextHandler !== null;
          if (scrut === true) {
            scrut1 = prevHandlerFrame.nextHandler.handler !== cur.handler;
            if (scrut1 === true) {
              prevHandlerFrame = prevHandlerFrame.nextHandler;
              tmp = runtime.Unit;
              continue tmp6
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
    scrut2 = prevHandlerFrame.nextHandler === null;
    if (scrut2 === true) {
      return cur
    } else {
      tmp1 = runtime.Unit;
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    saved = new Runtime.ContTrace.class(handlerFrame.next, cur.contTrace.last, handlerFrame.nextHandler, cur.contTrace.lastHandler, false);
    cur.contTrace.last = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    tmp2 = Runtime.resume(cur.contTrace);
    tmp3 = runtime.safeCall(cur.handlerFun(tmp2));
    cur = tmp3;
    if (cur instanceof Runtime.EffectSig.class) {
      scrut3 = saved.next !== null;
      if (scrut3 === true) {
        cur.contTrace.last.next = saved.next;
        cur.contTrace.last = saved.last;
        tmp4 = runtime.Unit;
      } else {
        tmp4 = runtime.Unit;
      }
      scrut4 = saved.nextHandler !== null;
      if (scrut4 === true) {
        cur.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur.contTrace.lastHandler = saved.lastHandler;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.Unit;
      }
      return cur
    } else {
      return Runtime.resumeContTrace(saved, cur)
    }
  } 
  static resume(contTrace) {
    return (value) => {
      let scrut, tmp, tmp1;
      scrut = contTrace.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption")
      } else {
        tmp = runtime.Unit;
      }
      contTrace.resumed = true;
      tmp1 = Runtime.resumeContTrace(contTrace, value);
      return Runtime.handleEffects(tmp1)
    }
  } 
  static resumeContTrace(contTrace, value) {
    let cont, handlerCont, curDepth, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
    cont = contTrace.next;
    handlerCont = contTrace.nextHandler;
    curDepth = Runtime.stackDepth;
    tmp5: while (true) {
      if (cont instanceof Runtime.FunctionContFrame.class) {
        tmp = runtime.safeCall(cont.resume(value));
        value = tmp;
        Runtime.stackDepth = curDepth;
        if (value instanceof Runtime.EffectSig.class) {
          value.contTrace.last.next = cont.next;
          value.contTrace.lastHandler.nextHandler = handlerCont;
          scrut = contTrace.last !== cont;
          if (scrut === true) {
            value.contTrace.last = contTrace.last;
            tmp1 = runtime.Unit;
          } else {
            tmp1 = runtime.Unit;
          }
          scrut1 = handlerCont !== null;
          if (scrut1 === true) {
            value.contTrace.lastHandler = contTrace.lastHandler;
            tmp2 = runtime.Unit;
          } else {
            tmp2 = runtime.Unit;
          }
          return value
        } else {
          cont = cont.next;
          tmp3 = runtime.Unit;
        }
        tmp4 = tmp3;
        continue tmp5
      } else {
        if (handlerCont instanceof Runtime.HandlerContFrame.class) {
          cont = handlerCont.next;
          handlerCont = handlerCont.nextHandler;
          tmp4 = runtime.Unit;
          continue tmp5
        } else {
          return value
        }
      }
      break;
    }
    return tmp4
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
    let result, scrut, saved, tmp, tmp1;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
    Runtime.stackDepth = 1;
    tmp2: while (true) {
      scrut = Runtime.stackResume !== null;
      if (scrut === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        tmp = runtime.safeCall(saved());
        result = tmp;
        Runtime.stackDepth = 1;
        tmp1 = runtime.Unit;
        continue tmp2
      } else {
        tmp1 = runtime.Unit;
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
