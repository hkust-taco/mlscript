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
  static #stackLimit;
  static #stackDepth;
  static #stackHandler;
  static #stackResume;
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
    this.FunctionContFrame = function FunctionContFrame(next) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next));
    };
    globalThis.Object.freeze(class FunctionContFrame {
      static {
        Runtime.FunctionContFrame.class = this
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
      static [definitionMetadata] = ["class", "FunctionContFrame", ["next"]]; 
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
    let scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp6: while (true) {
      scrut = tr.handler === Runtime.PrintStackEffect;
      if (scrut === true) {
        tmp = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
        tmp1 = runtime.safeCall(globalThis.console.log(tmp));
        tmp2 = Runtime.resume(tr.contTrace);
        tmp3 = runtime.safeCall(tmp2(runtime.Unit));
        tr = tmp3;
        tmp4 = runtime.Unit;
        continue tmp6
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      tmp5 = "Error: Unhandled effect " + tr.handler.constructor.name;
      throw Runtime.showStackTrace(tmp5, tr, debug, false)
    } else {
      return tr
    }
  } 
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail, scrut, cur, scrut1, locals, curLocals, loc, loc1, localsMsg, scrut2, scrut3, tmp, tmp1, lambda, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      tmp19: while (true) {
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          tmp20: while (true) {
            scrut1 = cur !== null;
            if (scrut1 === true) {
              locals = cur.getLocals;
              tmp = locals.length - 1;
              curLocals = runtime.safeCall(locals.at(tmp));
              loc = cur.getLoc;
              if (loc === null) {
                tmp1 = "pc=" + cur.pc;
              } else {
                tmp1 = loc;
              }
              loc1 = tmp1;
              split_root$: {
                split_1$: {
                  if (showLocals === true) {
                    scrut2 = curLocals.locals.length > 0;
                    if (scrut2 === true) {
                      lambda = (undefined, function (l) {
                        let tmp21, tmp22;
                        tmp21 = l.localName + "=";
                        tmp22 = Rendering.render(l.value);
                        return tmp21 + tmp22
                      });
                      tmp2 = runtime.safeCall(curLocals.locals.map(lambda));
                      tmp3 = runtime.safeCall(tmp2.join(", "));
                      tmp4 = " with locals: " + tmp3;
                      break split_root$
                    } else {
                      break split_1$
                    }
                  } else {
                    break split_1$
                  }
                }
                tmp4 = "";
              }
              localsMsg = tmp4;
              tmp5 = "\n\tat " + curLocals.fnName;
              tmp6 = tmp5 + " (";
              tmp7 = tmp6 + loc1;
              tmp8 = tmp7 + ")";
              tmp9 = msg + tmp8;
              msg = tmp9;
              tmp10 = msg + localsMsg;
              msg = tmp10;
              cur = cur.next;
              atTail = false;
              tmp11 = runtime.Unit;
              continue tmp20
            } else {
              tmp11 = runtime.Unit;
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut3 = curHandler !== null;
          if (scrut3 === true) {
            tmp12 = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp13 = msg + tmp12;
            msg = tmp13;
            atTail = false;
            tmp14 = runtime.Unit;
          } else {
            tmp14 = runtime.Unit;
          }
          tmp15 = tmp14;
          continue tmp19
        } else {
          tmp15 = runtime.Unit;
        }
        break;
      }
      if (atTail === true) {
        tmp16 = msg + "\n\tat tail position";
        msg = tmp16;
        tmp17 = runtime.Unit;
      } else {
        tmp17 = runtime.Unit;
      }
      tmp18 = tmp17;
    } else {
      tmp18 = runtime.Unit;
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
