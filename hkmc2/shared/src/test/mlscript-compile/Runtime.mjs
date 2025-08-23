const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let Runtime1;
(class Runtime {
  static #stackLimit;
  static #stackDepth;
  static #stackOffset;
  static #stackHandler;
  static #stackResume;
  get stackLimit() { return Runtime.#stackLimit; }
  set stackLimit(value) { Runtime.#stackLimit = value; }
  get stackDepth() { return Runtime.#stackDepth; }
  set stackDepth(value) { Runtime.#stackDepth = value; }
  get stackOffset() { return Runtime.#stackOffset; }
  set stackOffset(value) { Runtime.#stackOffset = value; }
  get stackHandler() { return Runtime.#stackHandler; }
  set stackHandler(value) { Runtime.#stackHandler = value; }
  get stackResume() { return Runtime.#stackResume; }
  set stackResume(value) { Runtime.#stackResume = value; }
  static {
    Runtime1 = Runtime;
    const Unit$class = class Unit {
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
    };
    this.Unit = globalThis.Object.freeze(new Unit$class);
    this.short_and = RuntimeJS.short_and;
    this.short_or = RuntimeJS.short_or;
    this.try_catch = RuntimeJS.try_catch;
    this.EffectHandle = function EffectHandle(_reified) {
      return globalThis.Object.freeze(new EffectHandle.class(_reified));
    };
    Object.defineProperty(this.EffectHandle, "class", {
      enumerable: true,
      value: class EffectHandle {
        #_reified;
        constructor(_reified) {
          this.#_reified = _reified;
          this.reified = this.#_reified;
        }
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
      }
    });
    this.MatchResult = function MatchResult(output, bindings) {
      return globalThis.Object.freeze(new MatchResult.class(output, bindings));
    };
    Object.defineProperty(this.MatchResult, "class", {
      enumerable: true,
      value: class MatchResult {
        constructor(output, bindings) {
          this.output = output;
          this.bindings = bindings;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "MatchResult", ["output", "bindings"]]; 
      }
    });
    this.MatchFailure = function MatchFailure(errors) {
      return globalThis.Object.freeze(new MatchFailure.class(errors));
    };
    Object.defineProperty(this.MatchFailure, "class", {
      enumerable: true,
      value: class MatchFailure {
        constructor(errors) {
          this.errors = errors;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "MatchFailure", ["errors"]]; 
      }
    });
    (class Tuple {
      static {
        Runtime.Tuple = Tuple;
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
      static toString() { return runtime.render(this); }
      static [definitionMetadata] = ["module", "Tuple"]; 
    });
    (class Str {
      static {
        Runtime.Str = Str;
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
      static toString() { return runtime.render(this); }
      static [definitionMetadata] = ["module", "Str"]; 
    });
    this.render = Rendering.render;
    (class TraceLogger {
      static #enabled;
      static #indentLvl;
      get enabled() { return TraceLogger.#enabled; }
      set enabled(value) { TraceLogger.#enabled = value; }
      get indentLvl() { return TraceLogger.#indentLvl; }
      set indentLvl(value) { TraceLogger.#indentLvl = value; }
      static {
        Runtime.TraceLogger = TraceLogger;
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
      static toString() { return runtime.render(this); }
      static [definitionMetadata] = ["module", "TraceLogger"]; 
    });
    const FatalEffect$class = class FatalEffect {
      constructor() {
        Object.defineProperty(this, "class", {
          value: FatalEffect
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "FatalEffect"]; 
    };
    this.FatalEffect = globalThis.Object.freeze(new FatalEffect$class);
    const PrintStackEffect$class = class PrintStackEffect {
      constructor() {
        Object.defineProperty(this, "class", {
          value: PrintStackEffect
        })
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "PrintStackEffect"]; 
    };
    this.PrintStackEffect = globalThis.Object.freeze(new PrintStackEffect$class);
    this.FunctionContFrame = function FunctionContFrame(next) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next));
    };
    Object.defineProperty(this.FunctionContFrame, "class", {
      enumerable: true,
      value: class FunctionContFrame {
        constructor(next) {
          this.next = next;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "FunctionContFrame", ["next"]]; 
      }
    });
    this.HandlerContFrame = function HandlerContFrame(next, nextHandler, handler) {
      return globalThis.Object.freeze(new HandlerContFrame.class(next, nextHandler, handler));
    };
    Object.defineProperty(this.HandlerContFrame, "class", {
      enumerable: true,
      value: class HandlerContFrame {
        constructor(next, nextHandler, handler) {
          this.next = next;
          this.nextHandler = nextHandler;
          this.handler = handler;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "HandlerContFrame", ["next", "nextHandler", "handler"]]; 
      }
    });
    this.ContTrace = function ContTrace(next, last, nextHandler, lastHandler, resumed) {
      return globalThis.Object.freeze(new ContTrace.class(next, last, nextHandler, lastHandler, resumed));
    };
    Object.defineProperty(this.ContTrace, "class", {
      enumerable: true,
      value: class ContTrace {
        constructor(next, last, nextHandler, lastHandler, resumed) {
          this.next = next;
          this.last = last;
          this.nextHandler = nextHandler;
          this.lastHandler = lastHandler;
          this.resumed = resumed;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "ContTrace", ["next", "last", "nextHandler", "lastHandler", "resumed"]]; 
      }
    });
    this.EffectSig = function EffectSig(contTrace, handler, handlerFun) {
      return globalThis.Object.freeze(new EffectSig.class(contTrace, handler, handlerFun));
    };
    Object.defineProperty(this.EffectSig, "class", {
      enumerable: true,
      value: class EffectSig {
        constructor(contTrace, handler, handlerFun) {
          this.contTrace = contTrace;
          this.handler = handler;
          this.handlerFun = handlerFun;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "EffectSig", ["contTrace", "handler", "handlerFun"]]; 
      }
    });
    this.NonLocalReturn = class NonLocalReturn {
      constructor() {}
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "NonLocalReturn"]; 
    };
    this.FnLocalsInfo = function FnLocalsInfo(fnName, locals) {
      return globalThis.Object.freeze(new FnLocalsInfo.class(fnName, locals));
    };
    Object.defineProperty(this.FnLocalsInfo, "class", {
      enumerable: true,
      value: class FnLocalsInfo {
        constructor(fnName, locals) {
          this.fnName = fnName;
          this.locals = locals;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "FnLocalsInfo", ["fnName", "locals"]]; 
      }
    });
    this.LocalVarInfo = function LocalVarInfo(localName, value) {
      return globalThis.Object.freeze(new LocalVarInfo.class(localName, value));
    };
    Object.defineProperty(this.LocalVarInfo, "class", {
      enumerable: true,
      value: class LocalVarInfo {
        constructor(localName, value) {
          this.localName = localName;
          this.value = value;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "LocalVarInfo", ["localName", "value"]]; 
      }
    });
    this.stackLimit = 0;
    this.stackDepth = 0;
    this.stackOffset = 0;
    this.stackHandler = null;
    this.stackResume = null;
    const StackDelayHandler$class = class StackDelayHandler {
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
    };
    this.StackDelayHandler = globalThis.Object.freeze(new StackDelayHandler$class);
  }
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, lambda;
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
    let res, tmp;
    tmp = runtime.safeCall(f());
    res = tmp;
    if (res instanceof Runtime.EffectSig.class) {
      return runtime.safeCall(Runtime.EffectHandle(res))
    } else {
      return res
    }
  } 
  static printRaw(x) {
    let tmp;
    tmp = Runtime.render(x, globalThis.Object.freeze({
      indent: 2,
      breakLength: 76
    }));
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
    let msg, curHandler, atTail, scrut, cur, scrut1, locals, curLocals, loc, loc1, localsMsg, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, lambda;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      tmp20: while (true) {
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          tmp21: while (true) {
            scrut1 = cur !== null;
            if (scrut1 === true) {
              locals = cur.getLocals;
              tmp = locals.length - 1;
              tmp1 = runtime.safeCall(locals.at(tmp));
              curLocals = tmp1;
              loc = cur.getLoc;
              if (loc === null) {
                tmp2 = "pc=" + cur.pc;
              } else {
                tmp2 = loc;
              }
              loc1 = tmp2;
              if (showLocals === true) {
                scrut2 = curLocals.locals.length > 0;
                if (scrut2 === true) {
                  lambda = (undefined, function (l) {
                    let tmp22, tmp23;
                    tmp22 = l.localName + "=";
                    tmp23 = Rendering.render(l.value);
                    return tmp22 + tmp23
                  });
                  tmp3 = runtime.safeCall(curLocals.locals.map(lambda));
                  tmp4 = runtime.safeCall(tmp3.join(", "));
                  tmp5 = " with locals: " + tmp4;
                } else {
                  tmp5 = "";
                }
              } else {
                tmp5 = "";
              }
              localsMsg = tmp5;
              tmp6 = "\n\tat " + curLocals.fnName;
              tmp7 = tmp6 + " (";
              tmp8 = tmp7 + loc1;
              tmp9 = tmp8 + ")";
              tmp10 = msg + tmp9;
              msg = tmp10;
              tmp11 = msg + localsMsg;
              msg = tmp11;
              cur = cur.next;
              atTail = false;
              tmp12 = runtime.Unit;
              continue tmp21
            } else {
              tmp12 = runtime.Unit;
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut3 = curHandler !== null;
          if (scrut3 === true) {
            tmp13 = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp14 = msg + tmp13;
            msg = tmp14;
            atTail = false;
            tmp15 = runtime.Unit;
          } else {
            tmp15 = runtime.Unit;
          }
          tmp16 = tmp15;
          continue tmp20
        } else {
          tmp16 = runtime.Unit;
        }
        break;
      }
      if (atTail === true) {
        tmp17 = msg + "\n\tat tail position";
        msg = tmp17;
        tmp18 = runtime.Unit;
      } else {
        tmp18 = runtime.Unit;
      }
      tmp19 = tmp18;
    } else {
      tmp19 = runtime.Unit;
    }
    return msg
  } 
  static showFunctionContChain(cont, hl, vis, reps) {
    let scrut, result, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont.constructor.name + "(pc=";
      tmp1 = tmp + cont.pc;
      result = tmp1;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp10, tmp11;
        scrut3 = runtime.safeCall(m.has(cont));
        if (scrut3 === true) {
          tmp10 = ", " + marker;
          tmp11 = result + tmp10;
          result = tmp11;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      tmp2 = lambda;
      tmp3 = runtime.safeCall(hl.forEach(tmp2));
      scrut1 = runtime.safeCall(vis.has(cont));
      if (scrut1 === true) {
        tmp4 = reps + 1;
        reps = tmp4;
        scrut2 = reps > 10;
        if (scrut2 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)")
        } else {
          tmp5 = runtime.Unit;
        }
        tmp6 = result + ", REPEAT";
        result = tmp6;
        tmp7 = runtime.Unit;
      } else {
        tmp7 = runtime.safeCall(vis.add(cont));
      }
      tmp8 = result + ") -> ";
      tmp9 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp8 + tmp9
    } else {
      scrut = cont === null;
      if (scrut === true) {
        return "(null)"
      } else {
        return "(NOT CONT)"
      }
    }
  } 
  static showHandlerContChain(cont, hl, vis, reps) {
    let scrut, result, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda;
    if (cont instanceof Runtime.HandlerContFrame.class) {
      result = cont.handler.constructor.name;
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
      tmp = lambda;
      tmp1 = runtime.safeCall(hl.forEach(tmp));
      scrut1 = runtime.safeCall(vis.has(cont));
      if (scrut1 === true) {
        tmp2 = reps + 1;
        reps = tmp2;
        scrut2 = reps > 10;
        if (scrut2 === true) {
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
      tmp6 = result + " -> ";
      tmp7 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp6 + tmp7
    } else {
      scrut = cont === null;
      if (scrut === true) {
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
      tmp3 = globalThis.Object.freeze(new globalThis.Set());
      vis = tmp3;
      tmp4 = globalThis.Object.freeze(new globalThis.Map());
      hl = tmp4;
      tmp5 = globalThis.Object.freeze(new globalThis.Set(globalThis.Object.freeze([
        contTrace.last
      ])));
      tmp6 = hl.set("last", tmp5);
      tmp7 = globalThis.Object.freeze(new globalThis.Set(globalThis.Object.freeze([
        contTrace.lastHandler
      ])));
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
    let res, tmp, tmp1;
    tmp = new Runtime.ContTrace.class(null, null, null, null, false);
    tmp1 = new Runtime.EffectSig.class(tmp, handler, handlerFun);
    res = tmp1;
    res.contTrace.last = res.contTrace;
    res.contTrace.lastHandler = res.contTrace;
    return res
  } 
  static handleBlockImpl(cur, handler) {
    let handlerFrame, tmp;
    tmp = new Runtime.HandlerContFrame.class(null, null, handler);
    handlerFrame = tmp;
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  } 
  static enterHandleBlock(handler, body) {
    let cur, tmp;
    tmp = runtime.safeCall(body());
    cur = tmp;
    if (cur instanceof Runtime.EffectSig.class) {
      return Runtime.handleBlockImpl(cur, handler)
    } else {
      return cur
    }
  } 
  static handleEffects(cur) {
    let nxt, scrut, tmp, tmp1, tmp2;
    tmp3: while (true) {
      if (cur instanceof Runtime.EffectSig.class) {
        tmp = Runtime.handleEffect(cur);
        nxt = tmp;
        scrut = cur === nxt;
        if (scrut === true) {
          return cur
        } else {
          cur = nxt;
          tmp1 = runtime.Unit;
        }
        tmp2 = tmp1;
        continue tmp3
      } else {
        return cur
      }
      break;
    }
    return tmp2
  } 
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, scrut1, scrut2, handlerFrame, saved, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    prevHandlerFrame = cur.contTrace;
    tmp7: while (true) {
      scrut = prevHandlerFrame.nextHandler !== null;
      if (scrut === true) {
        scrut1 = prevHandlerFrame.nextHandler.handler !== cur.handler;
        if (scrut1 === true) {
          prevHandlerFrame = prevHandlerFrame.nextHandler;
          tmp = runtime.Unit;
          continue tmp7
        } else {
          tmp = runtime.Unit;
        }
      } else {
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
    tmp2 = new Runtime.ContTrace.class(handlerFrame.next, cur.contTrace.last, handlerFrame.nextHandler, cur.contTrace.lastHandler, false);
    saved = tmp2;
    cur.contTrace.last = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    tmp3 = Runtime.resume(cur.contTrace);
    tmp4 = runtime.safeCall(cur.handlerFun(tmp3));
    cur = tmp4;
    if (cur instanceof Runtime.EffectSig.class) {
      scrut3 = saved.next !== null;
      if (scrut3 === true) {
        cur.contTrace.last.next = saved.next;
        cur.contTrace.last = saved.last;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.Unit;
      }
      scrut4 = saved.nextHandler !== null;
      if (scrut4 === true) {
        cur.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur.contTrace.lastHandler = saved.lastHandler;
        tmp6 = runtime.Unit;
      } else {
        tmp6 = runtime.Unit;
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
    let cont, handlerCont, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
    cont = contTrace.next;
    handlerCont = contTrace.nextHandler;
    tmp5: while (true) {
      if (cont instanceof Runtime.FunctionContFrame.class) {
        tmp = runtime.safeCall(cont.resume(value));
        value = tmp;
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
    let scrut, tmp, tmp1, lambda;
    tmp = Runtime.stackDepth - Runtime.stackOffset;
    tmp1 = tmp >= Runtime.stackLimit;
    lambda = (undefined, function () {
      return Runtime.stackHandler !== null
    });
    scrut = runtime.short_and(tmp1, lambda);
    if (scrut === true) {
      return runtime.safeCall(Runtime.stackHandler.delay())
    } else {
      return runtime.Unit
    }
  } 
  static resetDepth(tmp, curDepth) {
    let scrut, tmp1;
    Runtime.stackDepth = curDepth;
    scrut = curDepth < Runtime.stackOffset;
    if (scrut === true) {
      Runtime.stackOffset = curDepth;
      tmp1 = runtime.Unit;
    } else {
      tmp1 = runtime.Unit;
    }
    return tmp
  } 
  static runStackSafe(limit, f) {
    let result, scrut, saved, tmp, tmp1, tmp2;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackOffset = 0;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    tmp = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
    result = tmp;
    tmp3: while (true) {
      scrut = Runtime.stackResume !== null;
      if (scrut === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        Runtime.stackOffset = Runtime.stackDepth;
        tmp1 = runtime.safeCall(saved());
        result = tmp1;
        tmp2 = runtime.Unit;
        continue tmp3
      } else {
        tmp2 = runtime.Unit;
      }
      break;
    }
    Runtime.stackLimit = 0;
    Runtime.stackDepth = 0;
    Runtime.stackOffset = 0;
    Runtime.stackHandler = null;
    return result
  }
  static toString() { return runtime.render(this); }
  static [definitionMetadata] = ["module", "Runtime"]; 
});
let Runtime = Runtime1; export default Runtime;
