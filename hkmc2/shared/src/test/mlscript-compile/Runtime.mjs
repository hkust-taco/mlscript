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
    this.EffectHandle = function EffectHandle(_reified1) {
      return globalThis.Object.freeze(new EffectHandle.class(_reified1));
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
    this.MatchResult = function MatchResult(captures1) {
      return globalThis.Object.freeze(new MatchResult.class(captures1));
    };
    Object.defineProperty(this.MatchResult, "class", {
    enumerable: true,
      value: class MatchResult {
        constructor(captures) {
          this.captures = captures;
        }
        toString() { return runtime.render(this); }
        static [definitionMetadata] = ["class", "MatchResult", ["captures"]]; 
      }
    });
    this.MatchFailure = function MatchFailure(errors1) {
      return globalThis.Object.freeze(new MatchFailure.class(errors1));
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
      static lazySlice(xs1, i1, j1) {
        let tmp;
        tmp = LazyArray.dropLeftRight(i1, j1);
        return runtime.safeCall(tmp(xs1))
      } 
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      } 
      static get(xs2, i2) {
        let scrut, scrut1, tmp, tmp1, tmp2;
        scrut = i2 >= xs2.length;
        if (scrut === true) {
          throw globalThis.RangeError("Tuple.get: index out of bounds")
        } else {
          tmp = runtime.Unit;
        }
        tmp1 = - xs2.length;
        scrut1 = i2 < tmp1;
        if (scrut1 === true) {
          throw globalThis.RangeError("Tuple.get: negative index out of bounds")
        } else {
          tmp2 = runtime.Unit;
        }
        return xs2.at(i2)
      } 
      static isArrayLike(xs3) {
        return runtime.safeCall(Iter.isArrayLike(xs3))
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
      static get(string1, i) {
        let scrut;
        scrut = i >= string1.length;
        if (scrut === true) {
          throw globalThis.RangeError("Str.get: index out of bounds")
        } else {
          return runtime.safeCall(string1.at(i))
        }
      } 
      static drop(string2, n) {
        return runtime.safeCall(string2.slice(n))
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
    this.FunctionContFrame = function FunctionContFrame(next1) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next1));
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
    this.HandlerContFrame = function HandlerContFrame(next1, nextHandler1, handler1) {
      return globalThis.Object.freeze(new HandlerContFrame.class(next1, nextHandler1, handler1));
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
    this.ContTrace = function ContTrace(next1, last1, nextHandler1, lastHandler1, resumed1) {
      return globalThis.Object.freeze(new ContTrace.class(next1, last1, nextHandler1, lastHandler1, resumed1));
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
    this.EffectSig = function EffectSig(contTrace1, handler1, handlerFun1) {
      return globalThis.Object.freeze(new EffectSig.class(contTrace1, handler1, handlerFun1));
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
    this.FnLocalsInfo = function FnLocalsInfo(fnName1, locals1) {
      return globalThis.Object.freeze(new FnLocalsInfo.class(fnName1, locals1));
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
    this.LocalVarInfo = function LocalVarInfo(localName1, value1) {
      return globalThis.Object.freeze(new LocalVarInfo.class(localName1, value1));
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
  static checkCall(x1) {
    if (x1 === undefined) {
      throw globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value.")
    } else {
      return x1
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
  static printRaw(x2) {
    let tmp;
    tmp = runtime.safeCall(Runtime.render(x2));
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
  static showStackTrace(header, tr1, debug1, showLocals1) {
    let msg, curHandler, atTail, scrut, cur, scrut1, locals, curLocals, loc, loc1, localsMsg, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, lambda;
    msg = header;
    curHandler = tr1.contTrace;
    atTail = true;
    if (debug1 === true) {
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
              if (showLocals1 === true) {
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
  static showHandlerContChain(cont1, hl1, vis1, reps1) {
    let scrut, result, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda;
    if (cont1 instanceof Runtime.HandlerContFrame.class) {
      result = cont1.handler.constructor.name;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp8, tmp9;
        scrut3 = runtime.safeCall(m.has(cont1));
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
      tmp1 = runtime.safeCall(hl1.forEach(tmp));
      scrut1 = runtime.safeCall(vis1.has(cont1));
      if (scrut1 === true) {
        tmp2 = reps1 + 1;
        reps1 = tmp2;
        scrut2 = reps1 > 10;
        if (scrut2 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)")
        } else {
          tmp3 = runtime.Unit;
        }
        tmp4 = result + ", REPEAT";
        result = tmp4;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.safeCall(vis1.add(cont1));
      }
      tmp6 = result + " -> ";
      tmp7 = Runtime.showFunctionContChain(cont1.next, hl1, vis1, reps1);
      return tmp6 + tmp7
    } else {
      scrut = cont1 === null;
      if (scrut === true) {
        return "(null)"
      } else {
        return "(NOT HANDLER CONT)"
      }
    }
  } 
  static debugCont(cont2) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showFunctionContChain(cont2, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  } 
  static debugHandler(cont3) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showHandlerContChain(cont3, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  } 
  static debugContTrace(contTrace) {
    let scrut, scrut1, vis2, hl2, cur, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
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
      vis2 = tmp3;
      tmp4 = globalThis.Object.freeze(new globalThis.Map());
      hl2 = tmp4;
      tmp5 = globalThis.Object.freeze(new globalThis.Set(globalThis.Object.freeze([ contTrace.last ])));
      tmp6 = hl2.set("last", tmp5);
      tmp7 = globalThis.Object.freeze(new globalThis.Set(globalThis.Object.freeze([ contTrace.lastHandler ])));
      tmp8 = hl2.set("last-handler", tmp7);
      tmp9 = Runtime.showFunctionContChain(contTrace.next, hl2, vis2, 0);
      tmp10 = runtime.safeCall(globalThis.console.log(tmp9));
      cur = contTrace.nextHandler;
      tmp15: while (true) {
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp11 = Runtime.showHandlerContChain(cur, hl2, vis2, 0);
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
  static handleBlockImpl(cur, handler1) {
    let handlerFrame, tmp;
    tmp = new Runtime.HandlerContFrame.class(null, null, handler1);
    handlerFrame = tmp;
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  } 
  static enterHandleBlock(handler2, body) {
    let cur1, tmp;
    tmp = runtime.safeCall(body());
    cur1 = tmp;
    if (cur1 instanceof Runtime.EffectSig.class) {
      return Runtime.handleBlockImpl(cur1, handler2)
    } else {
      return cur1
    }
  } 
  static handleEffects(cur1) {
    let nxt, scrut, tmp, tmp1, tmp2;
    tmp3: while (true) {
      if (cur1 instanceof Runtime.EffectSig.class) {
        tmp = Runtime.handleEffect(cur1);
        nxt = tmp;
        scrut = cur1 === nxt;
        if (scrut === true) {
          return cur1
        } else {
          cur1 = nxt;
          tmp1 = runtime.Unit;
        }
        tmp2 = tmp1;
        continue tmp3
      } else {
        return cur1
      }
      break;
    }
    return tmp2
  } 
  static handleEffect(cur2) {
    let prevHandlerFrame, scrut, scrut1, scrut2, handlerFrame, saved, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    prevHandlerFrame = cur2.contTrace;
    tmp7: while (true) {
      scrut = prevHandlerFrame.nextHandler !== null;
      if (scrut === true) {
        scrut1 = prevHandlerFrame.nextHandler.handler !== cur2.handler;
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
      return cur2
    } else {
      tmp1 = runtime.Unit;
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    tmp2 = new Runtime.ContTrace.class(handlerFrame.next, cur2.contTrace.last, handlerFrame.nextHandler, cur2.contTrace.lastHandler, false);
    saved = tmp2;
    cur2.contTrace.last = handlerFrame;
    cur2.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    tmp3 = Runtime.resume(cur2.contTrace);
    tmp4 = runtime.safeCall(cur2.handlerFun(tmp3));
    cur2 = tmp4;
    if (cur2 instanceof Runtime.EffectSig.class) {
      scrut3 = saved.next !== null;
      if (scrut3 === true) {
        cur2.contTrace.last.next = saved.next;
        cur2.contTrace.last = saved.last;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.Unit;
      }
      scrut4 = saved.nextHandler !== null;
      if (scrut4 === true) {
        cur2.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur2.contTrace.lastHandler = saved.lastHandler;
        tmp6 = runtime.Unit;
      } else {
        tmp6 = runtime.Unit;
      }
      return cur2
    } else {
      return Runtime.resumeContTrace(saved, cur2)
    }
  } 
  static resume(contTrace1) {
    return (value) => {
      let scrut, tmp, tmp1;
      scrut = contTrace1.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption")
      } else {
        tmp = runtime.Unit;
      }
      contTrace1.resumed = true;
      tmp1 = Runtime.resumeContTrace(contTrace1, value);
      return Runtime.handleEffects(tmp1)
    }
  } 
  static resumeContTrace(contTrace2, value) {
    let cont4, handlerCont, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
    cont4 = contTrace2.next;
    handlerCont = contTrace2.nextHandler;
    tmp5: while (true) {
      if (cont4 instanceof Runtime.FunctionContFrame.class) {
        tmp = runtime.safeCall(cont4.resume(value));
        value = tmp;
        if (value instanceof Runtime.EffectSig.class) {
          value.contTrace.last.next = cont4.next;
          value.contTrace.lastHandler.nextHandler = handlerCont;
          scrut = contTrace2.last !== cont4;
          if (scrut === true) {
            value.contTrace.last = contTrace2.last;
            tmp1 = runtime.Unit;
          } else {
            tmp1 = runtime.Unit;
          }
          scrut1 = handlerCont !== null;
          if (scrut1 === true) {
            value.contTrace.lastHandler = contTrace2.lastHandler;
            tmp2 = runtime.Unit;
          } else {
            tmp2 = runtime.Unit;
          }
          return value
        } else {
          cont4 = cont4.next;
          tmp3 = runtime.Unit;
        }
        tmp4 = tmp3;
        continue tmp5
      } else {
        if (handlerCont instanceof Runtime.HandlerContFrame.class) {
          cont4 = handlerCont.next;
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
  static runStackSafe(limit, f1) {
    let result, scrut, saved, tmp1, tmp2, tmp3;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackOffset = 0;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    tmp1 = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f1);
    result = tmp1;
    tmp4: while (true) {
      scrut = Runtime.stackResume !== null;
      if (scrut === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        Runtime.stackOffset = Runtime.stackDepth;
        tmp2 = runtime.safeCall(saved());
        result = tmp2;
        tmp3 = runtime.Unit;
        continue tmp4
      } else {
        tmp3 = runtime.Unit;
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
