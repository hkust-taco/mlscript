import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let definitionMetadata, Runtime1, tmp;
tmp = globalThis.Symbol.for("mlscript.definitionMetadata");
definitionMetadata = tmp;
(class Runtime {
  static {
    Runtime1 = Runtime;
    const Unit$class = class Unit {
      constructor() {}
      toString() {
        return "()"
      }
      static [definitionMetadata] = ["object", "Unit"]; 
    };
    this.Unit = new Unit$class;
    Object.defineProperty(this.Unit, "class", {
    value: Unit$class
    });
    this.short_and = RuntimeJS.short_and;
    this.short_or = RuntimeJS.short_or;
    this.try_catch = RuntimeJS.try_catch;
    this.EffectHandle = function EffectHandle(_reified1) {
      return new EffectHandle.class(_reified1);
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
            let tmp1;
            tmp1 = Runtime.resume(this$EffectHandle.reified.contTrace);
            return runtime.safeCall(tmp1(value))
          });
          return Runtime1.try(lambda)
        } 
        raise() {
          return Runtime.topLevelEffect(this.reified, false)
        }
        static [definitionMetadata] = ["class", "EffectHandle", []]; 
      }
    });
    this.MatchResult = function MatchResult(captures1) {
      return new MatchResult.class(captures1);
    };
    Object.defineProperty(this.MatchResult, "class", {
    enumerable: true,
      value: class MatchResult {
        constructor(captures) {
          this.captures = captures;
        }
        static [definitionMetadata] = ["class", "MatchResult", ["captures"]]; 
      }
    });
    this.MatchFailure = function MatchFailure(errors1) {
      return new MatchFailure.class(errors1);
    };
    Object.defineProperty(this.MatchFailure, "class", {
    enumerable: true,
      value: class MatchFailure {
        constructor(errors) {
          this.errors = errors;
        }
        static [definitionMetadata] = ["class", "MatchFailure", ["errors"]]; 
      }
    });
    (class Tuple {
      static {
        Runtime.Tuple = Tuple;
        this.split = LazyArray.__split;
      }
      static slice(xs, i, j) {
        let tmp1;
        tmp1 = xs.length - j;
        return xs.slice(i, tmp1)
      } 
      static lazySlice(xs1, i1, j1) {
        let tmp1;
        tmp1 = LazyArray.slice(i1, j1);
        return runtime.safeCall(tmp1(xs1))
      } 
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      } 
      static get(xs2, i2) {
        let scrut, scrut1, tmp1, tmp2, tmp3;
        scrut = i2 >= xs2.length;
        if (scrut === true) {
          throw globalThis.RangeError("Tuple.get: index out of bounds");
        } else {
          tmp1 = runtime.Unit;
        }
        tmp2 = - xs2.length;
        scrut1 = i2 < tmp2;
        if (scrut1 === true) {
          throw globalThis.RangeError("Tuple.get: negative index out of bounds");
        } else {
          tmp3 = runtime.Unit;
        }
        return xs2.at(i2)
      } 
      static isArrayLike(xs3) {
        return runtime.safeCall(Iter.isArrayLike(xs3))
      }
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
          throw globalThis.RangeError("Str.get: index out of bounds");
        } else {
          return runtime.safeCall(string1.at(i))
        }
      } 
      static drop(string2, n) {
        return runtime.safeCall(string2.slice(n))
      }
      static [definitionMetadata] = ["module", "Str"]; 
    });
    this.render = Rendering.render;
    (class TraceLogger {
      static {
        Runtime.TraceLogger = TraceLogger;
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
      static [definitionMetadata] = ["module", "TraceLogger"]; 
    });
    const FatalEffect$class = class FatalEffect {
      constructor() {}
      static [definitionMetadata] = ["object", "FatalEffect"]; 
    };
    this.FatalEffect = new FatalEffect$class;
    Object.defineProperty(this.FatalEffect, "class", {
    value: FatalEffect$class
    });
    const PrintStackEffect$class = class PrintStackEffect {
      constructor() {}
      static [definitionMetadata] = ["object", "PrintStackEffect"]; 
    };
    this.PrintStackEffect = new PrintStackEffect$class;
    Object.defineProperty(this.PrintStackEffect, "class", {
    value: PrintStackEffect$class
    });
    this.FunctionContFrame = function FunctionContFrame(next1) {
      return new FunctionContFrame.class(next1);
    };
    Object.defineProperty(this.FunctionContFrame, "class", {
    enumerable: true,
      value: class FunctionContFrame {
        constructor(next) {
          this.next = next;
        }
        static [definitionMetadata] = ["class", "FunctionContFrame", ["next"]]; 
      }
    });
    this.HandlerContFrame = function HandlerContFrame(next1, nextHandler1, handler1) {
      return new HandlerContFrame.class(next1, nextHandler1, handler1);
    };
    Object.defineProperty(this.HandlerContFrame, "class", {
    enumerable: true,
      value: class HandlerContFrame {
        constructor(next, nextHandler, handler) {
          this.next = next;
          this.nextHandler = nextHandler;
          this.handler = handler;
        }
        static [definitionMetadata] = ["class", "HandlerContFrame", ["next", "nextHandler", "handler"]]; 
      }
    });
    this.ContTrace = function ContTrace(next1, last1, nextHandler1, lastHandler1, resumed1) {
      return new ContTrace.class(next1, last1, nextHandler1, lastHandler1, resumed1);
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
        static [definitionMetadata] = ["class", "ContTrace", ["next", "last", "nextHandler", "lastHandler", "resumed"]]; 
      }
    });
    this.EffectSig = function EffectSig(contTrace1, handler1, handlerFun1) {
      return new EffectSig.class(contTrace1, handler1, handlerFun1);
    };
    Object.defineProperty(this.EffectSig, "class", {
    enumerable: true,
      value: class EffectSig {
        constructor(contTrace, handler, handlerFun) {
          this.contTrace = contTrace;
          this.handler = handler;
          this.handlerFun = handlerFun;
        }
        static [definitionMetadata] = ["class", "EffectSig", ["contTrace", "handler", "handlerFun"]]; 
      }
    });
    this.NonLocalReturn = class NonLocalReturn {
      constructor() {}
      static [definitionMetadata] = ["class", "NonLocalReturn"]; 
    };
    this.FnLocalsInfo = function FnLocalsInfo(fnName1, locals1) {
      return new FnLocalsInfo.class(fnName1, locals1);
    };
    Object.defineProperty(this.FnLocalsInfo, "class", {
    enumerable: true,
      value: class FnLocalsInfo {
        constructor(fnName, locals) {
          this.fnName = fnName;
          this.locals = locals;
        }
        static [definitionMetadata] = ["class", "FnLocalsInfo", ["fnName", "locals"]]; 
      }
    });
    this.LocalVarInfo = function LocalVarInfo(localName1, value1) {
      return new LocalVarInfo.class(localName1, value1);
    };
    Object.defineProperty(this.LocalVarInfo, "class", {
    enumerable: true,
      value: class LocalVarInfo {
        constructor(localName, value) {
          this.localName = localName;
          this.value = value;
        }
        static [definitionMetadata] = ["class", "LocalVarInfo", ["localName", "value"]]; 
      }
    });
    this.stackLimit = 0;
    this.stackDepth = 0;
    this.stackOffset = 0;
    this.stackHandler = null;
    this.stackResume = null;
    const StackDelayHandler$class = class StackDelayHandler {
      constructor() {}
      delay() {
        let lambda;
        lambda = (undefined, function (k) {
          Runtime.stackResume = k;
          return runtime.Unit
        });
        return Runtime.mkEffect(this, lambda)
      }
      static [definitionMetadata] = ["object", "StackDelayHandler"]; 
    };
    this.StackDelayHandler = new StackDelayHandler$class;
    Object.defineProperty(this.StackDelayHandler, "class", {
    value: StackDelayHandler$class
    });
  }
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, lambda;
    tmp1 = got < expected;
    lambda = (undefined, function () {
      let lambda1;
      lambda1 = (undefined, function () {
        return got > expected
      });
      return runtime.short_and(isUB, lambda1)
    });
    scrut = runtime.short_or(tmp1, lambda);
    if (scrut === true) {
      scrut1 = functionName.length > 0;
      if (scrut1 === true) {
        tmp2 = " '" + functionName;
        tmp3 = tmp2 + "'";
      } else {
        tmp3 = "";
      }
      name = tmp3;
      tmp4 = "Function" + name;
      tmp5 = tmp4 + " expected ";
      if (isUB === true) {
        tmp6 = "";
      } else {
        tmp6 = "at least ";
      }
      tmp7 = tmp5 + tmp6;
      tmp8 = tmp7 + expected;
      tmp9 = tmp8 + " argument";
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp10 = "";
      } else {
        tmp10 = "s";
      }
      tmp11 = tmp9 + tmp10;
      tmp12 = tmp11 + " but got ";
      tmp13 = tmp12 + got;
      throw globalThis.Error(tmp13);
    } else {
      return runtime.Unit
    }
  } 
  static safeCall(x) {
    if (x === undefined) {
      return Runtime.Unit
    } else {
      return x
    }
  } 
  static checkCall(x1) {
    if (x1 === undefined) {
      throw globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value.");
    } else {
      return x1
    }
  } 
  static deboundMethod(mtdName, clsName) {
    let tmp1, tmp2, tmp3, tmp4;
    tmp1 = "[debinding error] Method '" + mtdName;
    tmp2 = tmp1 + "' of class '";
    tmp3 = tmp2 + clsName;
    tmp4 = tmp3 + "' was accessed without being called.";
    throw globalThis.Error(tmp4);
  } 
  static try(f) {
    let res, tmp1;
    tmp1 = runtime.safeCall(f());
    res = tmp1;
    if (res instanceof Runtime.EffectSig.class) {
      return runtime.safeCall(Runtime.EffectHandle(res))
    } else {
      return res
    }
  } 
  static printRaw(x2) {
    let tmp1;
    tmp1 = runtime.safeCall(Runtime.render(x2));
    return runtime.safeCall(globalThis.console.log(tmp1))
  } 
  static raisePrintStackEffect(showLocals) {
    return Runtime.mkEffect(Runtime.PrintStackEffect, showLocals)
  } 
  static topLevelEffect(tr, debug) {
    let scrut, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp7: while (true) {
      scrut = tr.handler === Runtime.PrintStackEffect;
      if (scrut === true) {
        tmp1 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
        tmp2 = runtime.safeCall(globalThis.console.log(tmp1));
        tmp3 = Runtime.resume(tr.contTrace);
        tmp4 = runtime.safeCall(tmp3(runtime.Unit));
        tr = tmp4;
        tmp5 = runtime.Unit;
        continue tmp7;
      } else {
        tmp5 = runtime.Unit;
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      tmp6 = "Error: Unhandled effect " + tr.handler.constructor.name;
      throw Runtime.showStackTrace(tmp6, tr, debug, false);
    } else {
      return tr
    }
  } 
  static showStackTrace(header, tr1, debug1, showLocals1) {
    let msg, curHandler, atTail, scrut, cur, scrut1, locals, curLocals, loc, loc1, localsMsg, scrut2, scrut3, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, lambda;
    msg = header;
    curHandler = tr1.contTrace;
    atTail = true;
    if (debug1 === true) {
      tmp21: while (true) {
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          tmp22: while (true) {
            scrut1 = cur !== null;
            if (scrut1 === true) {
              locals = cur.getLocals;
              tmp1 = locals.length - 1;
              tmp2 = runtime.safeCall(locals.at(tmp1));
              curLocals = tmp2;
              loc = cur.getLoc;
              if (loc === null) {
                tmp3 = "pc=" + cur.pc;
              } else {
                tmp3 = loc;
              }
              loc1 = tmp3;
              if (showLocals1 === true) {
                scrut2 = curLocals.locals.length > 0;
                if (scrut2 === true) {
                  lambda = (undefined, function (l) {
                    let tmp23, tmp24;
                    tmp23 = l.localName + "=";
                    tmp24 = Rendering.render(l.value);
                    return tmp23 + tmp24
                  });
                  tmp4 = runtime.safeCall(curLocals.locals.map(lambda));
                  tmp5 = runtime.safeCall(tmp4.join(", "));
                  tmp6 = " with locals: " + tmp5;
                } else {
                  tmp6 = "";
                }
              } else {
                tmp6 = "";
              }
              localsMsg = tmp6;
              tmp7 = "\n\tat " + curLocals.fnName;
              tmp8 = tmp7 + " (";
              tmp9 = tmp8 + loc1;
              tmp10 = tmp9 + ")";
              tmp11 = msg + tmp10;
              msg = tmp11;
              tmp12 = msg + localsMsg;
              msg = tmp12;
              cur = cur.next;
              atTail = false;
              tmp13 = runtime.Unit;
              continue tmp22;
            } else {
              tmp13 = runtime.Unit;
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut3 = curHandler !== null;
          if (scrut3 === true) {
            tmp14 = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp15 = msg + tmp14;
            msg = tmp15;
            atTail = false;
            tmp16 = runtime.Unit;
          } else {
            tmp16 = runtime.Unit;
          }
          tmp17 = tmp16;
          continue tmp21;
        } else {
          tmp17 = runtime.Unit;
        }
        break;
      }
      if (atTail === true) {
        tmp18 = msg + "\n\tat tail position";
        msg = tmp18;
        tmp19 = runtime.Unit;
      } else {
        tmp19 = runtime.Unit;
      }
      tmp20 = tmp19;
    } else {
      tmp20 = runtime.Unit;
    }
    return msg
  } 
  static showFunctionContChain(cont, hl, vis, reps) {
    let scrut, result, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp1 = cont.constructor.name + "(pc=";
      tmp2 = tmp1 + cont.pc;
      result = tmp2;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp11, tmp12;
        scrut3 = runtime.safeCall(m.has(cont));
        if (scrut3 === true) {
          tmp11 = ", " + marker;
          tmp12 = result + tmp11;
          result = tmp12;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      tmp3 = lambda;
      tmp4 = runtime.safeCall(hl.forEach(tmp3));
      scrut1 = runtime.safeCall(vis.has(cont));
      if (scrut1 === true) {
        tmp5 = reps + 1;
        reps = tmp5;
        scrut2 = reps > 10;
        if (scrut2 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)");
        } else {
          tmp6 = runtime.Unit;
        }
        tmp7 = result + ", REPEAT";
        result = tmp7;
        tmp8 = runtime.Unit;
      } else {
        tmp8 = runtime.safeCall(vis.add(cont));
      }
      tmp9 = result + ") -> ";
      tmp10 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp9 + tmp10
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
    let scrut, result, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, lambda;
    if (cont1 instanceof Runtime.HandlerContFrame.class) {
      result = cont1.handler.constructor.name;
      lambda = (undefined, function (m, marker) {
        let scrut3, tmp9, tmp10;
        scrut3 = runtime.safeCall(m.has(cont1));
        if (scrut3 === true) {
          tmp9 = ", " + marker;
          tmp10 = result + tmp9;
          result = tmp10;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      });
      tmp1 = lambda;
      tmp2 = runtime.safeCall(hl1.forEach(tmp1));
      scrut1 = runtime.safeCall(vis1.has(cont1));
      if (scrut1 === true) {
        tmp3 = reps1 + 1;
        reps1 = tmp3;
        scrut2 = reps1 > 10;
        if (scrut2 === true) {
          throw globalThis.Error("10 repeated continuation frame (loop?)");
        } else {
          tmp4 = runtime.Unit;
        }
        tmp5 = result + ", REPEAT";
        result = tmp5;
        tmp6 = runtime.Unit;
      } else {
        tmp6 = runtime.safeCall(vis1.add(cont1));
      }
      tmp7 = result + " -> ";
      tmp8 = Runtime.showFunctionContChain(cont1.next, hl1, vis1, reps1);
      return tmp7 + tmp8
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
    let tmp1, tmp2, tmp3;
    tmp1 = new globalThis.Map();
    tmp2 = new globalThis.Set();
    tmp3 = Runtime.showFunctionContChain(cont2, tmp1, tmp2, 0);
    return runtime.safeCall(globalThis.console.log(tmp3))
  } 
  static debugHandler(cont3) {
    let tmp1, tmp2, tmp3;
    tmp1 = new globalThis.Map();
    tmp2 = new globalThis.Set();
    tmp3 = Runtime.showHandlerContChain(cont3, tmp1, tmp2, 0);
    return runtime.safeCall(globalThis.console.log(tmp3))
  } 
  static debugContTrace(contTrace) {
    let scrut, scrut1, vis2, hl2, cur, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
    if (contTrace instanceof Runtime.ContTrace.class) {
      tmp1 = globalThis.console.log("resumed: ", contTrace.resumed);
      scrut = contTrace.last === contTrace;
      if (scrut === true) {
        tmp2 = runtime.safeCall(globalThis.console.log("<last is self>"));
      } else {
        tmp2 = runtime.Unit;
      }
      scrut1 = contTrace.lastHandler === contTrace;
      if (scrut1 === true) {
        tmp3 = runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      } else {
        tmp3 = runtime.Unit;
      }
      tmp4 = new globalThis.Set();
      vis2 = tmp4;
      tmp5 = new globalThis.Map();
      hl2 = tmp5;
      tmp6 = new globalThis.Set([
        contTrace.last
      ]);
      tmp7 = hl2.set("last", tmp6);
      tmp8 = new globalThis.Set([
        contTrace.lastHandler
      ]);
      tmp9 = hl2.set("last-handler", tmp8);
      tmp10 = Runtime.showFunctionContChain(contTrace.next, hl2, vis2, 0);
      tmp11 = runtime.safeCall(globalThis.console.log(tmp10));
      cur = contTrace.nextHandler;
      tmp16: while (true) {
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp12 = Runtime.showHandlerContChain(cur, hl2, vis2, 0);
          tmp13 = runtime.safeCall(globalThis.console.log(tmp12));
          cur = cur.nextHandler;
          tmp14 = runtime.Unit;
          continue tmp16;
        } else {
          tmp14 = runtime.Unit;
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    } else {
      tmp15 = runtime.safeCall(globalThis.console.log("Not a cont trace:"));
      return runtime.safeCall(globalThis.console.log(contTrace))
    }
  } 
  static debugEff(eff) {
    let tmp1, tmp2, tmp3, tmp4;
    if (eff instanceof Runtime.EffectSig.class) {
      tmp1 = runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      tmp2 = globalThis.console.log("handler: ", eff.handler.constructor.name);
      tmp3 = globalThis.console.log("handlerFun: ", eff.handlerFun);
      return Runtime.debugContTrace(eff.contTrace)
    } else {
      tmp4 = runtime.safeCall(globalThis.console.log("Not an effect:"));
      return runtime.safeCall(globalThis.console.log(eff))
    }
  } 
  static mkEffect(handler, handlerFun) {
    let res, tmp1, tmp2;
    tmp1 = new Runtime.ContTrace.class(null, null, null, null, false);
    tmp2 = new Runtime.EffectSig.class(tmp1, handler, handlerFun);
    res = tmp2;
    res.contTrace.last = res.contTrace;
    res.contTrace.lastHandler = res.contTrace;
    return res
  } 
  static handleBlockImpl(cur, handler1) {
    let handlerFrame, tmp1;
    tmp1 = new Runtime.HandlerContFrame.class(null, null, handler1);
    handlerFrame = tmp1;
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  } 
  static enterHandleBlock(handler2, body) {
    let cur1, tmp1;
    tmp1 = runtime.safeCall(body());
    cur1 = tmp1;
    if (cur1 instanceof Runtime.EffectSig.class) {
      return Runtime.handleBlockImpl(cur1, handler2)
    } else {
      return cur1
    }
  } 
  static handleEffects(cur1) {
    let nxt, scrut, tmp1, tmp2, tmp3;
    tmp4: while (true) {
      if (cur1 instanceof Runtime.EffectSig.class) {
        tmp1 = Runtime.handleEffect(cur1);
        nxt = tmp1;
        scrut = cur1 === nxt;
        if (scrut === true) {
          return cur1
        } else {
          cur1 = nxt;
          tmp2 = runtime.Unit;
        }
        tmp3 = tmp2;
        continue tmp4;
      } else {
        return cur1
      }
      break;
    }
    return tmp3
  } 
  static handleEffect(cur2) {
    let prevHandlerFrame, scrut, scrut1, scrut2, handlerFrame, saved, scrut3, scrut4, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    prevHandlerFrame = cur2.contTrace;
    tmp8: while (true) {
      scrut = prevHandlerFrame.nextHandler !== null;
      if (scrut === true) {
        scrut1 = prevHandlerFrame.nextHandler.handler !== cur2.handler;
        if (scrut1 === true) {
          prevHandlerFrame = prevHandlerFrame.nextHandler;
          tmp1 = runtime.Unit;
          continue tmp8;
        } else {
          tmp1 = runtime.Unit;
        }
      } else {
        tmp1 = runtime.Unit;
      }
      break;
    }
    scrut2 = prevHandlerFrame.nextHandler === null;
    if (scrut2 === true) {
      return cur2
    } else {
      tmp2 = runtime.Unit;
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    tmp3 = new Runtime.ContTrace.class(handlerFrame.next, cur2.contTrace.last, handlerFrame.nextHandler, cur2.contTrace.lastHandler, false);
    saved = tmp3;
    cur2.contTrace.last = handlerFrame;
    cur2.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    tmp4 = Runtime.resume(cur2.contTrace);
    tmp5 = runtime.safeCall(cur2.handlerFun(tmp4));
    cur2 = tmp5;
    if (cur2 instanceof Runtime.EffectSig.class) {
      scrut3 = saved.next !== null;
      if (scrut3 === true) {
        cur2.contTrace.last.next = saved.next;
        cur2.contTrace.last = saved.last;
        tmp6 = runtime.Unit;
      } else {
        tmp6 = runtime.Unit;
      }
      scrut4 = saved.nextHandler !== null;
      if (scrut4 === true) {
        cur2.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur2.contTrace.lastHandler = saved.lastHandler;
        tmp7 = runtime.Unit;
      } else {
        tmp7 = runtime.Unit;
      }
      return cur2
    } else {
      return Runtime.resumeContTrace(saved, cur2)
    }
  } 
  static resume(contTrace1) {
    return (value) => {
      let scrut, tmp1, tmp2;
      scrut = contTrace1.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption");
      } else {
        tmp1 = runtime.Unit;
      }
      contTrace1.resumed = true;
      tmp2 = Runtime.resumeContTrace(contTrace1, value);
      return Runtime.handleEffects(tmp2)
    }
  } 
  static resumeContTrace(contTrace2, value) {
    let cont4, handlerCont, scrut, scrut1, tmp1, tmp2, tmp3, tmp4, tmp5;
    cont4 = contTrace2.next;
    handlerCont = contTrace2.nextHandler;
    tmp6: while (true) {
      if (cont4 instanceof Runtime.FunctionContFrame.class) {
        tmp1 = runtime.safeCall(cont4.resume(value));
        value = tmp1;
        if (value instanceof Runtime.EffectSig.class) {
          value.contTrace.last.next = cont4.next;
          value.contTrace.lastHandler.nextHandler = handlerCont;
          scrut = contTrace2.last !== cont4;
          if (scrut === true) {
            value.contTrace.last = contTrace2.last;
            tmp2 = runtime.Unit;
          } else {
            tmp2 = runtime.Unit;
          }
          scrut1 = handlerCont !== null;
          if (scrut1 === true) {
            value.contTrace.lastHandler = contTrace2.lastHandler;
            tmp3 = runtime.Unit;
          } else {
            tmp3 = runtime.Unit;
          }
          return value
        } else {
          cont4 = cont4.next;
          tmp4 = runtime.Unit;
        }
        tmp5 = tmp4;
        continue tmp6;
      } else {
        if (handlerCont instanceof Runtime.HandlerContFrame.class) {
          cont4 = handlerCont.next;
          handlerCont = handlerCont.nextHandler;
          tmp5 = runtime.Unit;
          continue tmp6;
        } else {
          return value
        }
      }
      break;
    }
    return tmp5
  } 
  static checkDepth() {
    let scrut, tmp1, tmp2, lambda;
    tmp1 = Runtime.stackDepth - Runtime.stackOffset;
    tmp2 = tmp1 >= Runtime.stackLimit;
    lambda = (undefined, function () {
      return Runtime.stackHandler !== null
    });
    scrut = runtime.short_and(tmp2, lambda);
    if (scrut === true) {
      return runtime.safeCall(Runtime.stackHandler.delay())
    } else {
      return runtime.Unit
    }
  } 
  static resetDepth(tmp1, curDepth) {
    let scrut, tmp2;
    Runtime.stackDepth = curDepth;
    scrut = curDepth < Runtime.stackOffset;
    if (scrut === true) {
      Runtime.stackOffset = curDepth;
      tmp2 = runtime.Unit;
    } else {
      tmp2 = runtime.Unit;
    }
    return tmp1
  } 
  static runStackSafe(limit, f1) {
    let result, scrut, saved, tmp2, tmp3, tmp4;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackOffset = 0;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    tmp2 = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f1);
    result = tmp2;
    tmp5: while (true) {
      scrut = Runtime.stackResume !== null;
      if (scrut === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        Runtime.stackOffset = Runtime.stackDepth;
        tmp3 = runtime.safeCall(saved());
        result = tmp3;
        tmp4 = runtime.Unit;
        continue tmp5;
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    Runtime.stackLimit = 0;
    Runtime.stackDepth = 0;
    Runtime.stackOffset = 0;
    Runtime.stackHandler = null;
    return result
  }
  static [definitionMetadata] = ["module", "Runtime"]; 
});
let Runtime = Runtime1; export default Runtime;
