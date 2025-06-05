import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
let Runtime1;
(class Runtime {
  static {
    Runtime1 = Runtime;
    const Unit$class = class Unit {
      constructor() {}
      toString() {
        return "()"
      }
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    this.try_catch = RuntimeJS.try_catch;
    this.EffectHandle = function EffectHandle(_reified1) {
      return new EffectHandle.class(_reified1);
    };
    this.EffectHandle.class = class EffectHandle {
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
      toString() { return "EffectHandle(" + "" + ")"; }
    };
    this.MatchResult = function MatchResult(captures1) {
      return new MatchResult.class(captures1);
    };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
      }
      toString() { return "MatchResult(" + runtime.render(this.captures) + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) {
      return new MatchFailure.class(errors1);
    };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return "MatchFailure(" + runtime.render(this.errors) + ")"; }
    };
    (class Tuple {
      static {
        Runtime.Tuple = Tuple;
      }
      static slice(xs, i, j) {
        let tmp;
        tmp = xs.length - j;
        return runtime.safeCall(globalThis.Array.prototype.slice.call(xs, i, tmp))
      } 
      static get(xs1, i1) {
        let scrut;
        scrut = i1 >= xs1.length;
        if (scrut === true) {
          throw globalThis.RangeError("Tuple.get: index out of bounds");
        } else {
          return globalThis.Array.prototype.at.call(xs1, i1)
        }
      }
      static toString() { return "Tuple"; }
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
      static toString() { return "Str"; }
    });
    this.render = Rendering.render;
    (class TraceLogger {
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
      static toString() { return "TraceLogger"; }
    });
    const FatalEffect$class = class FatalEffect {
      constructor() {}
      toString() { return "FatalEffect"; }
    };
    this.FatalEffect = new FatalEffect$class;
    this.FatalEffect.class = FatalEffect$class;
    const PrintStackEffect$class = class PrintStackEffect {
      constructor() {}
      toString() { return "PrintStackEffect"; }
    };
    this.PrintStackEffect = new PrintStackEffect$class;
    this.PrintStackEffect.class = PrintStackEffect$class;
    this.FunctionContFrame = function FunctionContFrame(next1) {
      return new FunctionContFrame.class(next1);
    };
    this.FunctionContFrame.class = class FunctionContFrame {
      constructor(next) {
        this.next = next;
      }
      toString() { return "FunctionContFrame(" + runtime.render(this.next) + ")"; }
    };
    this.HandlerContFrame = function HandlerContFrame(next1, nextHandler1, handler1) {
      return new HandlerContFrame.class(next1, nextHandler1, handler1);
    };
    this.HandlerContFrame.class = class HandlerContFrame {
      constructor(next, nextHandler, handler) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.handler = handler;
      }
      toString() { return "HandlerContFrame(" + runtime.render(this.next) + ", " + runtime.render(this.nextHandler) + ", " + runtime.render(this.handler) + ")"; }
    };
    this.ContTrace = function ContTrace(next1, last1, nextHandler1, lastHandler1, resumed1) {
      return new ContTrace.class(next1, last1, nextHandler1, lastHandler1, resumed1);
    };
    this.ContTrace.class = class ContTrace {
      constructor(next, last, nextHandler, lastHandler, resumed) {
        this.next = next;
        this.last = last;
        this.nextHandler = nextHandler;
        this.lastHandler = lastHandler;
        this.resumed = resumed;
      }
      toString() { return "ContTrace(" + runtime.render(this.next) + ", " + runtime.render(this.last) + ", " + runtime.render(this.nextHandler) + ", " + runtime.render(this.lastHandler) + ", " + runtime.render(this.resumed) + ")"; }
    };
    this.EffectSig = function EffectSig(contTrace1, handler1, handlerFun1) {
      return new EffectSig.class(contTrace1, handler1, handlerFun1);
    };
    this.EffectSig.class = class EffectSig {
      constructor(contTrace, handler, handlerFun) {
        this.contTrace = contTrace;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return "EffectSig(" + runtime.render(this.contTrace) + ", " + runtime.render(this.handler) + ", " + runtime.render(this.handlerFun) + ")"; }
    };
    this.NonLocalReturn = class NonLocalReturn {
      constructor() {}
      toString() { return "NonLocalReturn"; }
    };
    this.FnLocalsInfo = function FnLocalsInfo(fnName1, locals1) {
      return new FnLocalsInfo.class(fnName1, locals1);
    };
    this.FnLocalsInfo.class = class FnLocalsInfo {
      constructor(fnName, locals) {
        this.fnName = fnName;
        this.locals = locals;
      }
      toString() { return "FnLocalsInfo(" + runtime.render(this.fnName) + ", " + runtime.render(this.locals) + ")"; }
    };
    this.LocalVarInfo = function LocalVarInfo(localName1, value1) {
      return new LocalVarInfo.class(localName1, value1);
    };
    this.LocalVarInfo.class = class LocalVarInfo {
      constructor(localName, value) {
        this.localName = localName;
        this.value = value;
      }
      toString() { return "LocalVarInfo(" + runtime.render(this.localName) + ", " + runtime.render(this.value) + ")"; }
    };
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
      toString() { return "StackDelayHandler"; }
    };
    this.StackDelayHandler = new StackDelayHandler$class;
    this.StackDelayHandler.class = StackDelayHandler$class;
  }
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    tmp = got < expected;
    tmp1 = got > expected;
    tmp2 = isUB && tmp1;
    scrut = tmp || tmp2;
    if (scrut === true) {
      scrut1 = functionName.length > 0;
      if (scrut1 === true) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      name = tmp4;
      tmp5 = "Function" + name;
      tmp6 = tmp5 + " expected ";
      if (isUB === true) {
        tmp7 = "";
      } else {
        tmp7 = "at least ";
      }
      tmp8 = tmp6 + tmp7;
      tmp9 = tmp8 + expected;
      tmp10 = tmp9 + " argument";
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp11 = "";
      } else {
        tmp11 = "s";
      }
      tmp12 = tmp10 + tmp11;
      tmp13 = tmp12 + " but got ";
      tmp14 = tmp13 + got;
      throw globalThis.Error(tmp14);
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
    let tmp, tmp1, tmp2, tmp3;
    tmp = "[debinding error] Method '" + mtdName;
    tmp1 = tmp + "' of class '";
    tmp2 = tmp1 + clsName;
    tmp3 = tmp2 + "' was accessed without being called.";
    throw globalThis.Error(tmp3);
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
        continue tmp6;
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      tmp5 = "Error: Unhandled effect " + tr.handler.constructor.name;
      throw Runtime.showStackTrace(tmp5, tr, debug, false);
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
              continue tmp21;
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
          continue tmp20;
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
          throw globalThis.Error("10 repeated continuation frame (loop?)");
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
          throw globalThis.Error("10 repeated continuation frame (loop?)");
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
    tmp = new globalThis.Map();
    tmp1 = new globalThis.Set();
    tmp2 = Runtime.showFunctionContChain(cont2, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  } 
  static debugHandler(cont3) {
    let tmp, tmp1, tmp2;
    tmp = new globalThis.Map();
    tmp1 = new globalThis.Set();
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
      tmp3 = new globalThis.Set();
      vis2 = tmp3;
      tmp4 = new globalThis.Map();
      hl2 = tmp4;
      tmp5 = new globalThis.Set([
        contTrace.last
      ]);
      tmp6 = hl2.set("last", tmp5);
      tmp7 = new globalThis.Set([
        contTrace.lastHandler
      ]);
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
          continue tmp15;
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
        continue tmp3;
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
          continue tmp7;
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
        throw globalThis.Error("Multiple resumption");
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
        continue tmp5;
      } else {
        if (handlerCont instanceof Runtime.HandlerContFrame.class) {
          cont4 = handlerCont.next;
          handlerCont = handlerCont.nextHandler;
          tmp4 = runtime.Unit;
          continue tmp5;
        } else {
          return value
        }
      }
      break;
    }
    return tmp4
  } 
  static checkDepth() {
    let scrut, tmp, tmp1, tmp2;
    tmp = Runtime.stackDepth - Runtime.stackOffset;
    tmp1 = tmp >= Runtime.stackLimit;
    tmp2 = Runtime.stackHandler !== null;
    scrut = tmp1 && tmp2;
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
        continue tmp4;
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
  static toString() { return "Runtime"; }
});
let Runtime = Runtime1; export default Runtime;
