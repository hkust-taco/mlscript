import runtime from "./Runtime.mjs";
let Runtime1;
Runtime1 = class Runtime {
  static {
    const Unit$class = class Unit {
      constructor() {}
      toString() {
        return "()"
      }
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    this.FunctionContFrame = function FunctionContFrame(next1) { return new FunctionContFrame.class(next1); };
    this.FunctionContFrame.class = class FunctionContFrame {
      constructor(next) {
        this.next = next;
      }
      toString() { return "FunctionContFrame(" + globalThis.Predef.render(this.next) + ")"; }
    };
    this.HandlerContFrame = function HandlerContFrame(next1, nextHandler1, handler1) { return new HandlerContFrame.class(next1, nextHandler1, handler1); };
    this.HandlerContFrame.class = class HandlerContFrame {
      constructor(next, nextHandler, handler) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.handler = handler;
      }
      toString() { return "HandlerContFrame(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.nextHandler) + ", " + globalThis.Predef.render(this.handler) + ")"; }
    };
    this.ContTrace = function ContTrace(next1, last1, nextHandler1, lastHandler1, resumed1) { return new ContTrace.class(next1, last1, nextHandler1, lastHandler1, resumed1); };
    this.ContTrace.class = class ContTrace {
      constructor(next, last, nextHandler, lastHandler, resumed) {
        this.next = next;
        this.last = last;
        this.nextHandler = nextHandler;
        this.lastHandler = lastHandler;
        this.resumed = resumed;
      }
      toString() { return "ContTrace(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.last) + ", " + globalThis.Predef.render(this.nextHandler) + ", " + globalThis.Predef.render(this.lastHandler) + ", " + globalThis.Predef.render(this.resumed) + ")"; }
    };
    this.EffectSig = function EffectSig(contTrace1, handler1, handlerFun1) { return new EffectSig.class(contTrace1, handler1, handlerFun1); };
    this.EffectSig.class = class EffectSig {
      constructor(contTrace, handler, handlerFun) {
        this.contTrace = contTrace;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return "EffectSig(" + globalThis.Predef.render(this.contTrace) + ", " + globalThis.Predef.render(this.handler) + ", " + globalThis.Predef.render(this.handlerFun) + ")"; }
    };
    this.Return = function Return(value1) { return new Return.class(value1); };
    this.Return.class = class Return {
      constructor(value) {
        this.value = value;
      }
      toString() { return "Return(" + globalThis.Predef.render(this.value) + ")"; }
    };
    this.stackLimit = 0;
    this.stackDepth = 0;
    this.stackOffset = 0;
    this.stackHandler = null;
    this.StackDelay = class StackDelay {
      constructor() {}
      toString() { return "StackDelay"; }
    };
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
  static showFunctionContChain(cont, hl, vis, reps) {
    let scrut, result, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont.constructor.name + "(pc=";
      tmp1 = tmp + cont.pc;
      result = tmp1;
      tmp2 = (m, marker) => {
        let scrut4, tmp12, tmp13;
        scrut4 = runtime.safeCall(m.has(cont));
        if (scrut4 === true) {
          tmp12 = ", " + marker;
          tmp13 = result + tmp12;
          result = tmp13;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      };
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
      scrut3 = cont.completed;
      if (scrut3 === true) {
        tmp8 = result + ", COMPLETED";
        result = tmp8;
        tmp9 = runtime.Unit;
      } else {
        tmp9 = runtime.Unit;
      }
      tmp10 = result + ") -> ";
      tmp11 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp10 + tmp11
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
    let scrut, result, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (cont1 instanceof Runtime.HandlerContFrame.class) {
      result = cont1.handler.constructor.name;
      tmp = (m, marker) => {
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
      };
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
    let handlerFrame, nxt, scrut, tmp, tmp1, tmp2, tmp3;
    tmp = new Runtime.HandlerContFrame.class(null, null, handler1);
    handlerFrame = tmp;
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    tmp4: while (true) {
      if (cur instanceof Runtime.EffectSig.class) {
        tmp1 = Runtime.handleEffect(cur);
        nxt = tmp1;
        scrut = cur === nxt;
        if (scrut === true) {
          return cur
        } else {
          cur = nxt;
          tmp2 = runtime.Unit;
        }
        tmp3 = tmp2;
        continue tmp4;
      } else {
        return cur
      }
      break;
    }
    return tmp3
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
  static handleEffect(cur1) {
    let prevHandlerFrame, scrut, scrut1, scrut2, handlerFrame, saved, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    prevHandlerFrame = cur1.contTrace;
    tmp7: while (true) {
      scrut = prevHandlerFrame.nextHandler !== null;
      if (scrut === true) {
        scrut1 = prevHandlerFrame.nextHandler.handler !== cur1.handler;
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
      return cur1
    } else {
      tmp1 = runtime.Unit;
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    tmp2 = new Runtime.ContTrace.class(handlerFrame.next, cur1.contTrace.last, handlerFrame.nextHandler, cur1.contTrace.lastHandler, false);
    saved = tmp2;
    cur1.contTrace.last = handlerFrame;
    cur1.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    tmp3 = Runtime.resume(cur1.contTrace);
    tmp4 = runtime.safeCall(cur1.handlerFun(tmp3));
    cur1 = tmp4;
    if (cur1 instanceof Runtime.EffectSig.class) {
      scrut3 = saved.next !== null;
      if (scrut3 === true) {
        cur1.contTrace.last.next = saved.next;
        cur1.contTrace.last = saved.last;
        tmp5 = runtime.Unit;
      } else {
        tmp5 = runtime.Unit;
      }
      scrut4 = saved.nextHandler !== null;
      if (scrut4 === true) {
        cur1.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur1.contTrace.lastHandler = saved.lastHandler;
        tmp6 = runtime.Unit;
      } else {
        tmp6 = runtime.Unit;
      }
      return cur1
    } else {
      return Runtime.resumeContTrace(saved, cur1)
    }
  } 
  static resume(contTrace1) {
    return (value) => {
      let scrut, tmp;
      scrut = contTrace1.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption");
      } else {
        tmp = runtime.Unit;
      }
      contTrace1.resumed = true;
      return Runtime.resumeContTrace(contTrace1, value)
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
      return runtime.safeCall(Runtime.stackHandler.perform())
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
  static toString() { return "Runtime"; }
};
let Runtime = Runtime1; export default Runtime;
