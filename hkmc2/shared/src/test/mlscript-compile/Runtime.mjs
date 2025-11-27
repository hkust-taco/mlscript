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
      resumeWith(value) {{
          let lambda; /** scoped **/
          const this$EffectHandle = this;
          lambda = (undefined, function () {{
              let tmp; /** scoped **/
              tmp = Runtime.resume(this$EffectHandle.reified.contTrace);
              return runtime.safeCall(tmp(value))
            }
          });
          return Runtime1.try(lambda)
        }
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
      static slice(xs, i, j) {{
          let tmp; /** scoped **/
          tmp = xs.length - j;
          return xs.slice(i, tmp)
        }
      } 
      static lazySlice(xs, i, j) {{
          let tmp; /** scoped **/
          tmp = LazyArray.dropLeftRight(i, j);
          return runtime.safeCall(tmp(xs))
        }
      } 
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      } 
      static get(xs, i) {{
          let scrut, scrut1, tmp, tmp1, tmp2; /** scoped **/
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
      static get(string, i) {{
          let scrut; /** scoped **/
          scrut = i >= string.length;
          if (scrut === true) {
            throw globalThis.RangeError("Str.get: index out of bounds")
          } else {
            return runtime.safeCall(string.at(i))
          }
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
      static indent() {{
          let scrut, prev, tmp; /** scoped **/
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
      } 
      static resetIndent(n) {{
          let scrut; /** scoped **/
          scrut = TraceLogger.enabled;
          if (scrut === true) {
            TraceLogger.indentLvl = n;
            return runtime.Unit
          } else {
            return runtime.Unit
          }
        }
      } 
      static log(msg) {{
          let scrut, tmp, tmp1, tmp2, tmp3, tmp4; /** scoped **/
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
      delay() {{
          let lambda; /** scoped **/
          lambda = (undefined, function (k) {
            Runtime.stackResume = k;
            return runtime.Unit
          });
          return Runtime.mkEffect(this, lambda)
        }
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
      zext() {{
          let tmp, tmp1; /** scoped **/
          tmp = Runtime.shl(1, 31);
          tmp1 = runtime.safeCall(Runtime.bitnot(tmp));
          return Runtime.bitand(this.#v, tmp1)
        }
      } 
      sext() {{
          let tmp; /** scoped **/
          tmp = Runtime.shl(1, 31);
          return Runtime.bitor(this.#v, tmp)
        }
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Int31", [null]]; 
    });
  }
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {{
      let scrut, name, tmp, lambda, lambda1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11; /** scoped **/
      tmp = got < expected;
      lambda = (undefined, function () {
        lambda1 = (undefined, function () {
          return got > expected
        });
        return runtime.short_and(isUB, lambda1)
      });
      scrut = runtime.short_or(tmp, lambda);
      if (scrut === true) {{
          let scrut1, scrut2, tmp12; /** scoped **/
          scrut1 = functionName.length > 0;
          if (scrut1 === true) {
            tmp12 = " '" + functionName;
            tmp1 = tmp12 + "'";
          } else {
            tmp1 = "";
          }
          name = tmp1;
          tmp2 = "Function" + name;
          tmp3 = tmp2 + " expected ";
          if (isUB === true) {
            tmp4 = "";
          } else {
            tmp4 = "at least ";
          }
          tmp5 = tmp3 + tmp4;
          tmp6 = tmp5 + expected;
          tmp7 = tmp6 + " argument";
          scrut2 = expected === 1;
          if (scrut2 === true) {
            tmp8 = "";
          } else {
            tmp8 = "s";
          }
          tmp9 = tmp7 + tmp8;
          tmp10 = tmp9 + " but got ";
          tmp11 = tmp10 + got;
          throw globalThis.Error(tmp11)
        }
      } else {
        return runtime.Unit
      }
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
  static deboundMethod(mtdName, clsName) {{
      let tmp, tmp1, tmp2, tmp3; /** scoped **/
      tmp = "[debinding error] Method '" + mtdName;
      tmp1 = tmp + "' of class '";
      tmp2 = tmp1 + clsName;
      tmp3 = tmp2 + "' was accessed without being called.";
      throw globalThis.Error(tmp3)
    }
  } 
  static try(f) {{
      let res; /** scoped **/
      res = runtime.safeCall(f());
      if (res instanceof Runtime.EffectSig.class) {
        return Runtime.EffectHandle(res)
      } else {
        return res
      }
    }
  } 
  static printRaw(x) {{
      let rcd, tmp; /** scoped **/
      rcd = globalThis.Object.freeze({
        indent: 2,
        breakLength: 76
      });
      tmp = Runtime.render(x, rcd);
      return runtime.safeCall(globalThis.console.log(tmp))
    }
  } 
  static raisePrintStackEffect(showLocals) {
    return Runtime.mkEffect(Runtime.PrintStackEffect, showLocals)
  } 
  static topLevelEffect(tr, debug) {{
      let tmp, tmp1; /** scoped **/
      tmp2: while (true) {{
          let scrut, tmp3, tmp4, tmp5, tmp6; /** scoped **/
          scrut = tr.handler === Runtime.PrintStackEffect;
          if (scrut === true) {
            tmp3 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
            tmp4 = runtime.safeCall(globalThis.console.log(tmp3));
            tmp5 = Runtime.resume(tr.contTrace);
            tmp6 = runtime.safeCall(tmp5(runtime.Unit));
            tr = tmp6;
            tmp = runtime.Unit;
            continue tmp2
          } else {
            tmp = runtime.Unit;
          }
        }
        break;
      }
      if (tr instanceof Runtime.EffectSig.class) {
        tmp1 = "Error: Unhandled effect " + tr.handler.constructor.name;
        throw Runtime.showStackTrace(tmp1, tr, debug, false)
      } else {
        return tr
      }
    }
  } 
  static showStackTrace(header, tr, debug, showLocals) {{
      let msg, curHandler, atTail, tmp, tmp1, tmp2; /** scoped **/
      msg = header;
      curHandler = tr.contTrace;
      atTail = true;
      if (debug === true) {{
          let tmp3; /** scoped **/
          tmp4: while (true) {{
              let scrut, cur, tmp5, tmp6; /** scoped **/
              scrut = curHandler !== null;
              if (scrut === true) {{
                  let scrut1, tmp7, tmp8; /** scoped **/
                  cur = curHandler.next;
                  tmp9: while (true) {{
                      let scrut2, locals, curLocals, loc, loc1, localsMsg, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18; /** scoped **/
                      scrut2 = cur !== null;
                      if (scrut2 === true) {{
                          let scrut3, lambda, tmp19, tmp20; /** scoped **/
                          locals = cur.getLocals;
                          tmp10 = locals.length - 1;
                          curLocals = runtime.safeCall(locals.at(tmp10));
                          loc = cur.getLoc;
                          if (loc === null) {
                            tmp11 = "pc=" + cur.pc;
                          } else {
                            tmp11 = loc;
                          }
                          loc1 = tmp11;
                          split_root$: {
                            split_1$: {
                              if (showLocals === true) {
                                scrut3 = curLocals.locals.length > 0;
                                if (scrut3 === true) {
                                  lambda = (undefined, function (l) {{
                                      let tmp21, tmp22; /** scoped **/
                                      tmp21 = l.localName + "=";
                                      tmp22 = Rendering.render(l.value);
                                      return tmp21 + tmp22
                                    }
                                  });
                                  tmp19 = runtime.safeCall(curLocals.locals.map(lambda));
                                  tmp20 = runtime.safeCall(tmp19.join(", "));
                                  tmp12 = " with locals: " + tmp20;
                                  break split_root$
                                } else {
                                  break split_1$
                                }
                              } else {
                                break split_1$
                              }
                            }
                            tmp12 = "";
                          }
                          localsMsg = tmp12;
                          tmp13 = "\n\tat " + curLocals.fnName;
                          tmp14 = tmp13 + " (";
                          tmp15 = tmp14 + loc1;
                          tmp16 = tmp15 + ")";
                          tmp17 = msg + tmp16;
                          msg = tmp17;
                          tmp18 = msg + localsMsg;
                          msg = tmp18;
                          cur = cur.next;
                          atTail = false;
                          tmp5 = runtime.Unit;
                          continue tmp9
                        }
                      } else {
                        tmp5 = runtime.Unit;
                      }
                    }
                    break;
                  }
                  curHandler = curHandler.nextHandler;
                  scrut1 = curHandler !== null;
                  if (scrut1 === true) {
                    tmp7 = "\n\twith handler " + curHandler.handler.constructor.name;
                    tmp8 = msg + tmp7;
                    msg = tmp8;
                    atTail = false;
                    tmp6 = runtime.Unit;
                  } else {
                    tmp6 = runtime.Unit;
                  }
                  tmp = tmp6;
                  continue tmp4
                }
              } else {
                tmp = runtime.Unit;
              }
            }
            break;
          }
          if (atTail === true) {
            tmp3 = msg + "\n\tat tail position";
            msg = tmp3;
            tmp1 = runtime.Unit;
          } else {
            tmp1 = runtime.Unit;
          }
          tmp2 = tmp1;
        }
      } else {
        tmp2 = runtime.Unit;
      }
      return msg
    }
  } 
  static showFunctionContChain(cont, hl, vis, reps) {{
      let result, tmp, lambda, tmp1, tmp2, tmp3, tmp4; /** scoped **/
      if (cont instanceof Runtime.FunctionContFrame.class) {{
          let scrut, tmp5, tmp6, tmp7; /** scoped **/
          tmp = cont.constructor.name + "(pc=";
          result = tmp + cont.pc;
          lambda = (undefined, function (m, marker) {{
              let scrut1, tmp8, tmp9; /** scoped **/
              scrut1 = runtime.safeCall(m.has(cont));
              if (scrut1 === true) {
                tmp8 = ", " + marker;
                tmp9 = result + tmp8;
                result = tmp9;
                return runtime.Unit
              } else {
                return runtime.Unit
              }
            }
          });
          tmp1 = runtime.safeCall(hl.forEach(lambda));
          scrut = runtime.safeCall(vis.has(cont));
          if (scrut === true) {{
              let scrut1; /** scoped **/
              tmp5 = reps + 1;
              reps = tmp5;
              scrut1 = reps > 10;
              if (scrut1 === true) {
                throw globalThis.Error("10 repeated continuation frame (loop?)")
              } else {
                tmp6 = runtime.Unit;
              }
              tmp7 = result + ", REPEAT";
              result = tmp7;
              tmp2 = runtime.Unit;
            }
          } else {
            tmp2 = runtime.safeCall(vis.add(cont));
          }
          tmp3 = result + ") -> ";
          tmp4 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
          return tmp3 + tmp4
        }
      } else {{
          let scrut; /** scoped **/
          scrut = cont === null;
          if (scrut === true) {
            return "(null)"
          } else {
            return "(NOT CONT)"
          }
        }
      }
    }
  } 
  static showHandlerContChain(cont, hl, vis, reps) {{
      let result, lambda, tmp, tmp1, tmp2, tmp3; /** scoped **/
      if (cont instanceof Runtime.HandlerContFrame.class) {{
          let scrut, tmp4, tmp5, tmp6; /** scoped **/
          result = cont.handler.constructor.name;
          lambda = (undefined, function (m, marker) {{
              let scrut1, tmp7, tmp8; /** scoped **/
              scrut1 = runtime.safeCall(m.has(cont));
              if (scrut1 === true) {
                tmp7 = ", " + marker;
                tmp8 = result + tmp7;
                result = tmp8;
                return runtime.Unit
              } else {
                return runtime.Unit
              }
            }
          });
          tmp = runtime.safeCall(hl.forEach(lambda));
          scrut = runtime.safeCall(vis.has(cont));
          if (scrut === true) {{
              let scrut1; /** scoped **/
              tmp4 = reps + 1;
              reps = tmp4;
              scrut1 = reps > 10;
              if (scrut1 === true) {
                throw globalThis.Error("10 repeated continuation frame (loop?)")
              } else {
                tmp5 = runtime.Unit;
              }
              tmp6 = result + ", REPEAT";
              result = tmp6;
              tmp1 = runtime.Unit;
            }
          } else {
            tmp1 = runtime.safeCall(vis.add(cont));
          }
          tmp2 = result + " -> ";
          tmp3 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
          return tmp2 + tmp3
        }
      } else {{
          let scrut; /** scoped **/
          scrut = cont === null;
          if (scrut === true) {
            return "(null)"
          } else {
            return "(NOT HANDLER CONT)"
          }
        }
      }
    }
  } 
  static debugCont(cont) {{
      let tmp, tmp1, tmp2; /** scoped **/
      tmp = globalThis.Object.freeze(new globalThis.Map());
      tmp1 = globalThis.Object.freeze(new globalThis.Set());
      tmp2 = Runtime.showFunctionContChain(cont, tmp, tmp1, 0);
      return runtime.safeCall(globalThis.console.log(tmp2))
    }
  } 
  static debugHandler(cont) {{
      let tmp, tmp1, tmp2; /** scoped **/
      tmp = globalThis.Object.freeze(new globalThis.Map());
      tmp1 = globalThis.Object.freeze(new globalThis.Set());
      tmp2 = Runtime.showHandlerContChain(cont, tmp, tmp1, 0);
      return runtime.safeCall(globalThis.console.log(tmp2))
    }
  } 
  static debugContTrace(contTrace) {{
      let vis, hl, cur, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12; /** scoped **/
      if (contTrace instanceof Runtime.ContTrace.class) {{
          let scrut, scrut1; /** scoped **/
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
          tmp13: while (true) {{
              let scrut2, tmp14, tmp15; /** scoped **/
              scrut2 = cur !== null;
              if (scrut2 === true) {
                tmp14 = Runtime.showHandlerContChain(cur, hl, vis, 0);
                tmp15 = runtime.safeCall(globalThis.console.log(tmp14));
                cur = cur.nextHandler;
                tmp11 = runtime.Unit;
                continue tmp13
              } else {
                tmp11 = runtime.Unit;
              }
            }
            break;
          }
          return runtime.safeCall(globalThis.console.log())
        }
      } else {
        tmp12 = runtime.safeCall(globalThis.console.log("Not a cont trace:"));
        return runtime.safeCall(globalThis.console.log(contTrace))
      }
    }
  } 
  static debugEff(eff) {{
      let tmp, tmp1, tmp2, tmp3; /** scoped **/
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
  } 
  static mkEffect(handler, handlerFun) {{
      let res, tmp; /** scoped **/
      tmp = new Runtime.ContTrace.class(null, null, null, null, false);
      res = new Runtime.EffectSig.class(tmp, handler, handlerFun);
      res.contTrace.last = res.contTrace;
      res.contTrace.lastHandler = res.contTrace;
      return res
    }
  } 
  static handleBlockImpl(cur, handler) {{
      let handlerFrame; /** scoped **/
      handlerFrame = new Runtime.HandlerContFrame.class(null, null, handler);
      cur.contTrace.lastHandler.nextHandler = handlerFrame;
      cur.contTrace.lastHandler = handlerFrame;
      cur.contTrace.last = handlerFrame;
      return Runtime.handleEffects(cur)
    }
  } 
  static enterHandleBlock(handler, body) {{
      let cur; /** scoped **/
      cur = runtime.safeCall(body());
      if (cur instanceof Runtime.EffectSig.class) {
        return Runtime.handleBlockImpl(cur, handler)
      } else {
        return cur
      }
    }
  } 
  static handleEffects(cur) {{
      let tmp; /** scoped **/
      tmp1: while (true) {{
          let nxt, tmp2; /** scoped **/
          if (cur instanceof Runtime.EffectSig.class) {{
              let scrut; /** scoped **/
              nxt = Runtime.handleEffect(cur);
              scrut = cur === nxt;
              if (scrut === true) {
                return cur
              } else {
                cur = nxt;
                tmp2 = runtime.Unit;
              }
              tmp = tmp2;
              continue tmp1
            }
          } else {
            return cur
          }
        }
        break;
      }
      return tmp
    }
  } 
  static handleEffect(cur) {{
      let prevHandlerFrame, scrut, handlerFrame, saved, tmp, tmp1, tmp2, tmp3, tmp4, tmp5; /** scoped **/
      prevHandlerFrame = cur.contTrace;
      tmp6: while (true) {{
          let scrut1, scrut2; /** scoped **/
          split_root$: {
            split_1$: {
              scrut1 = prevHandlerFrame.nextHandler !== null;
              if (scrut1 === true) {
                scrut2 = prevHandlerFrame.nextHandler.handler !== cur.handler;
                if (scrut2 === true) {
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
        }
        break;
      }
      scrut = prevHandlerFrame.nextHandler === null;
      if (scrut === true) {
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
      if (cur instanceof Runtime.EffectSig.class) {{
          let scrut1, scrut2; /** scoped **/
          scrut1 = saved.next !== null;
          if (scrut1 === true) {
            cur.contTrace.last.next = saved.next;
            cur.contTrace.last = saved.last;
            tmp4 = runtime.Unit;
          } else {
            tmp4 = runtime.Unit;
          }
          scrut2 = saved.nextHandler !== null;
          if (scrut2 === true) {
            cur.contTrace.lastHandler.nextHandler = saved.nextHandler;
            cur.contTrace.lastHandler = saved.lastHandler;
            tmp5 = runtime.Unit;
          } else {
            tmp5 = runtime.Unit;
          }
          return cur
        }
      } else {
        return Runtime.resumeContTrace(saved, cur)
      }
    }
  } 
  static resume(contTrace) {
    return (value) => {{
        let scrut, tmp, tmp1; /** scoped **/
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
  } 
  static resumeContTrace(contTrace, value) {{
      let cont, handlerCont, curDepth, tmp; /** scoped **/
      cont = contTrace.next;
      handlerCont = contTrace.nextHandler;
      curDepth = Runtime.stackDepth;
      tmp1: while (true) {{
          let tmp2, tmp3; /** scoped **/
          if (cont instanceof Runtime.FunctionContFrame.class) {{
              let tmp4, tmp5; /** scoped **/
              tmp2 = runtime.safeCall(cont.resume(value));
              value = tmp2;
              Runtime.stackDepth = curDepth;
              if (value instanceof Runtime.EffectSig.class) {{
                  let scrut, scrut1; /** scoped **/
                  value.contTrace.last.next = cont.next;
                  value.contTrace.lastHandler.nextHandler = handlerCont;
                  scrut = contTrace.last !== cont;
                  if (scrut === true) {
                    value.contTrace.last = contTrace.last;
                    tmp4 = runtime.Unit;
                  } else {
                    tmp4 = runtime.Unit;
                  }
                  scrut1 = handlerCont !== null;
                  if (scrut1 === true) {
                    value.contTrace.lastHandler = contTrace.lastHandler;
                    tmp5 = runtime.Unit;
                  } else {
                    tmp5 = runtime.Unit;
                  }
                  return value
                }
              } else {
                cont = cont.next;
                tmp3 = runtime.Unit;
              }
              tmp = tmp3;
              continue tmp1
            }
          } else {
            if (handlerCont instanceof Runtime.HandlerContFrame.class) {
              cont = handlerCont.next;
              handlerCont = handlerCont.nextHandler;
              tmp = runtime.Unit;
              continue tmp1
            } else {
              return value
            }
          }
        }
        break;
      }
      return tmp
    }
  } 
  static checkDepth() {{
      let scrut, tmp, lambda; /** scoped **/
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
  } 
  static runStackSafe(limit, f) {{
      let result, tmp; /** scoped **/
      Runtime.stackLimit = limit;
      Runtime.stackDepth = 1;
      Runtime.stackHandler = Runtime.StackDelayHandler;
      result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
      Runtime.stackDepth = 1;
      tmp1: while (true) {{
          let scrut, saved, tmp2; /** scoped **/
          scrut = Runtime.stackResume !== null;
          if (scrut === true) {
            saved = Runtime.stackResume;
            Runtime.stackResume = null;
            tmp2 = runtime.safeCall(saved());
            result = tmp2;
            Runtime.stackDepth = 1;
            tmp = runtime.Unit;
            continue tmp1
          } else {
            tmp = runtime.Unit;
          }
        }
        break;
      }
      Runtime.stackLimit = 0;
      Runtime.stackDepth = 0;
      Runtime.stackHandler = null;
      return result
    }
  } 
  static plus_impl(lhs, rhs) {{
      let tmp; /** scoped **/
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
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Runtime"]; 
});
let Runtime = Runtime1; export default Runtime;
