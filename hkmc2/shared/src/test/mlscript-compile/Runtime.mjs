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
    this.EffectTrace = function EffectTrace(contTrace, lastSegmentBuf, handler, handlerFun) {
      return globalThis.Object.freeze(new EffectTrace.class(contTrace, lastSegmentBuf, handler, handlerFun));
    };
    (class EffectTrace {
      static {
        Runtime.EffectTrace.class = this
      }
      constructor(contTrace, lastSegmentBuf, handler, handlerFun) {
        this.contTrace = contTrace;
        this.lastSegmentBuf = lastSegmentBuf;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectTrace", ["contTrace", "lastSegmentBuf", "handler", "handlerFun"]]; 
    });
    this.ContTrace = function ContTrace(funStack, lastStack, resumed) {
      return globalThis.Object.freeze(new ContTrace.class(funStack, lastStack, resumed));
    };
    (class ContTrace {
      static {
        Runtime.ContTrace.class = this
      }
      constructor(funStack, lastStack, resumed) {
        this.funStack = funStack;
        this.lastStack = lastStack;
        this.resumed = resumed;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "ContTrace", ["funStack", "lastStack", "resumed"]]; 
    });
    this.FunStack = function FunStack(segHead, segLast, handler, nextStack) {
      return globalThis.Object.freeze(new FunStack.class(segHead, segLast, handler, nextStack));
    };
    (class FunStack {
      static {
        Runtime.FunStack.class = this
      }
      constructor(segHead, segLast, handler, nextStack) {
        this.segHead = segHead;
        this.segLast = segLast;
        this.handler = handler;
        this.nextStack = nextStack;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunStack", ["segHead", "segLast", "handler", "nextStack"]]; 
    });
    this.StackSegment = function StackSegment(buf, off, nextSegment) {
      return globalThis.Object.freeze(new StackSegment.class(buf, off, nextSegment));
    };
    (class StackSegment {
      static {
        Runtime.StackSegment.class = this
      }
      constructor(buf, off, nextSegment) {
        this.buf = buf;
        this.off = off;
        this.nextSegment = nextSegment;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "StackSegment", ["buf", "off", "nextSegment"]]; 
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
    (class NewEffect {
      static {
        new this
      }
      constructor() {
        Runtime.NewEffect = this;
        Object.defineProperty(this, "class", {
          value: NewEffect
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "NewEffect"]; 
    });
    this.Unwind = function Unwind(ret) {
      return globalThis.Object.freeze(new Unwind.class(ret));
    };
    (class Unwind {
      static {
        Runtime.Unwind.class = this
      }
      constructor(ret) {
        this.ret = ret;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Unwind", ["ret"]]; 
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
    let tr, v, scrut, tmp, tmp1, tmp2;
    tr = Runtime.curEffect;
    v = null;
    lbl: while (true) {
      let scrut1, scrut2, tmp3, tmp4, tmp5, tmp6;
      split_root$: {
        split_1$: {
          scrut1 = tr !== null;
          if (scrut1 === true) {
            scrut2 = tr.handler === Runtime.PrintStackEffect;
            if (scrut2 === true) {
              tmp3 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
              tmp4 = runtime.safeCall(globalThis.console.log(tmp3));
              Runtime.curEffect = null;
              tmp5 = Runtime.resume(tr.contTrace);
              tmp6 = runtime.safeCall(tmp5(runtime.Unit));
              v = tmp6;
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
    scrut = tr !== null;
    if (scrut === true) {
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
    let msg, stack, atTail, tmp, tmp1, tmp2, tmp3;
    msg = header;
    stack = tr.contTrace.funStack;
    atTail = true;
    if (debug === true) {
      lbl: while (true) {
        let scrut, curSeg, scrut1, tmp4, tmp5, tmp6, tmp7;
        scrut = stack !== null;
        if (scrut === true) {
          curSeg = stack.segHead;
          lbl1: while (true) {
            let scrut2, curBuf, curOff, curBufLen, tmp8;
            scrut2 = curSeg !== null;
            if (scrut2 === true) {
              curBuf = curSeg.buf;
              curOff = curSeg.off;
              curBufLen = curBuf.length;
              lbl2: while (true) {
                let scrut3, dbgInfo, nme, loc, x, i, argListLength, i1, scrut4, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
                scrut3 = curOff < curBufLen;
                if (scrut3 === true) {
                  tmp9 = curOff + 3;
                  dbgInfo = curBuf.at(tmp9);
                  nme = dbgInfo.at(0);
                  tmp10 = curOff + 2;
                  x = curBuf.at(tmp10);
                  if (x === null) {
                    tmp11 = curOff + 1;
                    tmp12 = "pc=" + curBuf.at(tmp11);
                  } else {
                    tmp12 = x;
                  }
                  loc = tmp12;
                  i = 0;
                  tmp13 = curOff + 5;
                  argListLength = curBuf.at(tmp13);
                  tmp14 = "\n\tat " + nme;
                  tmp15 = tmp14 + " (";
                  tmp16 = tmp15 + loc;
                  tmp17 = tmp16 + ")";
                  tmp18 = msg + tmp17;
                  msg = tmp18;
                  tmp19 = curOff + 6;
                  curOff = tmp19;
                  lbl3: while (true) {
                    let scrut5, tmp26, tmp27, tmp28;
                    scrut5 = i < argListLength;
                    if (scrut5 === true) {
                      tmp26 = curBuf.at(curOff) + 1;
                      tmp27 = curOff + tmp26;
                      curOff = tmp27;
                      tmp28 = i + 1;
                      i = tmp28;
                      tmp20 = runtime.Unit;
                      continue lbl3
                    } else {
                      tmp20 = runtime.Unit;
                    }
                    break;
                  }
                  split_root$: {
                    split_1$: {
                      if (showLocals === true) {
                        scrut4 = dbgInfo.length > 1;
                        if (scrut4 === true) {
                          tmp21 = msg + " with locals: ";
                          msg = tmp21;
                          i1 = 1;
                          lbl4: while (true) {
                            let scrut6, scrut7, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37;
                            scrut6 = i1 < dbgInfo.length;
                            if (scrut6 === true) {
                              scrut7 = i1 !== 1;
                              if (scrut7 === true) {
                                tmp29 = msg + ", ";
                                msg = tmp29;
                                tmp30 = runtime.Unit;
                              } else {
                                tmp30 = runtime.Unit;
                              }
                              tmp31 = i1 + 1;
                              tmp32 = dbgInfo.at(tmp31) + "=";
                              tmp33 = curOff + 1;
                              tmp34 = tmp33 + dbgInfo.at(i1);
                              tmp35 = tmp32 + curBuf.at(tmp34);
                              tmp36 = msg + tmp35;
                              msg = tmp36;
                              tmp37 = i1 + 1;
                              i1 = tmp37;
                              tmp22 = runtime.Unit;
                              continue lbl4
                            } else {
                              tmp22 = runtime.Unit;
                            }
                            break;
                          }
                          tmp23 = tmp22;
                          break split_root$
                        } else {
                          break split_1$
                        }
                      } else {
                        break split_1$
                      }
                    }
                    tmp23 = runtime.Unit;
                  }
                  tmp24 = curBuf.at(curOff) + 1;
                  tmp25 = curOff + tmp24;
                  curOff = tmp25;
                  atTail = false;
                  tmp8 = runtime.Unit;
                  continue lbl2
                } else {
                  tmp8 = runtime.Unit;
                }
                break;
              }
              curSeg = curSeg.nextSegment;
              tmp4 = runtime.Unit;
              continue lbl1
            } else {
              tmp4 = runtime.Unit;
            }
            break;
          }
          scrut1 = stack.handler !== null;
          if (scrut1 === true) {
            tmp5 = "\n\twith handler " + stack.handler.constructor.name;
            tmp6 = msg + tmp5;
            msg = tmp6;
            atTail = false;
            tmp7 = runtime.Unit;
          } else {
            tmp7 = runtime.Unit;
          }
          stack = stack.nextStack;
          tmp = runtime.Unit;
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
  static debugEff(eff) {
    let tmp;
    tmp = Runtime.showStackTrace("Debug Effect: ", eff, true, false);
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static mkEffect(handler, handlerFun) {
    let buf, seg, stack, cont, tmp;
    buf = [];
    seg = new Runtime.StackSegment.class(buf, 0, null);
    stack = new Runtime.FunStack.class(seg, seg, null, null);
    cont = new Runtime.ContTrace.class(stack, stack, false);
    tmp = new Runtime.EffectTrace.class(cont, buf, handler, handlerFun);
    Runtime.curEffect = tmp;
    return runtime.Unit
  } 
  static enterHandleBlock(handler, body) {
    let tmp, scrut, buf, seg, newStack, tmp1;
    tmp = runtime.safeCall(body());
    scrut = Runtime.curEffect === null;
    if (scrut === true) {
      return tmp
    } else {
      tmp1 = runtime.Unit;
    }
    buf = [];
    seg = new Runtime.StackSegment.class(buf, 0, null);
    newStack = new Runtime.FunStack.class(seg, seg, null, null);
    Runtime.curEffect.contTrace.lastStack.handler = handler;
    Runtime.curEffect.contTrace.lastStack.nextStack = newStack;
    Runtime.curEffect.contTrace.lastStack = newStack;
    Runtime.curEffect.lastSegmentBuf = buf;
    return Runtime.handleEffects()
  } 
  static handleEffects() {
    let tmp;
    lbl: while (true) {
      let scrut, ret, arg$Unwind$0$;
      scrut = Runtime.handleEffect();
      if (scrut instanceof Runtime.NewEffect.class) {
        tmp = 1;
        continue lbl
      } else if (scrut instanceof Runtime.Unwind.class) {
        arg$Unwind$0$ = scrut.ret;
        ret = arg$Unwind$0$;
        return ret
      } else {
        tmp = runtime.Unit;
      }
      break;
    }
    return tmp
  } 
  static handleEffect() {
    let stack, scrut, saved, newBuf, newSeg, newStack, k, f, savedDepth, res, scrut1, scrut2, tmp, tmp1, tmp2, tmp3;
    stack = Runtime.curEffect.contTrace.funStack;
    lbl: while (true) {
      let scrut3, scrut4;
      split_root$: {
        split_1$: {
          scrut3 = stack !== null;
          if (scrut3 === true) {
            scrut4 = stack.handler !== Runtime.curEffect.handler;
            if (scrut4 === true) {
              stack = stack.nextStack;
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
    scrut = stack === null;
    if (scrut === true) {
      return Runtime.Unwind(runtime.Unit)
    } else {
      tmp1 = runtime.Unit;
    }
    saved = new Runtime.ContTrace.class(stack.nextStack, Runtime.curEffect.contTrace.lastStack, false);
    newBuf = [];
    newSeg = new Runtime.StackSegment.class(newBuf, 0, null);
    newStack = new Runtime.FunStack.class(newSeg, newSeg, null, null);
    Runtime.curEffect.contTrace.lastStack = newStack;
    Runtime.curEffect.lastSegmentBuf = newBuf;
    stack.nextStack = newStack;
    k = Runtime.resume(Runtime.curEffect.contTrace);
    f = Runtime.curEffect.handlerFun;
    savedDepth = Runtime.stackDepth;
    Runtime.curEffect = null;
    tmp2 = Runtime.stackDepth + 30;
    Runtime.stackDepth = tmp2;
    res = runtime.safeCall(f(k));
    Runtime.stackDepth = savedDepth;
    scrut1 = Runtime.curEffect !== null;
    if (scrut1 === true) {
      scrut2 = saved.funStack === saved.lastStack;
      if (scrut2 === true) {
        saved.lastStack = Runtime.curEffect.contTrace.lastStack;
        tmp3 = runtime.Unit;
      } else {
        tmp3 = runtime.Unit;
      }
      Runtime.curEffect.contTrace.lastStack.segLast.nextSegment = saved.funStack.segHead;
      Runtime.curEffect.contTrace.lastStack.segLast = saved.funStack.segLast;
      Runtime.curEffect.contTrace.lastStack.handler = saved.funStack.handler;
      Runtime.curEffect.contTrace.lastStack.nextStack = saved.funStack.nextStack;
      Runtime.curEffect.contTrace.lastStack = saved.lastStack;
      Runtime.curEffect.lastSegmentBuf = saved.lastStack.segLast.buf;
      return Runtime.NewEffect
    } else {
      return Runtime.resumeContTrace(saved, res)
    }
  } 
  static resume(contTrace) {
    return (value) => {
      let scrut, scrut1, ret, tmp, arg$Unwind$0$;
      scrut = contTrace.resumed;
      if (scrut === true) {
        throw runtime.safeCall(globalThis.Error("Multiple resumption"))
      } else {
        tmp = runtime.Unit;
      }
      contTrace.resumed = true;
      scrut1 = Runtime.resumeContTrace(contTrace, value);
      if (scrut1 instanceof Runtime.NewEffect.class) {
        return Runtime.handleEffects()
      } else if (scrut1 instanceof Runtime.Unwind.class) {
        arg$Unwind$0$ = scrut1.ret;
        ret = arg$Unwind$0$;
        return ret
      } else {
        throw globalThis.Object.freeze(new globalThis.Error("match error"))
      }
    }
  } 
  static resumeContTrace(contTrace, value) {
    let savedDepth, curDepth, stack, tmp;
    savedDepth = Runtime.stackDepth;
    curDepth = Runtime.stackDepth + 30;
    stack = contTrace.funStack;
    lbl: while (true) {
      let scrut, segment, tmp1;
      scrut = stack !== null;
      if (scrut === true) {
        segment = stack.segHead;
        lbl1: while (true) {
          let scrut1, buf, off, tmp2;
          scrut1 = segment !== null;
          if (scrut1 === true) {
            buf = segment.buf;
            off = segment.off;
            lbl2: while (true) {
              let scrut2, i, f, argListsLength, currentArgList, thisOff, scrut3, argListLength, scrut4, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
              scrut2 = off < buf.length;
              if (scrut2 === true) {
                i = 0;
                f = buf.at(off);
                tmp3 = off + 5;
                argListsLength = buf.at(tmp3);
                currentArgList = off + 6;
                thisOff = off + 4;
                Runtime.resumeValue = value;
                Runtime.resumeArr = buf;
                tmp4 = off + 1;
                Runtime.resumePc = buf.at(tmp4);
                scrut3 = argListsLength === 0;
                if (scrut3 === true) {
                  throw globalThis.Object.freeze(new globalThis.Error("cannot resume getters"))
                } else {
                  tmp5 = runtime.Unit;
                }
                lbl3: while (true) {
                  let scrut5, argListLength1, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
                  tmp17 = argListsLength - 1;
                  scrut5 = i < tmp17;
                  if (scrut5 === true) {
                    argListLength1 = buf.at(currentArgList);
                    tmp18 = currentArgList + 1;
                    tmp19 = currentArgList + 1;
                    tmp20 = tmp19 + argListLength1;
                    tmp21 = buf.slice(tmp18, tmp20);
                    tmp22 = f.apply(buf.at(thisOff), tmp21);
                    f = tmp22;
                    tmp23 = argListLength1 + 1;
                    tmp24 = currentArgList + tmp23;
                    currentArgList = tmp24;
                    tmp25 = i + 1;
                    i = tmp25;
                    tmp6 = runtime.Unit;
                    continue lbl3
                  } else {
                    tmp6 = runtime.Unit;
                  }
                  break;
                }
                argListLength = buf.at(currentArgList);
                tmp7 = currentArgList + argListLength;
                tmp8 = tmp7 + 2;
                Runtime.resumeIdx = tmp8;
                tmp9 = Runtime.resumeIdx - 1;
                tmp10 = Runtime.resumeIdx + buf.at(tmp9);
                off = tmp10;
                Runtime.stackDepth = curDepth;
                tmp11 = currentArgList + 1;
                tmp12 = currentArgList + 1;
                tmp13 = tmp12 + argListLength;
                tmp14 = buf.slice(tmp11, tmp13);
                tmp15 = f.apply(buf.at(thisOff), tmp14);
                value = tmp15;
                Runtime.stackDepth = savedDepth;
                scrut4 = Runtime.curEffect !== null;
                if (scrut4 === true) {
                  segment.off = off;
                  Runtime.curEffect.contTrace.lastStack.segLast.nextSegment = segment;
                  Runtime.curEffect.contTrace.lastStack.segLast = stack.segLast;
                  Runtime.curEffect.contTrace.lastStack.handler = stack.handler;
                  Runtime.curEffect.contTrace.lastStack.nextStack = stack.nextStack;
                  Runtime.curEffect.contTrace.lastStack = contTrace.lastStack;
                  Runtime.curEffect.lastSegmentBuf = contTrace.lastStack.segLast.buf;
                  return Runtime.NewEffect
                } else {
                  tmp16 = runtime.Unit;
                }
                tmp2 = tmp16;
                continue lbl2
              } else {
                tmp2 = runtime.Unit;
              }
              break;
            }
            segment = segment.nextSegment;
            tmp1 = runtime.Unit;
            continue lbl1
          } else {
            tmp1 = runtime.Unit;
          }
          break;
        }
        stack = stack.nextStack;
        tmp = runtime.Unit;
        continue lbl
      } else {
        tmp = runtime.Unit;
      }
      break;
    }
    return Runtime.Unwind(value)
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
    let result, scrut, tmp, tmp1;
    Runtime.stackLimit = limit;
    Runtime.stackDepth = 1;
    Runtime.stackHandler = Runtime.StackDelayHandler;
    result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
    scrut = Runtime.curEffect !== null;
    if (scrut === true) {
      throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
    } else {
      tmp = runtime.Unit;
    }
    lbl: while (true) {
      let scrut1, saved, scrut2, tmp2, tmp3;
      scrut1 = Runtime.stackResume !== null;
      if (scrut1 === true) {
        saved = Runtime.stackResume;
        Runtime.stackResume = null;
        Runtime.stackDepth = 1;
        tmp2 = runtime.safeCall(saved(runtime.Unit));
        result = tmp2;
        scrut2 = Runtime.curEffect !== null;
        if (scrut2 === true) {
          throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
        } else {
          tmp3 = runtime.Unit;
        }
        tmp1 = tmp3;
        continue lbl
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
