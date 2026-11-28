const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let continuation, Runtime1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda$, lambda$1, Capture$scope351, lambda$2, Capture$scope371, lambda$3, lambda$4, continuation$;
continuation$ = function continuation$(Runtime2, resume) {
  return (value) => {
    return continuation(Runtime2, resume, value)
  }
};
continuation = function continuation(Runtime2, resume, value) {
  let r, scrut, tmp;
  r = runtime.safeCall(resume(value));
  tmp = Runtime2.curEffect;
  scrut = tmp !== null;
  if (scrut === true) {
    Runtime2.illegalEffect("in exported async function");
    return r
  }
  return r;
};
lambda$4 = (undefined, function (Runtime2, promise) {
  return (resume) => {
    let continuation$here;
    continuation$here = continuation$(Runtime2, resume);
    return runtime.safeCall(promise.then(continuation$here))
  }
});
lambda3 = (undefined, function (Runtime2, promise, resume) {
  let continuation$here;
  continuation$here = continuation$(Runtime2, resume);
  return runtime.safeCall(promise.then(continuation$here))
});
(class Capture$scope37 {
  static {
    Capture$scope371 = this
  }
  constructor(result$0) {
    this.result$0 = result$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope37"];
});
lambda$3 = (undefined, function (scope37$cap, cont) {
  return (m, marker, ..._) => {
    return lambda2(scope37$cap, cont, m, marker, ..._)
  }
});
lambda2 = (undefined, function (scope37$cap, cont, m, marker, ..._) {
  let scrut, tmp, tmp1, tmp2;
  scrut = runtime.safeCall(m.has(cont));
  if (scrut === true) {
    tmp = scope37$cap.result$0;
    tmp1 = ", " + marker;
    tmp2 = tmp + tmp1;
    scope37$cap.result$0 = tmp2;
    return runtime.Unit
  }
  return runtime.Unit;
});
(class Capture$scope35 {
  static {
    Capture$scope351 = this
  }
  constructor(result$0) {
    this.result$0 = result$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope35"];
});
lambda$2 = (undefined, function (scope35$cap, cont) {
  return (m, marker, ..._) => {
    return lambda1(scope35$cap, cont, m, marker, ..._)
  }
});
lambda1 = (undefined, function (scope35$cap, cont, m, marker, ..._) {
  let scrut, tmp, tmp1, tmp2;
  scrut = runtime.safeCall(m.has(cont));
  if (scrut === true) {
    tmp = scope35$cap.result$0;
    tmp1 = ", " + marker;
    tmp2 = tmp + tmp1;
    scope35$cap.result$0 = tmp2;
    return runtime.Unit
  }
  return runtime.Unit;
});
lambda = (undefined, function (l, ..._) {
  let tmp, tmp1;
  tmp = l.localName + "=";
  tmp1 = runtime.safeCall(Rendering.render(l.value));
  return tmp + tmp1
});
lambda$1 = (undefined, function (Runtime2) {
  return (k) => {
    Runtime2.stackResume = k;
    return runtime.Unit
  }
});
lambda5 = (undefined, function (Runtime2, k) {
  Runtime2.stackResume = k;
  return runtime.Unit
});
lambda$ = (undefined, function (Runtime2, EffectHandle1, value) {
  return () => {
    return Runtime2.resume(EffectHandle1.reified.contTrace)(value)
  }
});
lambda4 = (undefined, function (Runtime2, EffectHandle1, value) {
  return Runtime2.resume(EffectHandle1.reified.contTrace)(value)
});
(class Runtime {
  static {
    Runtime1 = this
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
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
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
    (class Continue {
      static {
        new this
      }
      constructor() {
        Runtime.Continue = this;
        Object.defineProperty(this, "class", {
          value: Continue
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Continue"];
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
    tmp = RuntimeJS.short_and;
    Runtime.short_and = tmp;
    tmp1 = RuntimeJS.short_or;
    Runtime.short_or = tmp1;
    tmp2 = RuntimeJS.bitand;
    Runtime.bitand = tmp2;
    tmp3 = RuntimeJS.bitnot;
    Runtime.bitnot = tmp3;
    tmp4 = RuntimeJS.bitor;
    Runtime.bitor = tmp4;
    tmp5 = RuntimeJS.shl;
    Runtime.shl = tmp5;
    tmp6 = RuntimeJS.try_catch;
    Runtime.try_catch = tmp6;
    Runtime.EffectHandle = function EffectHandle(_reified) {
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
        let lambda$here;
        lambda$here = lambda$(Runtime, this, value);
        return Runtime._try(lambda$here)
      }
      raise() {
        Runtime.curEffect = this.reified;
        return runtime.Unit
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectHandle", [null]];
    });
    Runtime.MatchSuccess = function MatchSuccess(output, bindings) {
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
    Runtime.MatchFailure = function MatchFailure(errors) {
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
      static {
        let tmp8;
        tmp8 = LazyArray.__split;
        Tuple.split = tmp8;
      }
      static slice(xs, i, j) {
        let tmp8, tmp9;
        tmp8 = xs.length;
        tmp9 = tmp8 - j;
        return runtime.safeCall(xs.slice(i, tmp9))
      }
      static sliceArray(xs, i, j) {
        let tmp8, tmp9;
        tmp8 = xs.length;
        tmp9 = tmp8 - j;
        return runtime.safeCall(xs.slice(i, tmp9))
      }
      static lazySlice(xs, i, j) {
        let callPrefix;
        callPrefix = runtime.safeCall(LazyArray.dropLeftRight(i, j));
        return runtime.safeCall(callPrefix(xs))
      }
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      }
      static get(xs, i) {
        let scrut, scrut1, tmp8, tmp9, tmp10;
        tmp8 = xs.length;
        scrut = i >= tmp8;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: index out of bounds"))
        }
        tmp9 = xs.length;
        tmp10 = - tmp9;
        scrut1 = i < tmp10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: negative index out of bounds"))
        }
        return xs.at(i);
      }
      static isArrayLike(xs) {
        return runtime.safeCall(Iter.isArrayLike(xs))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Tuple"];
    });
    (class StrOps {
      static {
        Runtime.StrOps = this
      }
      static startsWith(string, prefix) {
        return runtime.safeCall(string.startsWith(prefix))
      }
      static get(string, i) {
        let scrut, tmp8;
        tmp8 = string.length;
        scrut = i >= tmp8;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Str.get: index out of bounds"))
        }
        return runtime.safeCall(string.at(i));
      }
      static take(string, n) {
        return runtime.safeCall(string.slice(0, n))
      }
      static leaveOut(string, n) {
        return runtime.safeCall(string.slice(n))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "StrOps"];
    });
    tmp7 = Rendering.render;
    Runtime.render = tmp7;
    (class TraceLogger {
      static {
        Runtime.TraceLogger = this
      }
      static #enabled;
      static #indentLvl;
      static get enabled() { return TraceLogger.#enabled; }
      static set enabled(value) { TraceLogger.#enabled = value; }
      static get indentLvl() { return TraceLogger.#indentLvl; }
      static set indentLvl(value) { TraceLogger.#indentLvl = value; }
      static {
        TraceLogger.#enabled = false;
        TraceLogger.#indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp8;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp8 = prev + 1;
          TraceLogger.indentLvl = tmp8;
          return prev
        }
        return runtime.Unit;
      }
      static resetIndent(n) {
        let scrut;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          TraceLogger.indentLvl = n;
          return runtime.Unit
        }
        return runtime.Unit;
      }
      static log(msg) {
        let scrut, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp8 = TraceLogger.indentLvl;
          tmp9 = runtime.safeCall(("| ").repeat(tmp8));
          tmp10 = TraceLogger.indentLvl;
          tmp11 = runtime.safeCall(("  ").repeat(tmp10));
          tmp12 = "\n" + tmp11;
          tmp13 = runtime.safeCall(msg.replaceAll("\n", tmp12));
          tmp14 = tmp9 + tmp13;
          return runtime.safeCall(globalThis.console.log(tmp14))
        }
        return runtime.Unit;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "TraceLogger"];
    });
    Runtime.#curEffect = null;
    Runtime.#resumeValue = null;
    Runtime.#resumeArr = null;
    Runtime.#resumeIdx = null;
    Runtime.#resumePc = -1;
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
    Runtime.FunctionContFrame = function FunctionContFrame(next, saved) {
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
        let i, f, argListsLength, currentArgList, scrut, argListLength, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
        i = 0;
        f = this.saved.at(0);
        argListsLength = this.saved.at(5);
        currentArgList = 6;
        Runtime.resumeValue = value;
        Runtime.resumeArr = this.saved;
        tmp8 = this.saved.at(1);
        Runtime.resumePc = tmp8;
        scrut = argListsLength === 0;
        if (scrut === true) {
          runtime.safeCall(globalThis.console.log("cannot resume getters"));
        }
        lbl: while (true) {
          let scrut1, argListLength1, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
          tmp16 = argListsLength - 1;
          scrut1 = i < tmp16;
          if (scrut1 === true) {
            argListLength1 = this.saved.at(currentArgList);
            tmp17 = this.saved.at(4);
            tmp18 = currentArgList + 1;
            tmp19 = currentArgList + 1;
            tmp20 = tmp19 + argListLength1;
            tmp21 = runtime.safeCall(this.saved.slice(tmp18, tmp20));
            tmp22 = runtime.safeCall(f.apply(tmp17, tmp21));
            f = tmp22;
            tmp23 = argListLength1 + 1;
            tmp24 = currentArgList + tmp23;
            currentArgList = tmp24;
            tmp25 = i + 1;
            i = tmp25;
            continue lbl
          }
          break;
        }
        argListLength = this.saved.at(currentArgList);
        tmp9 = currentArgList + argListLength;
        tmp10 = tmp9 + 2;
        Runtime.resumeIdx = tmp10;
        tmp11 = this.saved.at(4);
        tmp12 = currentArgList + 1;
        tmp13 = currentArgList + 1;
        tmp14 = tmp13 + argListLength;
        tmp15 = runtime.safeCall(this.saved.slice(tmp12, tmp14));
        return runtime.safeCall(f.apply(tmp11, tmp15))
      }
      get getLocals() {
        let debugInfo, i, cur, res, i1;
        debugInfo = this.saved.at(3);
        i = 0;
        cur = 6;
        lbl: while (true) {
          let scrut, tmp8, tmp9, tmp10, tmp11, tmp12;
          tmp8 = this.saved.at(5);
          scrut = i < tmp8;
          if (scrut === true) {
            tmp9 = this.saved.at(cur);
            tmp10 = tmp9 + 1;
            tmp11 = cur + tmp10;
            cur = tmp11;
            tmp12 = i + 1;
            i = tmp12;
            continue lbl
          }
          break;
        }
        res = [];
        i1 = 1;
        lbl1: while (true) {
          let scrut, tmp8, tmp9, tmp10, arg, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
          tmp8 = debugInfo.length;
          scrut = i1 < tmp8;
          if (scrut === true) {
            tmp9 = i1 + 1;
            tmp10 = debugInfo.at(tmp9);
            arg = tmp10;
            tmp11 = cur + 1;
            tmp12 = debugInfo.at(i1);
            tmp13 = tmp11 + tmp12;
            tmp14 = this.saved.at(tmp13);
            tmp15 = globalThis.Object.freeze(new Runtime.LocalVarInfo.class(arg, tmp14));
            runtime.safeCall(res.push(tmp15));
            tmp16 = i1 + 2;
            i1 = tmp16;
            continue lbl1
          }
          break;
        }
        return res;
      }
      get getNme() {
        let tmp8;
        tmp8 = this.saved.at(3);
        return tmp8.at(0);
      }
      get getLoc() {
        let loc, tmp8;
        loc = this.saved.at(2);
        if (loc === null) {
          tmp8 = this.saved.at(1);
          return "pc=" + tmp8
        }
        return loc;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunctionContFrame", ["next", "saved"]];
    });
    Runtime.HandlerContFrame = function HandlerContFrame(next, nextHandler, handler) {
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
    Runtime.ContTrace = function ContTrace(next, last, nextHandler, lastHandler, resumed) {
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
    Runtime.EffectSig = function EffectSig(contTrace, handler, handlerFun) {
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
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "NonLocalReturn"];
    });
    Runtime.FnLocalsInfo = function FnLocalsInfo(fnName, locals) {
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
    Runtime.LocalVarInfo = function LocalVarInfo(localName, value) {
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
    Runtime.CustomStackError = function CustomStackError(stack) {
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
    (class AsyncEffectMarker {
      static {
        new this
      }
      constructor() {
        Runtime.AsyncEffectMarker = this;
        Object.defineProperty(this, "class", {
          value: AsyncEffectMarker
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "AsyncEffectMarker"];
    });
    Runtime.#stackLimit = 0;
    Runtime.#stackDepth = 0;
    Runtime.#stackHandler = null;
    Runtime.#stackResume = null;
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
        let lambda$here;
        lambda$here = lambda$1(Runtime);
        return Runtime.mkEffect(this, lambda$here)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "StackDelayHandler"];
    });
    Runtime.Int31 = function Int31(v) {
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
        let tmp8, tmp9;
        tmp8 = runtime.safeCall(Runtime.shl(1, 31));
        tmp9 = runtime.safeCall(Runtime.bitnot(tmp8));
        return runtime.safeCall(Runtime.bitand(this.#v, tmp9))
      }
      sext() {
        let tmp8;
        tmp8 = runtime.safeCall(Runtime.shl(1, 31));
        return runtime.safeCall(Runtime.bitor(this.#v, tmp8))
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
  static checkArgs(functionName, expected, got) {
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
    scrut = got < expected;
    if (scrut === true) {
      tmp = functionName.length;
      scrut1 = tmp > 0;
      if (scrut1 === true) {
        tmp1 = " '" + functionName;
        tmp2 = tmp1 + "'";
      } else {
        tmp2 = "";
      }
      tmp3 = "Function" + tmp2;
      tmp4 = tmp3 + " expected at least ";
      tmp5 = tmp4 + expected;
      tmp6 = tmp5 + " argument";
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp7 = "";
      } else {
        tmp7 = "s";
      }
      tmp8 = tmp6 + tmp7;
      tmp9 = tmp8 + " but got ";
      tmp10 = tmp9 + got;
      throw runtime.safeCall(globalThis.Error(tmp10))
    }
    return runtime.Unit;
  }
  static checkVariadicArgs(functionName, expected, leading, args) {
    let tmp, tmp1;
    tmp = args.length;
    tmp1 = leading + tmp;
    return Runtime.checkArgs(functionName, expected, tmp1)
  }
  static checkSelect(sel, nme, qual) {
    let scrut, tmp, tmp1, tmp2;
    scrut = sel === undefined;
    if (scrut === true) {
      tmp = "Access to required field '" + nme;
      tmp1 = tmp + "' yielded 'undefined'";
      throw runtime.safeCall(globalThis.Error(tmp1))
    }
    tmp2 = nme + "$__checkNotMethod";
    qual[tmp2];
    return sel;
  }
  static safeCall(x) {
    if (x === undefined) {
      return runtime.Unit
    }
    return x;
  }
  static checkCall(x) {
    if (x === undefined) {
      throw runtime.safeCall(globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value."))
    }
    return x;
  }
  static deboundMethod(mtdName, clsName) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = "[debinding error] Method '" + mtdName;
    tmp1 = tmp + "' of class '";
    tmp2 = tmp1 + clsName;
    tmp3 = tmp2 + "' was accessed without being called.";
    throw runtime.safeCall(globalThis.Error(tmp3))
  }
  static _try(f) {
    let res, scrut, tmp, tmp1;
    res = runtime.safeCall(f());
    tmp1 = Runtime.curEffect;
    scrut = tmp1 !== null;
    if (scrut === true) {
      tmp = Runtime.curEffect;
      Runtime.curEffect = null;
      return Runtime.EffectHandle(tmp)
    }
    return res;
  }
  static printRaw(x) {
    let rcd, tmp;
    rcd = globalThis.Object.freeze({
      indent: 2,
      breakLength: 76
    });
    tmp = runtime.safeCall(Runtime.render(x, rcd));
    return runtime.safeCall(globalThis.console.log(tmp))
  }
  static resetEffects() {
    Runtime.curEffect = null;
    Runtime.resumePc = -1;
    return runtime.Unit
  }
  static raisePrintStackEffect(showLocals) {
    return Runtime.mkEffect(Runtime.PrintStackEffect, showLocals)
  }
  static topLevelEffect(debug) {
    let tr, v, tmp, tmp1, tmp2, tmp3;
    tr = Runtime.curEffect;
    v = null;
    lbl: while (true) {
      let scrut, tmp4, tmp5, tmp6;
      if (tr instanceof Runtime.EffectSig.class) {
        scrut = tr.handler === Runtime.PrintStackEffect;
        if (scrut === true) {
          tmp4 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
          runtime.safeCall(globalThis.console.log(tmp4));
          Runtime.curEffect = null;
          tmp5 = Runtime.resume(tr.contTrace)(runtime.Unit);
          v = tmp5;
          tmp6 = Runtime.curEffect;
          tr = tmp6;
          continue lbl
        }
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      Runtime.curEffect = null;
      tmp = tr.handler["constructor"];
      tmp1 = tmp["name"];
      tmp2 = "Error: Unhandled effect " + tmp1;
      tmp3 = Runtime.showStackTrace(tmp2, tr, debug, false);
      throw Runtime.CustomStackError(tmp3)
    }
    return v;
  }
  static illegalEffect(position) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Runtime.curEffect;
    Runtime.curEffect = null;
    tmp1 = tmp.handler["constructor"];
    tmp2 = tmp1["name"];
    tmp3 = "Error: Effect " + tmp2;
    tmp4 = tmp3 + " is raised ";
    tmp5 = tmp4 + position;
    tmp6 = Runtime.showStackTrace(tmp5, tmp, false, false);
    throw Runtime.CustomStackError(tmp6)
  }
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      lbl: while (true) {
        let scrut, cur, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          lbl1: while (true) {
            let scrut2, curLocals, loc, scrut3, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
            scrut2 = cur !== null;
            if (scrut2 === true) {
              curLocals = cur.getLocals;
              loc = cur.getLoc;
              if (showLocals === true) {
                tmp5 = curLocals.length;
                scrut3 = tmp5 > 0;
                if (scrut3 === true) {
                  tmp6 = runtime.safeCall(curLocals.map(lambda));
                  tmp7 = runtime.safeCall(tmp6.join(", "));
                  tmp8 = " with locals: " + tmp7;
                } else {
                  tmp8 = "";
                }
              } else {
                tmp8 = "";
              }
              tmp9 = cur.getNme;
              tmp10 = "\n\tat " + tmp9;
              tmp11 = tmp10 + " (";
              tmp12 = tmp11 + loc;
              tmp13 = tmp12 + ")";
              tmp14 = msg + tmp13;
              tmp15 = tmp14 + tmp8;
              msg = tmp15;
              tmp16 = cur.next;
              cur = tmp16;
              atTail = false;
              continue lbl1
            }
            break;
          }
          tmp = curHandler.nextHandler;
          curHandler = tmp;
          scrut1 = tmp !== null;
          if (scrut1 === true) {
            tmp1 = tmp.handler["constructor"];
            tmp2 = tmp1["name"];
            tmp3 = "\n\twith handler " + tmp2;
            tmp4 = msg + tmp3;
            msg = tmp4;
            atTail = false;
            continue lbl
          }
          continue lbl;
        }
        break;
      }
      if (atTail === true) {
        return msg + "\n\tat tail position"
      }
      return msg;
    }
    return header;
  }
  static showFunctionContChain(cont, hl, vis, reps) {
    let reps1, frame, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, scope35$cap, lambda$here;
    scope35$cap = new Capture$scope351(undefined);
    reps1 = reps;
    if (cont instanceof Runtime.FunctionContFrame.class) {
      frame = cont;
      tmp = frame["constructor"];
      tmp1 = tmp["name"];
      tmp2 = tmp1 + "(pc=";
      tmp3 = frame.saved.at(1);
      scope35$cap.result$0 = tmp2 + tmp3;
      lambda$here = lambda$2(scope35$cap, cont);
      runtime.safeCall(hl.forEach(lambda$here));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp4 = reps + 1;
        reps1 = tmp4;
        scrut1 = tmp4 > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp5 = scope35$cap.result$0;
        tmp6 = tmp5 + ", REPEAT";
        scope35$cap.result$0 = tmp6;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp7 = scope35$cap.result$0;
      tmp8 = tmp7 + ") -> ";
      tmp9 = frame.next;
      tmp10 = Runtime.showFunctionContChain(tmp9, hl, vis, reps1);
      return tmp8 + tmp10
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT CONT)";
  }
  static showHandlerContChain(cont, hl, vis, reps) {
    let reps1, frame, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, scope37$cap, lambda$here;
    scope37$cap = new Capture$scope371(undefined);
    reps1 = reps;
    if (cont instanceof Runtime.HandlerContFrame.class) {
      frame = cont;
      tmp = frame.handler["constructor"];
      scope37$cap.result$0 = tmp["name"];
      lambda$here = lambda$3(scope37$cap, cont);
      runtime.safeCall(hl.forEach(lambda$here));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp1 = reps + 1;
        reps1 = tmp1;
        scrut1 = tmp1 > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp2 = scope37$cap.result$0;
        tmp3 = tmp2 + ", REPEAT";
        scope37$cap.result$0 = tmp3;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp4 = scope37$cap.result$0;
      tmp5 = tmp4 + " -> ";
      tmp6 = frame.next;
      tmp7 = Runtime.showFunctionContChain(tmp6, hl, vis, reps1);
      return tmp5 + tmp7
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT HANDLER CONT)";
  }
  static debugCont(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map(undefined));
    tmp1 = globalThis.Object.freeze(new globalThis.Set(undefined));
    tmp2 = Runtime.showFunctionContChain(cont, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  }
  static debugHandler(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map(undefined));
    tmp1 = globalThis.Object.freeze(new globalThis.Set(undefined));
    tmp2 = Runtime.showHandlerContChain(cont, tmp, tmp1, 0);
    return runtime.safeCall(globalThis.console.log(tmp2))
  }
  static debugContTrace(contTrace) {
    let contTrace1, scrut, scrut1, vis, hl, cur, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
    if (contTrace instanceof Runtime.ContTrace.class) {
      contTrace1 = contTrace;
      tmp = contTrace1.resumed;
      runtime.safeCall(globalThis.console.log("resumed: ", tmp));
      tmp1 = contTrace1.last;
      scrut = tmp1 === contTrace1;
      if (scrut === true) {
        runtime.safeCall(globalThis.console.log("<last is self>"));
      }
      tmp2 = contTrace1.lastHandler;
      scrut1 = tmp2 === contTrace1;
      if (scrut1 === true) {
        runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      }
      vis = globalThis.Object.freeze(new globalThis.Set(undefined));
      hl = globalThis.Object.freeze(new globalThis.Map(undefined));
      tmp3 = contTrace1.last;
      tmp4 = globalThis.Object.freeze([
        tmp3
      ]);
      tmp5 = globalThis.Object.freeze(new globalThis.Set(tmp4));
      runtime.safeCall(hl.set("last", tmp5));
      tmp6 = contTrace1.lastHandler;
      tmp7 = globalThis.Object.freeze([
        tmp6
      ]);
      tmp8 = globalThis.Object.freeze(new globalThis.Set(tmp7));
      runtime.safeCall(hl.set("last-handler", tmp8));
      tmp9 = contTrace1.next;
      tmp10 = Runtime.showFunctionContChain(tmp9, hl, vis, 0);
      runtime.safeCall(globalThis.console.log(tmp10));
      cur = contTrace1.nextHandler;
      lbl: while (true) {
        let scrut2, tmp11, tmp12;
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp11 = Runtime.showHandlerContChain(cur, hl, vis, 0);
          runtime.safeCall(globalThis.console.log(tmp11));
          tmp12 = cur.nextHandler;
          cur = tmp12;
          continue lbl
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    }
    runtime.safeCall(globalThis.console.log("Not a cont trace:"));
    return runtime.safeCall(globalThis.console.log(contTrace));
  }
  static debugEff(eff) {
    let eff1, tmp, tmp1;
    if (eff instanceof Runtime.EffectSig.class) {
      eff1 = eff;
      runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      tmp = eff1.handler["constructor"];
      tmp1 = tmp["name"];
      runtime.safeCall(globalThis.console.log("handler: ", tmp1));
      runtime.safeCall(globalThis.console.log("handlerFun: ", eff1.handlerFun));
      return Runtime.debugContTrace(eff1.contTrace)
    }
    runtime.safeCall(globalThis.console.log("Not an effect:"));
    return runtime.safeCall(globalThis.console.log(eff));
  }
  static unwind(...saved) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Runtime.curEffect;
    tmp1 = tmp.contTrace.last;
    tmp2 = new Runtime.FunctionContFrame.class(null, saved);
    tmp1.next = tmp2;
    tmp3 = Runtime.curEffect;
    tmp4 = Runtime.curEffect;
    tmp5 = tmp4.contTrace.last;
    tmp6 = tmp5.next;
    tmp3.contTrace.last = tmp6;
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
    let handlerFrame, tmp;
    handlerFrame = new Runtime.HandlerContFrame.class(null, null, handler);
    tmp = cur.contTrace.lastHandler;
    tmp.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  }
  static enterHandleBlock(handler, body) {
    let tmp, scrut, tmp1, tmp2;
    tmp = runtime.safeCall(body());
    tmp1 = Runtime.curEffect;
    scrut = tmp1 === null;
    if (scrut === true) {
      return tmp
    }
    tmp2 = Runtime.curEffect;
    return Runtime.handleBlockImpl(tmp2, handler);
  }
  static handleEffects(cur) {
    let cur1;
    cur1 = cur;
    lbl: while (true) {
      let effect, nxt, scrut;
      if (cur1 instanceof Runtime.EffectSig.class) {
        effect = cur1;
        nxt = Runtime.handleEffect(effect);
        scrut = cur1 === nxt;
        if (scrut === true) {
          Runtime.curEffect = cur1;
          return null
        }
        cur1 = nxt;
        continue lbl;
      }
      return cur1;
    }
  }
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, handlerFrame, saved, scrut1, scrut2, old, scrut3, scrut4, scrut5, scrut6, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
    prevHandlerFrame = cur.contTrace;
    lbl: while (true) {
      let scrut7, scrut8, tmp23, tmp24, tmp25;
      tmp23 = prevHandlerFrame.nextHandler;
      scrut7 = tmp23 !== null;
      if (scrut7 === true) {
        tmp24 = prevHandlerFrame.nextHandler;
        scrut8 = tmp24.handler !== cur.handler;
        if (scrut8 === true) {
          tmp25 = prevHandlerFrame.nextHandler;
          prevHandlerFrame = tmp25;
          continue lbl
        }
      }
      break;
    }
    tmp = prevHandlerFrame.nextHandler;
    scrut = tmp === null;
    if (scrut === true) {
      return cur
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    tmp1 = handlerFrame.next;
    tmp2 = cur.contTrace.last;
    tmp3 = handlerFrame.nextHandler;
    tmp4 = cur.contTrace.lastHandler;
    saved = new Runtime.ContTrace.class(tmp1, tmp2, tmp3, tmp4, false);
    tmp5 = cur.contTrace.last;
    scrut1 = tmp5 === handlerFrame;
    if (scrut1 === true) {
      saved.last = saved;
    }
    tmp6 = cur.contTrace.lastHandler;
    scrut2 = tmp6 === handlerFrame;
    if (scrut2 === true) {
      saved.lastHandler = saved;
    }
    cur.contTrace.last = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    Runtime.curEffect = null;
    old = Runtime.stackDepth;
    try {
      tmp8 = Runtime.stackDepth;
      tmp9 = tmp8 + 2;
      Runtime.stackDepth = tmp9;
      tmp10 = Runtime.resume(cur.contTrace);
      tmp11 = runtime.safeCall(cur.handlerFun(tmp10));
      tmp7 = tmp11;
    } finally {
      Runtime.stackDepth = old;
    }
    tmp12 = Runtime.curEffect;
    scrut3 = tmp12 !== null;
    if (scrut3 === true) {
      tmp13 = Runtime.curEffect;
      tmp14 = saved.next;
      scrut4 = tmp14 !== null;
      if (scrut4 === true) {
        tmp15 = tmp13.contTrace.last;
        tmp16 = saved.next;
        tmp15.next = tmp16;
      }
      tmp17 = saved.last;
      scrut5 = tmp17 !== saved;
      if (scrut5 === true) {
        tmp18 = saved.last;
        tmp13.contTrace.last = tmp18;
      }
      tmp19 = saved.nextHandler;
      scrut6 = tmp19 !== null;
      if (scrut6 === true) {
        tmp20 = tmp13.contTrace.lastHandler;
        tmp21 = saved.nextHandler;
        tmp20.nextHandler = tmp21;
        tmp22 = saved.lastHandler;
        tmp13.contTrace.lastHandler = tmp22;
        return tmp13
      }
      return tmp13;
    }
    return Runtime.resumeContTrace(saved, tmp7);
  }
  static resume(contTrace) {
    return (value) => {
      let scrut, tmp;
      scrut = contTrace.resumed;
      if (scrut === true) {
        throw runtime.safeCall(globalThis.Error("Multiple resumption"))
      }
      contTrace.resumed = true;
      tmp = Runtime.resumeContTrace(contTrace, value);
      return Runtime.handleEffects(tmp);
    }
  }
  static resumeContTrace(contTrace, value) {
    let value1, cont, handlerCont;
    value1 = value;
    cont = contTrace.next;
    handlerCont = contTrace.nextHandler;
    lbl: while (true) {
      let old, scrut, effect, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
      if (cont instanceof Runtime.FunctionContFrame.class) {
        Runtime.curEffect = null;
        old = Runtime.stackDepth;
        try {
          tmp1 = Runtime.stackDepth;
          tmp2 = tmp1 + 3;
          Runtime.stackDepth = tmp2;
          tmp3 = cont.resume(value1);
          tmp = tmp3;
        } finally {
          Runtime.stackDepth = old;
        }
        value1 = tmp;
        tmp4 = Runtime.curEffect;
        scrut = tmp4 !== null;
        if (scrut === true) {
          tmp5 = Runtime.curEffect;
          value1 = tmp5;
        }
        if (value1 instanceof Runtime.EffectSig.class) {
          effect = value1;
          tmp6 = effect.contTrace.last;
          tmp7 = cont.next;
          tmp6.next = tmp7;
          tmp8 = effect.contTrace.lastHandler;
          tmp8.nextHandler = handlerCont;
          tmp9 = contTrace.last;
          scrut1 = tmp9 !== cont;
          if (scrut1 === true) {
            tmp10 = contTrace.last;
            effect.contTrace.last = tmp10;
          }
          scrut2 = handlerCont !== null;
          if (scrut2 === true) {
            tmp11 = contTrace.lastHandler;
            effect.contTrace.lastHandler = tmp11;
            return value1
          }
          return value1;
        }
        tmp12 = cont.next;
        cont = tmp12;
        continue lbl;
      }
      if (handlerCont instanceof Runtime.HandlerContFrame.class) {
        tmp13 = handlerCont.next;
        cont = tmp13;
        tmp14 = handlerCont.nextHandler;
        handlerCont = tmp14;
        continue lbl
      }
      return value1;
    }
  }
  static await(promise) {
    let lambda$here;
    lambda$here = lambda$4(Runtime, promise);
    return Runtime.mkEffect(Runtime.AsyncEffectMarker, lambda$here)
  }
  static toJsAsync(thunk) {
    let r, scrut, tmp;
    r = Runtime.enterHandleBlock(Runtime.AsyncEffectMarker, thunk);
    tmp = Runtime.curEffect;
    scrut = tmp !== null;
    if (scrut === true) {
      Runtime.illegalEffect("in exported async function");
      return runtime.safeCall(globalThis.Promise.resolve(r))
    }
    return runtime.safeCall(globalThis.Promise.resolve(r));
  }
  static checkDepth() {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = Runtime.stackDepth;
    tmp1 = Runtime.stackLimit;
    tmp2 = tmp >= tmp1;
    if (tmp2 === true) {
      tmp4 = Runtime.stackHandler;
      tmp3 = tmp4 !== null;
      if (tmp3 === true) {
        tmp5 = Runtime.stackHandler;
        return tmp5.delay()
      }
      return runtime.Unit;
    }
    return runtime.Unit;
  }
  static runStackSafe(limit, f) {
    let old, old1, old2, result, scrut, tmp, tmp1, tmp2, tmp3;
    old = Runtime.stackLimit;
    try {
      Runtime.stackLimit = limit;
      old1 = Runtime.stackDepth;
      try {
        Runtime.stackDepth = 1;
        old2 = Runtime.stackHandler;
        try {
          Runtime.stackHandler = Runtime.StackDelayHandler;
          result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
          tmp3 = Runtime.curEffect;
          scrut = tmp3 !== null;
          if (scrut === true) {
            throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary", undefined))
          }
          lbl: while (true) {
            let scrut1, saved, scrut2, tmp4, tmp5, tmp6;
            tmp4 = Runtime.stackResume;
            scrut1 = tmp4 !== null;
            if (scrut1 === true) {
              saved = Runtime.stackResume;
              Runtime.stackResume = null;
              Runtime.stackDepth = 1;
              tmp5 = runtime.safeCall(saved(runtime.Unit));
              result = tmp5;
              tmp6 = Runtime.curEffect;
              scrut2 = tmp6 !== null;
              if (scrut2 === true) {
                throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary", undefined))
              }
              continue lbl;
            }
            break;
          }
          tmp2 = result;
        } finally {
          Runtime.stackHandler = old2;
        }
        tmp1 = tmp2;
      } finally {
        Runtime.stackDepth = old1;
      }
      tmp = tmp1;
    } finally {
      Runtime.stackLimit = old;
    }
    return tmp
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Runtime"];
});
export { continuation as _$_modulePrivate_$_continuation };
export { Runtime1 as _$_modulePrivate_$_Runtime };
export { lambda as _$_modulePrivate_$_lambda };
export { lambda1 as _$_modulePrivate_$_lambda1 };
export { lambda2 as _$_modulePrivate_$_lambda2 };
export { lambda3 as _$_modulePrivate_$_lambda3 };
export { lambda4 as _$_modulePrivate_$_lambda4 };
export { lambda5 as _$_modulePrivate_$_lambda5 };
export { lambda$ as _$_modulePrivate_$_lambda$ };
export { lambda$1 as _$_modulePrivate_$_lambda$1 };
export { Capture$scope351 as _$_modulePrivate_$_Capture$scope35 };
export { lambda$2 as _$_modulePrivate_$_lambda$2 };
export { Capture$scope371 as _$_modulePrivate_$_Capture$scope37 };
export { lambda$3 as _$_modulePrivate_$_lambda$3 };
export { lambda$4 as _$_modulePrivate_$_lambda$4 };
export { continuation$ as _$_modulePrivate_$_continuation$ };
export default Runtime1;
