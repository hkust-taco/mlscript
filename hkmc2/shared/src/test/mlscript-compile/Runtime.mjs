const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let continuation, Runtime1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda$, Capture$scope271, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, Capture$scope701, lambda$8, Capture$scope721, lambda$9, lambda$10, continuation$;
continuation$ = function continuation$(Runtime2, resume) {
  return (value) => {
    return continuation(Runtime2, resume, value)
  }
};
continuation = function continuation(Runtime2, resume, value) {
  let r, scrut;
  r = runtime.safeCall(resume(value));
  scrut = Runtime2.curEffect !== null;
  if (scrut === true) {
    Runtime2.illegalEffect("in exported async function");
    return r
  }
  return r;
};
lambda$10 = (undefined, function (Runtime2, promise) {
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
(class Capture$scope72 {
  static {
    Capture$scope721 = this
  }
  constructor(result$0) {
    this.result$0 = result$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope72"];
});
lambda$9 = (undefined, function (scope72$cap, cont) {
  return (m, marker, ..._) => {
    return lambda2(scope72$cap, cont, m, marker, ..._)
  }
});
lambda2 = (undefined, function (scope72$cap, cont, m, marker, ..._) {
  let scrut, tmp, tmp1;
  scrut = runtime.safeCall(m.has(cont));
  if (scrut === true) {
    tmp = ", " + marker;
    tmp1 = scope72$cap.result$0 + tmp;
    scope72$cap.result$0 = tmp1;
    return runtime.Unit
  }
  return runtime.Unit;
});
(class Capture$scope70 {
  static {
    Capture$scope701 = this
  }
  constructor(result$0) {
    this.result$0 = result$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope70"];
});
lambda$8 = (undefined, function (scope70$cap, cont) {
  return (m, marker, ..._) => {
    return lambda1(scope70$cap, cont, m, marker, ..._)
  }
});
lambda1 = (undefined, function (scope70$cap, cont, m, marker, ..._) {
  let scrut, tmp, tmp1;
  scrut = runtime.safeCall(m.has(cont));
  if (scrut === true) {
    tmp = ", " + marker;
    tmp1 = scope70$cap.result$0 + tmp;
    scope70$cap.result$0 = tmp1;
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
lambda$7 = (undefined, function (Runtime2) {
  return (k) => {
    Runtime2.stackResume = k;
    return runtime.Unit
  }
});
lambda11 = (undefined, function (Runtime2, k) {
  Runtime2.stackResume = k;
  return runtime.Unit
});
(class Capture$scope27 {
  static {
    Capture$scope271 = this
  }
  constructor(cur$0, pos$1, remStart$2) {
    this.remStart$2 = remStart$2;
    this.pos$1 = pos$1;
    this.cur$0 = cur$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope27"];
});
lambda$6 = (undefined, function (bindings) {
  return (slot, overlay) => {
    return lambda5(bindings, slot, overlay)
  }
});
lambda$5 = (undefined, function (scope27$cap, actions, input, valStack, markStack, bindings, readSlot) {
  return (ops, k, overlay) => {
    return lambda6(scope27$cap, actions, input, valStack, markStack, bindings, readSlot, ops, k, overlay)
  }
});
lambda$4 = (undefined, function (execValueOp) {
  return (ops, overlay) => {
    return lambda7(execValueOp, ops, overlay)
  }
});
lambda$3 = (undefined, function (prog, bindings, execValueOp, runFrameOps, frames) {
  return (opsId) => {
    return lambda8(prog, bindings, execValueOp, runFrameOps, frames, opsId)
  }
});
lambda$2 = (undefined, function (scope27$cap, parentState, parentOps, runOps) {
  return (state) => {
    return lambda9(scope27$cap, parentState, parentOps, runOps, state)
  }
});
lambda$1 = (undefined, function (prog) {
  return (stack, state) => {
    return lambda10(prog, stack, state)
  }
});
lambda5 = (undefined, function (bindings, slot, overlay) {
  let scrut;
  if (overlay === null) {
    return runtime.safeCall(bindings.get(slot))
  }
  scrut = runtime.safeCall(overlay.has(slot));
  if (scrut === true) {
    return runtime.safeCall(overlay.get(slot))
  }
  return runtime.safeCall(bindings.get(slot));
});
lambda6 = (undefined, function (scope27$cap, actions, input, valStack, markStack, bindings, readSlot, ops, k, overlay) {
  let op, b, a, actionId, argCount, args, j, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  op = ops.at(k);
  switch (op) {
    case 0:
      runtime.safeCall(markStack.push(scope27$cap.pos$1));
      return k + 1;
    case 1:
      tmp = runtime.safeCall(markStack.pop());
      tmp1 = runtime.safeCall(input.slice(tmp, scope27$cap.pos$1));
      runtime.safeCall(valStack.push(tmp1));
      return k + 1;
    case 2:
      b = runtime.safeCall(valStack.pop());
      a = runtime.safeCall(valStack.pop());
      tmp2 = a + b;
      runtime.safeCall(valStack.push(tmp2));
      return k + 1;
    case 3:
      runtime.safeCall(valStack.pop());
      return k + 1;
    case 4:
      tmp3 = k + 1;
      tmp4 = valStack.length - 1;
      runtime.safeCall(bindings.set(ops.at(tmp3), valStack.at(tmp4)));
      return k + 2;
    case 5:
      tmp5 = k + 1;
      actionId = ops.at(tmp5);
      tmp6 = k + 2;
      argCount = ops.at(tmp6);
      args = [];
      j = 0;
      lbl: while (true) {
        let scrut, tmp10, tmp11, tmp12, tmp13;
        scrut = j < argCount;
        if (scrut === true) {
          tmp10 = k + 3;
          tmp11 = tmp10 + j;
          tmp12 = runtime.safeCall(readSlot(ops.at(tmp11), overlay));
          runtime.safeCall(args.push(tmp12));
          tmp13 = j + 1;
          j = tmp13;
          continue lbl
        }
        break;
      }
      tmp7 = runtime.safeCall(actions.at(actionId).apply(null, args));
      runtime.safeCall(valStack.push(tmp7));
      tmp8 = k + 3;
      return tmp8 + argCount;
    case 8:
      scope27$cap.remStart$2 = scope27$cap.pos$1;
      return k + 1;
  }
  tmp9 = "StrPat: malformed operation " + op;
  throw runtime.safeCall(globalThis.Error(tmp9))
});
lambda7 = (undefined, function (execValueOp, ops, overlay) {
  let k;
  k = 0;
  lbl: while (true) {
    let scrut, tmp;
    scrut = k < ops.length;
    if (scrut === true) {
      tmp = runtime.safeCall(execValueOp(ops, k, overlay));
      k = tmp;
      continue lbl
    }
    break;
  }
  return runtime.Unit
});
lambda8 = (undefined, function (prog, bindings, execValueOp, runFrameOps, frames, opsId) {
  let ops, k;
  ops = prog.opsPool.at(opsId);
  k = 0;
  lbl: while (true) {
    let scrut, op, frame, deferredOps, capCount, captures, j, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    scrut = k < ops.length;
    if (scrut === true) {
      op = ops.at(k);
      switch (op) {
        case 6:
          runtime.safeCall(frames.push(null));
          tmp = k + 1;
          k = tmp;
          continue lbl;
        case 7:
          frame = runtime.safeCall(frames.pop());
          lbl1: while (true) {
            let scrut1, element1$, element0$, tmp8;
            scrut1 = frame !== null;
            if (scrut1 === true) {
              if (runtime.Tuple.isArrayLike(frame) && frame.length === 2) {
                element0$ = runtime.Tuple.get(frame, 0);
                element1$ = runtime.Tuple.get(frame, 1);
                runtime.safeCall(runFrameOps(prog.opsPool.at(element0$), element1$));
                tmp8 = runtime.safeCall(frames.pop());
                frame = tmp8;
                continue lbl1
              }
              throw runtime.safeCall(globalThis.Error("StrPat: missing recursive frame sentinel (this is a compiler bug)"));
            }
            break;
          }
          tmp1 = k + 1;
          k = tmp1;
          continue lbl;
        case 9:
          tmp2 = k + 1;
          deferredOps = ops.at(tmp2);
          tmp3 = k + 2;
          capCount = ops.at(tmp3);
          captures = globalThis.Object.freeze(new globalThis.Map());
          j = 0;
          lbl2: while (true) {
            let scrut1, slot, tmp8, tmp9, tmp10, tmp11;
            scrut1 = j < capCount;
            if (scrut1 === true) {
              tmp8 = k + 3;
              tmp9 = tmp8 + j;
              slot = ops.at(tmp9);
              tmp10 = runtime.safeCall(bindings.get(slot));
              runtime.safeCall(captures.set(slot, tmp10));
              tmp11 = j + 1;
              j = tmp11;
              continue lbl2
            }
            break;
          }
          tmp4 = globalThis.Object.freeze([
            deferredOps,
            captures
          ]);
          runtime.safeCall(frames.push(tmp4));
          tmp5 = 3 + capCount;
          tmp6 = k + tmp5;
          k = tmp6;
          continue lbl;
      }
      tmp7 = runtime.safeCall(execValueOp(ops, k, null));
      k = tmp7;
      continue lbl
    }
    break;
  }
  return runtime.Unit
});
lambda9 = (undefined, function (scope27$cap, parentState, parentOps, runOps, state) {
  let chain, w, idx;
  chain = [];
  w = state;
  lbl: while (true) {
    let scrut, opsId, scrut1, tmp;
    scrut = w !== scope27$cap.cur$0;
    if (scrut === true) {
      opsId = runtime.safeCall(parentOps.get(w));
      scrut1 = opsId !== -1;
      if (scrut1 === true) {
        runtime.safeCall(chain.push(opsId));
      }
      tmp = runtime.safeCall(parentState.get(w));
      w = tmp;
      continue lbl
    }
    break;
  }
  idx = chain.length - 1;
  lbl1: while (true) {
    let scrut, tmp;
    scrut = idx >= 0;
    if (scrut === true) {
      runtime.safeCall(runOps(chain.at(idx)));
      tmp = idx - 1;
      idx = tmp;
      continue lbl1
    }
    break;
  }
  return runtime.Unit
});
lambda10 = (undefined, function (prog, stack, state) {
  let edges, i;
  edges = prog.states.at(state);
  i = edges.length - 1;
  lbl: while (true) {
    let scrut, tmp, tmp1;
    scrut = i >= 0;
    if (scrut === true) {
      tmp = globalThis.Object.freeze([
        state,
        edges.at(i)
      ]);
      runtime.safeCall(stack.push(tmp));
      tmp1 = i - 1;
      i = tmp1;
      continue lbl
    }
    break;
  }
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
    Runtime.short_and = RuntimeJS.short_and;
    Runtime.short_or = RuntimeJS.short_or;
    Runtime.bitand = RuntimeJS.bitand;
    Runtime.bitnot = RuntimeJS.bitnot;
    Runtime.bitor = RuntimeJS.bitor;
    Runtime.shl = RuntimeJS.shl;
    Runtime.try_catch = RuntimeJS.try_catch;
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
        return Runtime._try(lambda$(Runtime, this, value))
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
        Tuple.split = LazyArray.__split;
      }
      static slice(xs, i, j) {
        let tmp;
        tmp = xs.length - j;
        return runtime.safeCall(xs.slice(i, tmp))
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
        let scrut, scrut1, tmp;
        scrut = i >= xs.length;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: index out of bounds"))
        }
        tmp = - xs.length;
        scrut1 = i < tmp;
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
        let scrut;
        scrut = i >= string.length;
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
    (class StrPat {
      static {
        Runtime.StrPat = this
      }
      static {
        let tmp, tmp1;
        StrPat.Program = function Program(stateCount, start, accept, slotCount, classCount, seedRev, bounds, states, opsPool, revTrans, viability) {
          return globalThis.Object.freeze(new Program.class(stateCount, start, accept, slotCount, classCount, seedRev, bounds, states, opsPool, revTrans, viability));
        };
        (class Program {
          static {
            StrPat.Program.class = this
          }
          constructor(stateCount, start, accept, slotCount, classCount, seedRev, bounds, states, opsPool, revTrans, viability) {
            this.stateCount = stateCount;
            this.start = start;
            this.accept = accept;
            this.slotCount = slotCount;
            this.classCount = classCount;
            this.seedRev = seedRev;
            this.bounds = bounds;
            this.states = states;
            this.opsPool = opsPool;
            this.revTrans = revTrans;
            this.viability = viability;
          }
          toString() { return runtime.render(this); }
          static [definitionMetadata] = ["class", "Program", ["stateCount", "start", "accept", "slotCount", "classCount", "seedRev", "bounds", "states", "opsPool", "revTrans", "viability"]];
        });
        StrPat.Matcher = function Matcher(classCount, seedRev, bounds, revTrans, starts) {
          return globalThis.Object.freeze(new Matcher.class(classCount, seedRev, bounds, revTrans, starts));
        };
        (class Matcher {
          static {
            StrPat.Matcher.class = this
          }
          constructor(classCount, seedRev, bounds, revTrans, starts) {
            this.classCount = classCount;
            this.seedRev = seedRev;
            this.bounds = bounds;
            this.revTrans = revTrans;
            this.starts = starts;
          }
          toString() { return runtime.render(this); }
          static [definitionMetadata] = ["class", "Matcher", ["classCount", "seedRev", "bounds", "revTrans", "starts"]];
        });
        tmp = globalThis.Object.freeze(new globalThis.Map());
        StrPat.programs = tmp;
        tmp1 = globalThis.Object.freeze(new globalThis.Map());
        StrPat.matchers = tmp1;
      }
      static decodeInts(s) {
        let values, value, shift, i;
        values = [];
        value = 0;
        shift = 1;
        i = 0;
        lbl: while (true) {
          let scrut, d, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
          scrut = i < s.length;
          if (scrut === true) {
            tmp = runtime.safeCall(s.charCodeAt(i));
            d = StrPat.sextet(tmp);
            scrut1 = d >= 32;
            if (scrut1 === true) {
              tmp1 = d - 32;
              tmp2 = tmp1 * shift;
              tmp3 = value + tmp2;
              value = tmp3;
              tmp4 = shift * 32;
              shift = tmp4;
            } else {
              tmp5 = d * shift;
              tmp6 = value + tmp5;
              runtime.safeCall(values.push(tmp6));
              value = 0;
              shift = 1;
            }
            tmp7 = i + 1;
            i = tmp7;
            continue lbl
          }
          break;
        }
        return values
      }
      static sextet(code) {
        let scrut, scrut1, scrut2, scrut3;
        scrut = code >= 97;
        if (scrut === true) {
          return code - 71
        }
        scrut1 = code >= 65;
        if (scrut1 === true) {
          return code - 65
        }
        scrut2 = code >= 48;
        if (scrut2 === true) {
          return code + 4
        }
        scrut3 = code === 43;
        if (scrut3 === true) {
          return 62
        }
        return 63;
      }
      static decodeBits(packed) {
        let thresholds, bits, i;
        thresholds = globalThis.Object.freeze([
          32,
          16,
          8,
          4,
          2,
          1
        ]);
        bits = [];
        i = 0;
        lbl: while (true) {
          let scrut, v, j, tmp, tmp1;
          scrut = i < packed.length;
          if (scrut === true) {
            tmp = runtime.safeCall(packed.charCodeAt(i));
            v = StrPat.sextet(tmp);
            j = 0;
            lbl1: while (true) {
              let scrut1, scrut2, tmp2, tmp3;
              scrut1 = j < 6;
              if (scrut1 === true) {
                scrut2 = v >= thresholds.at(j);
                if (scrut2 === true) {
                  runtime.safeCall(bits.push(true));
                  tmp2 = v - thresholds.at(j);
                  v = tmp2;
                } else {
                  runtime.safeCall(bits.push(false));
                }
                tmp3 = j + 1;
                j = tmp3;
                continue lbl1
              }
              break;
            }
            tmp1 = i + 1;
            i = tmp1;
            continue lbl
          }
          break;
        }
        return bits
      }
      static decodeProgram(table) {
        let sections, header, stateCount, nfaInts, cursor, opsInts, opsPool, opsCount, states, tmp, tmp1, tmp2;
        sections = runtime.safeCall(table.split(";"));
        header = StrPat.decodeInts(sections.at(0));
        stateCount = header.at(0);
        nfaInts = StrPat.decodeInts(sections.at(2));
        states = [];
        cursor = 0;
        lbl: while (true) {
          let scrut, edgeCount, edges, tmp3;
          scrut = states.length < stateCount;
          if (scrut === true) {
            edgeCount = nfaInts.at(cursor);
            edges = [];
            tmp3 = cursor + 1;
            cursor = tmp3;
            lbl1: while (true) {
              let scrut1, kind, target, scrut2, rangeCount, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18;
              scrut1 = edges.length < edgeCount;
              if (scrut1 === true) {
                kind = nfaInts.at(cursor);
                tmp4 = cursor + 1;
                target = nfaInts.at(tmp4);
                scrut2 = kind === 0;
                if (scrut2 === true) {
                  tmp5 = cursor + 2;
                  rangeCount = nfaInts.at(tmp5);
                  tmp6 = cursor + 3;
                  tmp7 = cursor + 3;
                  tmp8 = rangeCount * 2;
                  tmp9 = tmp7 + tmp8;
                  tmp10 = runtime.safeCall(nfaInts.slice(tmp6, tmp9));
                  tmp11 = globalThis.Object.freeze([
                    0,
                    target,
                    tmp10
                  ]);
                  runtime.safeCall(edges.push(tmp11));
                  tmp12 = rangeCount * 2;
                  tmp13 = 3 + tmp12;
                  tmp14 = cursor + tmp13;
                  cursor = tmp14;
                  continue lbl1
                }
                tmp15 = cursor + 2;
                tmp16 = nfaInts.at(tmp15) - 1;
                tmp17 = globalThis.Object.freeze([
                  1,
                  target,
                  tmp16
                ]);
                runtime.safeCall(edges.push(tmp17));
                tmp18 = cursor + 3;
                cursor = tmp18;
                continue lbl1;
              }
              break;
            }
            runtime.safeCall(states.push(edges));
            continue lbl
          }
          break;
        }
        opsInts = StrPat.decodeInts(sections.at(3));
        opsPool = [];
        opsCount = opsInts.at(0);
        cursor = 1;
        lbl1: while (true) {
          let scrut, len, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
          scrut = opsPool.length < opsCount;
          if (scrut === true) {
            len = opsInts.at(cursor);
            tmp3 = cursor + 1;
            tmp4 = cursor + 1;
            tmp5 = tmp4 + len;
            tmp6 = runtime.safeCall(opsInts.slice(tmp3, tmp5));
            runtime.safeCall(opsPool.push(tmp6));
            tmp7 = 1 + len;
            tmp8 = cursor + tmp7;
            cursor = tmp8;
            continue lbl1
          }
          break;
        }
        tmp = StrPat.decodeInts(sections.at(1));
        tmp1 = StrPat.decodeInts(sections.at(4));
        tmp2 = StrPat.decodeBits(sections.at(5));
        return StrPat.Program(stateCount, header.at(1), header.at(2), header.at(3), header.at(4), header.at(6), tmp, states, opsPool, tmp1, tmp2)
      }
      static getProgram(table) {
        let scrut, prog;
        scrut = runtime.safeCall(StrPat.programs.has(table));
        if (scrut === true) {
          return runtime.safeCall(StrPat.programs.get(table))
        }
        prog = StrPat.decodeProgram(table);
        runtime.safeCall(StrPat.programs.set(table, prog));
        return prog;
      }
      static decodeMatcher(table) {
        let sections, header, tmp, tmp1;
        sections = runtime.safeCall(table.split(";"));
        header = StrPat.decodeInts(sections.at(0));
        tmp = StrPat.decodeInts(sections.at(1));
        tmp1 = StrPat.decodeInts(sections.at(2));
        return StrPat.Matcher(header.at(0), header.at(1), tmp, tmp1, sections.at(3))
      }
      static getMatcher(table) {
        let scrut, matcher;
        scrut = runtime.safeCall(StrPat.matchers.has(table));
        if (scrut === true) {
          return runtime.safeCall(StrPat.matchers.get(table))
        }
        matcher = StrPat.decodeMatcher(table);
        runtime.safeCall(StrPat.matchers.set(table, matcher));
        return matcher;
      }
      static classOf(prog, unit) {
        let bounds, i;
        bounds = prog.bounds;
        i = 0;
        lbl: while (true) {
          let tmp, tmp1, tmp2;
          tmp = i < bounds.length;
          if (tmp === true) {
            tmp1 = bounds.at(i) <= unit;
            if (tmp1 === true) {
              tmp2 = i + 1;
              i = tmp2;
              continue lbl
            }
          }
          break;
        }
        return i
      }
      static viable(prog, revState, state) {
        let tmp, tmp1;
        tmp = revState * prog.stateCount;
        tmp1 = tmp + state;
        return prog.viability.at(tmp1)
      }
      static unitInRanges(ranges, unit) {
        let i;
        i = 0;
        lbl: while (true) {
          let scrut, tmp, tmp1, tmp2, tmp3;
          scrut = i < ranges.length;
          if (scrut === true) {
            tmp = ranges.at(i) <= unit;
            if (tmp === true) {
              tmp2 = i + 1;
              tmp1 = unit <= ranges.at(tmp2);
              if (tmp1 === true) {
                return true
              }
              tmp3 = i + 2;
              i = tmp3;
              continue lbl;
            }
            tmp3 = i + 2;
            i = tmp3;
            continue lbl;
          }
          break;
        }
        return false
      }
      static matchWhole(table, input) {
        let matcher, rev, i, tmp;
        matcher = StrPat.getMatcher(table);
        rev = matcher.seedRev;
        i = input.length - 1;
        lbl: while (true) {
          let scrut, tmp1, tmp2, tmp3, tmp4, tmp5;
          scrut = i >= 0;
          if (scrut === true) {
            tmp1 = rev * matcher.classCount;
            tmp2 = runtime.safeCall(input.charCodeAt(i));
            tmp3 = StrPat.classOf(matcher, tmp2);
            tmp4 = tmp1 + tmp3;
            rev = matcher.revTrans.at(tmp4);
            tmp5 = i - 1;
            i = tmp5;
            continue lbl
          }
          break;
        }
        tmp = runtime.safeCall(matcher.starts.charCodeAt(rev));
        return tmp === 49
      }
      static parseRun(table, actions, input, prefix) {
        let prog, n, revArr, rev, i, scrut, gen, visited, parentState, parentOps, valStack, markStack, bindings, readSlot, execValueOp, runFrameOps, scrut1, result, s, frames, tmp, tmp1, scope27$cap;
        scope27$cap = new Capture$scope271(undefined, undefined, undefined);
        prog = StrPat.getProgram(table);
        n = input.length;
        revArr = [];
        rev = prog.seedRev;
        runtime.safeCall(revArr.push(rev));
        i = n - 1;
        lbl: while (true) {
          let scrut2, tmp2, tmp3, tmp4, tmp5, tmp6;
          scrut2 = i >= 0;
          if (scrut2 === true) {
            tmp2 = rev * prog.classCount;
            tmp3 = runtime.safeCall(input.charCodeAt(i));
            tmp4 = StrPat.classOf(prog, tmp3);
            tmp5 = tmp2 + tmp4;
            rev = prog.revTrans.at(tmp5);
            runtime.safeCall(revArr.push(rev));
            tmp6 = i - 1;
            i = tmp6;
            continue lbl
          }
          break;
        }
        scrut = StrPat.viable(prog, revArr.at(n), prog.start);
        if (scrut === false) {
          return null
        }
        scope27$cap.cur$0 = prog.start;
        scope27$cap.pos$1 = 0;
        gen = 0;
        visited = globalThis.Object.freeze(new globalThis.Map());
        parentState = globalThis.Object.freeze(new globalThis.Map());
        parentOps = globalThis.Object.freeze(new globalThis.Map());
        valStack = [];
        markStack = [];
        frames = [];
        bindings = globalThis.Object.freeze(new globalThis.Map());
        scope27$cap.remStart$2 = n;
        readSlot = lambda$6(bindings);
        execValueOp = lambda$5(scope27$cap, actions, input, valStack, markStack, bindings, readSlot);
        runFrameOps = lambda$4(execValueOp);
        lbl1: while (true) {
          let committed, tmp2, tmp3, stack, tmp4;
          tmp2 = scope27$cap.cur$0 === prog.accept;
          if (tmp2 === true) {
            tmp3 = scope27$cap.pos$1 === n;
          } else {
            tmp3 = false;
          }
          if (tmp3 === false) {
            let state;
            tmp4 = gen + 1;
            gen = tmp4;
            runtime.safeCall(visited.set(scope27$cap.cur$0, tmp4));
            stack = [];
            state = scope27$cap.cur$0;
            lambda10(prog, stack, state);
            committed = false;
            lbl2: while (true) {
              let scrut2, item, source, edge, scrut3, target, scrut4, scrut5, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
              if (committed === false) {
                scrut2 = stack.length === 0;
                if (scrut2 === true) {
                  throw runtime.safeCall(globalThis.Error("StrPat: no viable transition (this is a compiler bug)"))
                }
                tmp5 = stack.length - 1;
                item = stack.at(tmp5);
                runtime.safeCall(stack.pop());
                source = item.at(0);
                edge = item.at(1);
                scrut3 = edge.at(0) === 0;
                if (scrut3 === true) {
                  tmp6 = scope27$cap.pos$1 < n;
                  if (tmp6 === true) {
                    tmp8 = runtime.safeCall(input.charCodeAt(scope27$cap.pos$1));
                    tmp7 = StrPat.unitInRanges(edge.at(2), tmp8);
                    if (tmp7 === true) {
                      tmp10 = scope27$cap.pos$1 + 1;
                      tmp11 = n - tmp10;
                      tmp9 = StrPat.viable(prog, revArr.at(tmp11), edge.at(1));
                      if (tmp9 === true) {
                        let runOps;
                        runOps = lambda$3(prog, bindings, execValueOp, runFrameOps, frames);
                        lambda9(scope27$cap, parentState, parentOps, runOps, source);
                        scope27$cap.cur$0 = edge.at(1);
                        tmp12 = scope27$cap.pos$1 + 1;
                        scope27$cap.pos$1 = tmp12;
                        committed = true;
                        continue lbl2
                      }
                      continue lbl2;
                    }
                    continue lbl2;
                  }
                  continue lbl2;
                }
                target = edge.at(1);
                scrut4 = target === prog.accept;
                if (scrut4 === true) {
                  scrut5 = scope27$cap.pos$1 === n;
                  if (scrut5 === true) {
                    let runOps;
                    runtime.safeCall(parentState.set(target, source));
                    runtime.safeCall(parentOps.set(target, edge.at(2)));
                    runOps = lambda$3(prog, bindings, execValueOp, runFrameOps, frames);
                    lambda9(scope27$cap, parentState, parentOps, runOps, target);
                    scope27$cap.cur$0 = target;
                    committed = true;
                    continue lbl2
                  }
                  continue lbl2;
                }
                tmp13 = runtime.safeCall(visited.get(target));
                tmp14 = tmp13 !== tmp4;
                if (tmp14 === true) {
                  tmp16 = n - scope27$cap.pos$1;
                  tmp15 = StrPat.viable(prog, revArr.at(tmp16), target);
                  if (tmp15 === true) {
                    runtime.safeCall(visited.set(target, tmp4));
                    runtime.safeCall(parentState.set(target, source));
                    runtime.safeCall(parentOps.set(target, edge.at(2)));
                    lambda10(prog, stack, target);
                    continue lbl2
                  }
                  continue lbl2;
                }
                continue lbl2;
              }
              break;
            }
            continue lbl1
          }
          break;
        }
        scrut1 = valStack.length > 0;
        if (scrut1 === true) {
          tmp = runtime.safeCall(valStack.pop());
        } else {
          tmp = input;
        }
        result = [];
        runtime.safeCall(result.push(tmp));
        if (prefix === true) {
          tmp1 = runtime.safeCall(input.slice(scope27$cap.remStart$2));
          runtime.safeCall(result.push(tmp1));
        }
        s = 0;
        lbl2: while (true) {
          let scrut2, tmp2, tmp3;
          scrut2 = s < prog.slotCount;
          if (scrut2 === true) {
            tmp2 = runtime.safeCall(bindings.get(s));
            runtime.safeCall(result.push(tmp2));
            tmp3 = s + 1;
            s = tmp3;
            continue lbl2
          }
          break;
        }
        return result;
      }
      static parseWhole(table, actions, input) {
        return StrPat.parseRun(table, actions, input, false)
      }
      static parsePrefix(table, actions, input) {
        return StrPat.parseRun(table, actions, input, true)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "StrPat"];
    });
    Runtime.render = Rendering.render;
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
        TraceLogger.enabled = false;
        TraceLogger.indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp = prev + 1;
          TraceLogger.indentLvl = tmp;
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
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp = runtime.safeCall(("| ").repeat(TraceLogger.indentLvl));
          tmp1 = runtime.safeCall(("  ").repeat(TraceLogger.indentLvl));
          tmp2 = "\n" + tmp1;
          tmp3 = runtime.safeCall(msg.replaceAll("\n", tmp2));
          tmp4 = tmp + tmp3;
          return runtime.safeCall(globalThis.console.log(tmp4))
        }
        return runtime.Unit;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "TraceLogger"];
    });
    Runtime.curEffect = null;
    Runtime.resumeValue = null;
    Runtime.resumeArr = null;
    Runtime.resumeIdx = null;
    Runtime.resumePc = -1;
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
        let i, f, argListsLength, currentArgList, scrut, argListLength, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
        i = 0;
        f = this.saved.at(0);
        argListsLength = this.saved.at(5);
        currentArgList = 6;
        Runtime.resumeValue = value;
        Runtime.resumeArr = this.saved;
        Runtime.resumePc = this.saved.at(1);
        scrut = argListsLength === 0;
        if (scrut === true) {
          runtime.safeCall(globalThis.console.log("cannot resume getters"));
        }
        lbl: while (true) {
          let scrut1, argListLength1, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
          tmp6 = argListsLength - 1;
          scrut1 = i < tmp6;
          if (scrut1 === true) {
            argListLength1 = this.saved.at(currentArgList);
            tmp7 = currentArgList + 1;
            tmp8 = currentArgList + 1;
            tmp9 = tmp8 + argListLength1;
            tmp10 = runtime.safeCall(this.saved.slice(tmp7, tmp9));
            tmp11 = runtime.safeCall(f.apply(this.saved.at(4), tmp10));
            f = tmp11;
            tmp12 = argListLength1 + 1;
            tmp13 = currentArgList + tmp12;
            currentArgList = tmp13;
            tmp14 = i + 1;
            i = tmp14;
            continue lbl
          }
          break;
        }
        argListLength = this.saved.at(currentArgList);
        tmp = currentArgList + argListLength;
        tmp1 = tmp + 2;
        Runtime.resumeIdx = tmp1;
        tmp2 = currentArgList + 1;
        tmp3 = currentArgList + 1;
        tmp4 = tmp3 + argListLength;
        tmp5 = runtime.safeCall(this.saved.slice(tmp2, tmp4));
        return runtime.safeCall(f.apply(this.saved.at(4), tmp5))
      }
      get getLocals() {
        let debugInfo, i, cur, res, i1;
        debugInfo = this.saved.at(3);
        i = 0;
        cur = 6;
        lbl: while (true) {
          let scrut, tmp, tmp1, tmp2;
          scrut = i < this.saved.at(5);
          if (scrut === true) {
            tmp = this.saved.at(cur) + 1;
            tmp1 = cur + tmp;
            cur = tmp1;
            tmp2 = i + 1;
            i = tmp2;
            continue lbl
          }
          break;
        }
        res = [];
        i1 = 1;
        lbl1: while (true) {
          let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
          scrut = i1 < debugInfo.length;
          if (scrut === true) {
            tmp = i1 + 1;
            tmp1 = cur + 1;
            tmp2 = tmp1 + debugInfo.at(i1);
            tmp3 = globalThis.Object.freeze(new Runtime.LocalVarInfo.class(debugInfo.at(tmp), this.saved.at(tmp2)));
            runtime.safeCall(res.push(tmp3));
            tmp4 = i1 + 2;
            i1 = tmp4;
            continue lbl1
          }
          break;
        }
        return res;
      }
      get getNme() {
        return this.saved.at(3).at(0);
      }
      get getLoc() {
        let loc;
        loc = this.saved.at(2);
        if (loc === null) {
          return "pc=" + this.saved.at(1)
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
    Runtime.stackLimit = 0;
    Runtime.stackDepth = 0;
    Runtime.stackHandler = null;
    Runtime.stackResume = null;
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
        lambda$here = lambda$7(Runtime);
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
        let tmp, tmp1;
        tmp = runtime.safeCall(Runtime.shl(1, 31));
        tmp1 = runtime.safeCall(Runtime.bitnot(tmp));
        return runtime.safeCall(Runtime.bitand(this.#v, tmp1))
      }
      sext() {
        let tmp;
        tmp = runtime.safeCall(Runtime.shl(1, 31));
        return runtime.safeCall(Runtime.bitor(this.#v, tmp))
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
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    tmp = got < expected;
    if (tmp === false) {
      if (isUB === true) {
        tmp2 = got > expected;
      } else {
        tmp2 = false;
      }
      tmp1 = tmp2;
    } else {
      tmp1 = true;
    }
    if (tmp1 === true) {
      scrut = functionName.length > 0;
      if (scrut === true) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      tmp5 = "Function" + tmp4;
      tmp6 = tmp5 + " expected ";
      if (isUB === true) {
        tmp7 = "";
      } else {
        tmp7 = "at least ";
      }
      tmp8 = tmp6 + tmp7;
      tmp9 = tmp8 + expected;
      tmp10 = tmp9 + " argument";
      scrut1 = expected === 1;
      if (scrut1 === true) {
        tmp11 = "";
      } else {
        tmp11 = "s";
      }
      tmp12 = tmp10 + tmp11;
      tmp13 = tmp12 + " but got ";
      tmp14 = tmp13 + got;
      throw runtime.safeCall(globalThis.Error(tmp14))
    }
    return runtime.Unit;
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
    let res, scrut, tmp;
    res = runtime.safeCall(f());
    scrut = Runtime.curEffect !== null;
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
    let tr, v, tmp, tmp1;
    tr = Runtime.curEffect;
    v = null;
    lbl: while (true) {
      let scrut, tmp2, tmp3;
      if (tr instanceof Runtime.EffectSig.class) {
        scrut = tr.handler === Runtime.PrintStackEffect;
        if (scrut === true) {
          tmp2 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
          runtime.safeCall(globalThis.console.log(tmp2));
          Runtime.curEffect = null;
          tmp3 = Runtime.resume(tr.contTrace)(runtime.Unit);
          v = tmp3;
          tr = Runtime.curEffect;
          continue lbl
        }
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      Runtime.curEffect = null;
      tmp = "Error: Unhandled effect " + tr.handler["constructor"]["name"];
      tmp1 = Runtime.showStackTrace(tmp, tr, debug, false);
      throw Runtime.CustomStackError(tmp1)
    }
    return v;
  }
  static illegalEffect(position) {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Runtime.curEffect;
    Runtime.curEffect = null;
    tmp1 = "Error: Effect " + tmp.handler["constructor"]["name"];
    tmp2 = tmp1 + " is raised ";
    tmp3 = tmp2 + position;
    tmp4 = Runtime.showStackTrace(tmp3, tmp, false, false);
    throw Runtime.CustomStackError(tmp4)
  }
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      lbl: while (true) {
        let scrut, cur, scrut1, tmp, tmp1;
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          lbl1: while (true) {
            let scrut2, curLocals, loc, scrut3, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
            scrut2 = cur !== null;
            if (scrut2 === true) {
              curLocals = cur.getLocals;
              loc = cur.getLoc;
              if (showLocals === true) {
                scrut3 = curLocals.length > 0;
                if (scrut3 === true) {
                  tmp2 = runtime.safeCall(curLocals.map(lambda));
                  tmp3 = runtime.safeCall(tmp2.join(", "));
                  tmp4 = " with locals: " + tmp3;
                } else {
                  tmp4 = "";
                }
              } else {
                tmp4 = "";
              }
              tmp5 = "\n\tat " + cur.getNme;
              tmp6 = tmp5 + " (";
              tmp7 = tmp6 + loc;
              tmp8 = tmp7 + ")";
              tmp9 = msg + tmp8;
              tmp10 = tmp9 + tmp4;
              msg = tmp10;
              cur = cur.next;
              atTail = false;
              continue lbl1
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut1 = curHandler !== null;
          if (scrut1 === true) {
            tmp = "\n\twith handler " + curHandler.handler["constructor"]["name"];
            tmp1 = msg + tmp;
            msg = tmp1;
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
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, scope70$cap;
    scope70$cap = new Capture$scope701(undefined);
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont["constructor"]["name"] + "(pc=";
      scope70$cap.result$0 = tmp + cont.saved.at(1);
      runtime.safeCall(hl.forEach(lambda$8(scope70$cap, cont)));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp1 = reps + 1;
        reps = tmp1;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp2 = scope70$cap.result$0 + ", REPEAT";
        scope70$cap.result$0 = tmp2;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp3 = scope70$cap.result$0 + ") -> ";
      tmp4 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp3 + tmp4
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT CONT)";
  }
  static showHandlerContChain(cont, hl, vis, reps) {
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, scope72$cap;
    scope72$cap = new Capture$scope721(undefined);
    if (cont instanceof Runtime.HandlerContFrame.class) {
      scope72$cap.result$0 = cont.handler["constructor"]["name"];
      runtime.safeCall(hl.forEach(lambda$9(scope72$cap, cont)));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp = reps + 1;
        reps = tmp;
        scrut1 = reps > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp1 = scope72$cap.result$0 + ", REPEAT";
        scope72$cap.result$0 = tmp1;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp2 = scope72$cap.result$0 + " -> ";
      tmp3 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp2 + tmp3
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT HANDLER CONT)";
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
    let scrut, scrut1, vis, hl, cur, tmp, tmp1, tmp2, tmp3, tmp4;
    if (contTrace instanceof Runtime.ContTrace.class) {
      runtime.safeCall(globalThis.console.log("resumed: ", contTrace.resumed));
      scrut = contTrace.last === contTrace;
      if (scrut === true) {
        runtime.safeCall(globalThis.console.log("<last is self>"));
      }
      scrut1 = contTrace.lastHandler === contTrace;
      if (scrut1 === true) {
        runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      }
      vis = globalThis.Object.freeze(new globalThis.Set());
      hl = globalThis.Object.freeze(new globalThis.Map());
      tmp = globalThis.Object.freeze([
        contTrace.last
      ]);
      tmp1 = globalThis.Object.freeze(new globalThis.Set(tmp));
      runtime.safeCall(hl.set("last", tmp1));
      tmp2 = globalThis.Object.freeze([
        contTrace.lastHandler
      ]);
      tmp3 = globalThis.Object.freeze(new globalThis.Set(tmp2));
      runtime.safeCall(hl.set("last-handler", tmp3));
      tmp4 = Runtime.showFunctionContChain(contTrace.next, hl, vis, 0);
      runtime.safeCall(globalThis.console.log(tmp4));
      cur = contTrace.nextHandler;
      lbl: while (true) {
        let scrut2, tmp5;
        scrut2 = cur !== null;
        if (scrut2 === true) {
          tmp5 = Runtime.showHandlerContChain(cur, hl, vis, 0);
          runtime.safeCall(globalThis.console.log(tmp5));
          cur = cur.nextHandler;
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
    if (eff instanceof Runtime.EffectSig.class) {
      runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      runtime.safeCall(globalThis.console.log("handler: ", eff.handler["constructor"]["name"]));
      runtime.safeCall(globalThis.console.log("handlerFun: ", eff.handlerFun));
      return Runtime.debugContTrace(eff.contTrace)
    }
    runtime.safeCall(globalThis.console.log("Not an effect:"));
    return runtime.safeCall(globalThis.console.log(eff));
  }
  static unwind(...saved) {
    let tmp;
    tmp = new Runtime.FunctionContFrame.class(null, saved);
    Runtime.curEffect.contTrace.last.next = tmp;
    Runtime.curEffect.contTrace.last = Runtime.curEffect.contTrace.last.next;
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
    let handlerFrame;
    handlerFrame = new Runtime.HandlerContFrame.class(null, null, handler);
    cur.contTrace.lastHandler.nextHandler = handlerFrame;
    cur.contTrace.lastHandler = handlerFrame;
    cur.contTrace.last = handlerFrame;
    return Runtime.handleEffects(cur)
  }
  static enterHandleBlock(handler, body) {
    let tmp, scrut;
    tmp = runtime.safeCall(body());
    scrut = Runtime.curEffect === null;
    if (scrut === true) {
      return tmp
    }
    return Runtime.handleBlockImpl(Runtime.curEffect, handler);
  }
  static handleEffects(cur) {
    lbl: while (true) {
      let nxt, scrut;
      if (cur instanceof Runtime.EffectSig.class) {
        nxt = Runtime.handleEffect(cur);
        scrut = cur === nxt;
        if (scrut === true) {
          Runtime.curEffect = cur;
          return null
        }
        cur = nxt;
        continue lbl;
      }
      return cur;
    }
  }
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, handlerFrame, saved, scrut1, scrut2, old, scrut3, scrut4, scrut5, scrut6, tmp, tmp1, tmp2, tmp3;
    prevHandlerFrame = cur.contTrace;
    lbl: while (true) {
      let scrut7, scrut8;
      scrut7 = prevHandlerFrame.nextHandler !== null;
      if (scrut7 === true) {
        scrut8 = prevHandlerFrame.nextHandler.handler !== cur.handler;
        if (scrut8 === true) {
          prevHandlerFrame = prevHandlerFrame.nextHandler;
          continue lbl
        }
      }
      break;
    }
    scrut = prevHandlerFrame.nextHandler === null;
    if (scrut === true) {
      return cur
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    saved = new Runtime.ContTrace.class(handlerFrame.next, cur.contTrace.last, handlerFrame.nextHandler, cur.contTrace.lastHandler, false);
    scrut1 = cur.contTrace.last === handlerFrame;
    if (scrut1 === true) {
      saved.last = saved;
    }
    scrut2 = cur.contTrace.lastHandler === handlerFrame;
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
      tmp1 = Runtime.stackDepth + 2;
      Runtime.stackDepth = tmp1;
      tmp2 = Runtime.resume(cur.contTrace);
      tmp3 = runtime.safeCall(cur.handlerFun(tmp2));
      tmp = tmp3;
    } finally {
      Runtime.stackDepth = old;
    }
    scrut3 = Runtime.curEffect !== null;
    if (scrut3 === true) {
      cur = Runtime.curEffect;
      scrut4 = saved.next !== null;
      if (scrut4 === true) {
        cur.contTrace.last.next = saved.next;
      }
      scrut5 = saved.last !== saved;
      if (scrut5 === true) {
        cur.contTrace.last = saved.last;
      }
      scrut6 = saved.nextHandler !== null;
      if (scrut6 === true) {
        cur.contTrace.lastHandler.nextHandler = saved.nextHandler;
        cur.contTrace.lastHandler = saved.lastHandler;
        return cur
      }
      return cur;
    }
    return Runtime.resumeContTrace(saved, tmp);
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
    let cont, handlerCont;
    cont = contTrace.next;
    handlerCont = contTrace.nextHandler;
    lbl: while (true) {
      let old, scrut, scrut1, scrut2, tmp, tmp1, tmp2;
      if (cont instanceof Runtime.FunctionContFrame.class) {
        Runtime.curEffect = null;
        old = Runtime.stackDepth;
        try {
          tmp1 = Runtime.stackDepth + 3;
          Runtime.stackDepth = tmp1;
          tmp2 = cont.resume(value);
          tmp = tmp2;
        } finally {
          Runtime.stackDepth = old;
        }
        value = tmp;
        scrut = Runtime.curEffect !== null;
        if (scrut === true) {
          value = Runtime.curEffect;
        }
        if (value instanceof Runtime.EffectSig.class) {
          value.contTrace.last.next = cont.next;
          value.contTrace.lastHandler.nextHandler = handlerCont;
          scrut1 = contTrace.last !== cont;
          if (scrut1 === true) {
            value.contTrace.last = contTrace.last;
          }
          scrut2 = handlerCont !== null;
          if (scrut2 === true) {
            value.contTrace.lastHandler = contTrace.lastHandler;
            return value
          }
          return value;
        }
        cont = cont.next;
        continue lbl;
      }
      if (handlerCont instanceof Runtime.HandlerContFrame.class) {
        cont = handlerCont.next;
        handlerCont = handlerCont.nextHandler;
        continue lbl
      }
      return value;
    }
  }
  static await(promise) {
    let lambda$here;
    lambda$here = lambda$10(Runtime, promise);
    return Runtime.mkEffect(Runtime.AsyncEffectMarker, lambda$here)
  }
  static toJsAsync(thunk) {
    let r, scrut;
    r = Runtime.enterHandleBlock(Runtime.AsyncEffectMarker, thunk);
    scrut = Runtime.curEffect !== null;
    if (scrut === true) {
      Runtime.illegalEffect("in exported async function");
      return runtime.safeCall(globalThis.Promise.resolve(r))
    }
    return runtime.safeCall(globalThis.Promise.resolve(r));
  }
  static checkDepth() {
    let tmp, tmp1;
    tmp = Runtime.stackDepth >= Runtime.stackLimit;
    if (tmp === true) {
      tmp1 = Runtime.stackHandler !== null;
      if (tmp1 === true) {
        return Runtime.stackHandler.delay()
      }
      return runtime.Unit;
    }
    return runtime.Unit;
  }
  static runStackSafe(limit, f) {
    let old, old1, old2, result, scrut, tmp, tmp1, tmp2;
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
          scrut = Runtime.curEffect !== null;
          if (scrut === true) {
            throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
          }
          lbl: while (true) {
            let scrut1, saved, scrut2, tmp3;
            scrut1 = Runtime.stackResume !== null;
            if (scrut1 === true) {
              saved = Runtime.stackResume;
              Runtime.stackResume = null;
              Runtime.stackDepth = 1;
              tmp3 = runtime.safeCall(saved(runtime.Unit));
              result = tmp3;
              scrut2 = Runtime.curEffect !== null;
              if (scrut2 === true) {
                throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
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
  static plus_impl(lhs, rhs) {
    if (lhs instanceof Runtime.Int31.class) {
      if (rhs instanceof Runtime.Int31.class) {
        return lhs + rhs
      }
      return Runtime.unreachable;
    }
    return Runtime.unreachable;
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
export { lambda6 as _$_modulePrivate_$_lambda6 };
export { lambda7 as _$_modulePrivate_$_lambda7 };
export { lambda8 as _$_modulePrivate_$_lambda8 };
export { lambda9 as _$_modulePrivate_$_lambda9 };
export { lambda10 as _$_modulePrivate_$_lambda10 };
export { lambda11 as _$_modulePrivate_$_lambda11 };
export { lambda$ as _$_modulePrivate_$_lambda$ };
export { Capture$scope271 as _$_modulePrivate_$_Capture$scope27 };
export { lambda$1 as _$_modulePrivate_$_lambda$1 };
export { lambda$2 as _$_modulePrivate_$_lambda$2 };
export { lambda$3 as _$_modulePrivate_$_lambda$3 };
export { lambda$4 as _$_modulePrivate_$_lambda$4 };
export { lambda$5 as _$_modulePrivate_$_lambda$5 };
export { lambda$6 as _$_modulePrivate_$_lambda$6 };
export { lambda$7 as _$_modulePrivate_$_lambda$7 };
export { Capture$scope701 as _$_modulePrivate_$_Capture$scope70 };
export { lambda$8 as _$_modulePrivate_$_lambda$8 };
export { Capture$scope721 as _$_modulePrivate_$_Capture$scope72 };
export { lambda$9 as _$_modulePrivate_$_lambda$9 };
export { lambda$10 as _$_modulePrivate_$_lambda$10 };
export { continuation$ as _$_modulePrivate_$_continuation$ };
export default Runtime1;
