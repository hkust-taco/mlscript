let Predef1;
Predef1 = class Predef {
  static {
    this.assert = globalThis.console.assert;
    this.foldl = Predef.fold;
    this.MatchResult = function MatchResult(captures1) { return new MatchResult.class(captures1); };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
      }
      toString() { return "MatchResult(" + globalThis.Predef.render(this.captures) + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) { return new MatchFailure.class(errors1); };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return "MatchFailure(" + globalThis.Predef.render(this.errors) + ")"; }
    };
    this.TraceLogger = class TraceLogger {
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
          return prev;
        } else {
          return null;
        }
      } 
      static resetIndent(n) {
        let scrut;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          TraceLogger.indentLvl = n;
          return null;
        } else {
          return null;
        }
      } 
      static log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp = "| ".repeat(TraceLogger.indentLvl) ?? null;
          tmp1 = "  ".repeat(TraceLogger.indentLvl) ?? null;
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return globalThis.console.log(tmp4) ?? null;
        } else {
          return null;
        }
      }
      static toString() { return "TraceLogger"; }
    };
    this.Test = class Test {
      constructor() {
        let tmp;
        tmp = Predef.print("Test");
        this.y = 1;
      }
      toString() { return "Test"; }
    };
    this.__Cont = function __Cont(next1) { return new __Cont.class(next1); };
    this.__Cont.class = class __Cont {
      constructor(next) {
        this.next = next;
      }
      toString() { return "__Cont(" + globalThis.Predef.render(this.next) + ")"; }
    };
    this.__TailList = function __TailList(next1) { return new __TailList.class(next1); };
    this.__TailList.class = class __TailList {
      constructor(next) {
        this.next = next;
      }
      toString() { return "__TailList(" + globalThis.Predef.render(this.next) + ")"; }
    };
    this.__ListWithTail = function __ListWithTail(next1, tail1) { return new __ListWithTail.class(next1, tail1); };
    this.__ListWithTail.class = class __ListWithTail {
      constructor(next, tail) {
        this.next = next;
        this.tail = tail;
      }
      append(elem) {
        this.tail.next = elem;
        this.tail = elem;
        return null;
      }
      toString() { return "__ListWithTail(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.__HandleBlock = function __HandleBlock(contHead1, lastHandlerCont1, next1, handler1) { return new __HandleBlock.class(contHead1, lastHandlerCont1, next1, handler1); };
    this.__HandleBlock.class = class __HandleBlock {
      constructor(contHead, lastHandlerCont, next, handler) {
        this.contHead = contHead;
        this.lastHandlerCont = lastHandlerCont;
        this.next = next;
        this.handler = handler;
      }
      toString() { return "__HandleBlock(" + globalThis.Predef.render(this.contHead) + ", " + globalThis.Predef.render(this.lastHandlerCont) + ", " + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.handler) + ")"; }
    };
    this.__EffectSig = function __EffectSig(next1, tail1, handleBlockList1, resumed1, handler1, handlerFun1) { return new __EffectSig.class(next1, tail1, handleBlockList1, resumed1, handler1, handlerFun1); };
    this.__EffectSig.class = class __EffectSig {
      constructor(next, tail, handleBlockList, resumed, handler, handlerFun) {
        this.next = next;
        this.tail = tail;
        this.handleBlockList = handleBlockList;
        this.resumed = resumed;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return "__EffectSig(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.tail) + ", " + globalThis.Predef.render(this.handleBlockList) + ", " + globalThis.Predef.render(this.resumed) + ", " + globalThis.Predef.render(this.handler) + ", " + globalThis.Predef.render(this.handlerFun) + ")"; }
    };
    this.__Return = function __Return(value1) { return new __Return.class(value1); };
    this.__Return.class = class __Return {
      constructor(value) {
        this.value = value;
      }
      toString() { return "__Return(" + globalThis.Predef.render(this.value) + ")"; }
    };
    this.__stackLimit = 0;
    this.__stackDepth = 0;
    this.__stackOffset = 0;
    this.__stackHandler = null;
    this.__StackDelay = function __StackDelay() { return new __StackDelay.class(); };
    this.__StackDelay.class = class __StackDelay {
      constructor() {}
      toString() { return "__StackDelay(" + "" + ")"; }
    };
  }
  static id(x) {
    return x;
  } 
  static not(x1) {
    if (x1 === false) {
      return true;
    } else {
      return false;
    }
  } 
  static pipeInto(x2, f) {
    return f(x2) ?? null;
  } 
  static pipeFrom(f1, x3) {
    return f1(x3) ?? null;
  } 
  static andThen(f2, g) {
    return (x4) => {
      let tmp;
      tmp = f2(x4) ?? null;
      return g(tmp) ?? null;
    };
  } 
  static compose(f3, g1) {
    return (x4) => {
      let tmp;
      tmp = g1(x4) ?? null;
      return f3(tmp) ?? null;
    };
  } 
  static passTo(receiver, f4) {
    return (...args) => {
      return f4(receiver, ...args) ?? null;
    };
  } 
  static call(receiver1, f5) {
    return (...args) => {
      return f5.call(receiver1, ...args);
    };
  } 
  static pass1(f6) {
    return (...xs) => {
      return f6(xs[0]) ?? null;
    };
  } 
  static pass2(f7) {
    return (...xs) => {
      return f7(xs[0], xs[1]) ?? null;
    };
  } 
  static pass3(f8) {
    return (...xs) => {
      return f8(xs[0], xs[1], xs[2]) ?? null;
    };
  } 
  static print(...xs) {
    let tmp, tmp1;
    tmp = Predef.map(Predef.renderAsStr);
    tmp1 = tmp(...xs) ?? null;
    return globalThis.console.log(...tmp1) ?? null;
  } 
  static interleave(sep) {
    return (...args) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
      scrut2 = args.length === 0;
      if (scrut2 === true) {
        return [];
      } else {
        tmp = args.length * 2;
        tmp1 = tmp - 1;
        tmp2 = globalThis.Array(tmp1);
        res = tmp2;
        len = args.length;
        i = 0;
        tmp8: while (true) {
          scrut = i < len;
          if (scrut === true) {
            tmp3 = i * 2;
            idx = tmp3;
            res[idx] = args[i];
            tmp4 = i + 1;
            i = tmp4;
            scrut1 = i < len;
            if (scrut1 === true) {
              tmp5 = idx + 1;
              res[tmp5] = sep;
              tmp6 = null;
            } else {
              tmp6 = null;
            }
            tmp7 = tmp6;
            continue tmp8;
          } else {
            tmp7 = null;
          }
          break;
        }
        return res;
      }
    };
  } 
  static renderAsStr(arg) {
    if (typeof arg === 'string') {
      return arg;
    } else {
      return Predef.render(arg);
    }
  } 
  static render(arg1) {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    if (arg1 instanceof globalThis.Array) {
      tmp = Predef.fold((arg11, arg2) => {
        return arg11 + arg2;
      });
      tmp1 = Predef.interleave(", ");
      tmp2 = Predef.map(Predef.render);
      tmp3 = tmp2(...arg1) ?? null;
      tmp4 = tmp1(...tmp3) ?? null;
      return tmp("[", ...tmp4, "]") ?? null;
    } else {
      if (typeof arg1 === 'string') {
        return globalThis.JSON.stringify(arg1) ?? null;
      } else {
        return globalThis.String(arg1);
      }
    }
  } 
  static notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw globalThis.Error(tmp);
  } 
  static get notImplementedError() {
    throw globalThis.Error("Not implemented");
  } 
  static tuple(...xs1) {
    return xs1;
  } 
  static tupleSlice(xs2, i, j) {
    let tmp;
    tmp = xs2.length - j;
    return globalThis.Array.prototype.slice.call(xs2, i, tmp) ?? null;
  } 
  static tupleGet(xs3, i1) {
    return globalThis.Array.prototype.at.call(xs3, i1);
  } 
  static map(f9) {
    return (...xs4) => {
      let tmp;
      tmp = Predef.pass1(f9);
      return xs4.map(tmp) ?? null;
    };
  } 
  static fold(f10) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3;
      i2 = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i2 < len;
        if (scrut === true) {
          tmp = rest.at(i2) ?? null;
          tmp1 = f10(init, tmp) ?? null;
          init = tmp1;
          tmp2 = i2 + 1;
          i2 = tmp2;
          tmp3 = null;
          continue tmp4;
        } else {
          tmp3 = null;
        }
        break;
      }
      return init;
    };
  } 
  static foldr(f11) {
    return (first, ...rest) => {
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first;
      } else {
        tmp = len - 1;
        i2 = tmp;
        tmp1 = rest.at(i2) ?? null;
        init = tmp1;
        tmp6: while (true) {
          scrut = i2 > 0;
          if (scrut === true) {
            tmp2 = i2 - 1;
            i2 = tmp2;
            tmp3 = rest.at(i2) ?? null;
            tmp4 = f11(tmp3, init) ?? null;
            init = tmp4;
            tmp5 = null;
            continue tmp6;
          } else {
            tmp5 = null;
          }
          break;
        }
        return f11(first, init) ?? null;
      }
    };
  } 
  static stringStartsWith(string, prefix) {
    return string.startsWith(prefix) ?? null;
  } 
  static stringGet(string1, i2) {
    return string1.at(i2) ?? null;
  } 
  static stringDrop(string2, n) {
    return string2.slice(n) ?? null;
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
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
      tmp5 = Predef.fold((arg11, arg2) => {
        return arg11 + arg2;
      });
      if (isUB === true) {
        tmp6 = "";
      } else {
        tmp6 = "at least ";
      }
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp7 = "";
      } else {
        tmp7 = "s";
      }
      tmp8 = tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got) ?? null;
      throw globalThis.Error(tmp8);
    } else {
      return null;
    }
  } 
  static __mkListWithTail() {
    let res, tmp;
    tmp = new Predef.__ListWithTail.class(null, null);
    res = tmp;
    res.tail = res;
    return res;
  } 
  static __appendInCont(eff, cont) {
    let scrut, scrut1, tmp, tmp1;
    scrut = eff.tail;
    if (scrut instanceof Predef.__TailList.class) {
      scrut1 = cont.next !== null;
      if (scrut1 === true) {
        throw globalThis.Error("unexpected handler continuation");
      } else {
        tmp = null;
      }
      cont.next = eff.tail.next;
      eff.tail.next = cont;
      tmp1 = null;
    } else {
      eff.tail.next = cont;
      tmp1 = null;
    }
    return eff;
  } 
  static __mkEffect(handler, handlerFun) {
    let res, tmp, tmp1;
    tmp = Predef.__mkListWithTail();
    tmp1 = new Predef.__EffectSig.class(null, null, tmp, false, handler, handlerFun);
    res = tmp1;
    res.tail = res;
    return res;
  } 
  static __handleBlockImpl(cur, handler1) {
    let handleBlock, nxt, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Predef.__TailList(null);
    tmp1 = new Predef.__HandleBlock.class(tmp, null, null, handler1);
    handleBlock = tmp1;
    tmp2 = cur.handleBlockList.append(handleBlock) ?? null;
    tmp7: while (true) {
      if (cur instanceof Predef.__EffectSig.class) {
        tmp3 = Predef.__handleEffect(cur);
        nxt = tmp3;
        scrut = cur === nxt;
        if (scrut === true) {
          scrut1 = handleBlock.lastHandlerCont === null;
          if (scrut1 === true) {
            cur.tail = handleBlock.contHead;
            tmp4 = null;
          } else {
            cur.tail = handleBlock.lastHandlerCont;
            tmp4 = null;
          }
          return cur;
        } else {
          cur = nxt;
          tmp5 = null;
        }
        tmp6 = tmp5;
        continue tmp7;
      } else {
        return cur;
      }
      break;
    }
    return tmp6;
  } 
  static __handleEffect(cur1) {
    let prevBlock, scrut, scrut1, scrut2, handleBlock, origTailBlock, savedNext, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    prevBlock = cur1.handleBlockList;
    tmp6: while (true) {
      scrut = prevBlock.next;
      if (scrut instanceof Predef.__HandleBlock.class) {
        scrut1 = prevBlock.next.handler !== cur1.handler;
        if (scrut1 === true) {
          prevBlock = prevBlock.next;
          tmp = null;
          continue tmp6;
        } else {
          tmp = null;
        }
      } else {
        tmp = null;
      }
      break;
    }
    scrut2 = prevBlock.next === null;
    if (scrut2 === true) {
      return cur1;
    } else {
      tmp1 = null;
    }
    handleBlock = prevBlock.next;
    origTailBlock = cur1.handleBlockList.tail;
    prevBlock.next = null;
    cur1.handleBlockList.tail = prevBlock;
    savedNext = handleBlock.contHead.next;
    tmp2 = Predef.__resume(cur1, handleBlock.contHead);
    tmp3 = cur1.handlerFun(tmp2) ?? null;
    cur1 = tmp3;
    scrut3 = savedNext !== handleBlock.contHead.next;
    if (scrut3 === true) {
      handleBlock.contHead.next.next = savedNext;
      scrut4 = handleBlock.lastHandlerCont === null;
      if (scrut4 === true) {
        handleBlock.lastHandlerCont = handleBlock.contHead.next;
        tmp4 = null;
      } else {
        tmp4 = null;
      }
      tmp5 = tmp4;
    } else {
      tmp5 = null;
    }
    if (cur1 instanceof Predef.__EffectSig.class) {
      cur1.handleBlockList.tail.next = handleBlock;
      cur1.handleBlockList.tail = origTailBlock;
      return cur1;
    } else {
      return Predef.__resumeHandleBlocks(handleBlock, origTailBlock, cur1);
    }
  } 
  static __resume(cur2, tail) {
    return (value) => {
      let scrut, cont1, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
      scrut = cur2.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption");
      } else {
        tmp = null;
      }
      cur2.resumed = true;
      cont1 = cur2.next;
      tmp10: while (true) {
        if (cont1 instanceof Predef.__Cont.class) {
          tmp1 = cont1.resume(value) ?? null;
          value = tmp1;
          if (value instanceof Predef.__EffectSig.class) {
            scrut1 = value.tail.next !== cont1;
            if (scrut1 === true) {
              scrut2 = cont1.next !== null;
              if (scrut2 === true) {
                scrut3 = value.tail.next !== null;
                if (scrut3 === true) {
                  throw globalThis.Error("Internal Error: unexpected continuation");
                } else {
                  tmp2 = null;
                }
              } else {
                tmp2 = null;
              }
              tmp3 = tmp2;
            } else {
              tmp3 = null;
            }
            scrut4 = value.tail.next === null;
            if (scrut4 === true) {
              value.tail.next = cont1.next;
              tmp4 = null;
            } else {
              tmp4 = null;
            }
            value.tail = tail;
            scrut5 = cur2.handleBlockList.next !== null;
            if (scrut5 === true) {
              value.handleBlockList.tail.next = cur2.handleBlockList.next;
              value.handleBlockList.tail = cur2.handleBlockList.tail;
              tmp5 = null;
            } else {
              tmp5 = null;
            }
            return value;
          } else {
            cont1 = cont1.next;
            tmp6 = null;
          }
          tmp7 = tmp6;
          continue tmp10;
        } else {
          tmp7 = null;
        }
        break;
      }
      scrut6 = cur2.handleBlockList.next === null;
      if (scrut6 === true) {
        return value;
      } else {
        tmp8 = Predef.__resumeHandleBlocks(cur2.handleBlockList.next, cur2.handleBlockList.tail, value);
        cur2 = tmp8;
        if (cur2 instanceof Predef.__EffectSig.class) {
          cur2.tail = tail;
          tmp9 = null;
        } else {
          tmp9 = null;
        }
        return cur2;
      }
    };
  } 
  static __resumeHandleBlocks(handleBlock, tailHandleBlock, value) {
    let scrut, scrut1, scrut2, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp5: while (true) {
      scrut1 = handleBlock.contHead.next;
      if (scrut1 instanceof Predef.__Cont.class) {
        tmp = handleBlock.contHead.next.resume(value) ?? null;
        value = tmp;
        if (value instanceof Predef.__EffectSig.class) {
          scrut2 = value.tail.next !== handleBlock.contHead.next;
          if (scrut2 === true) {
            scrut3 = value.tail.next !== null;
            if (scrut3 === true) {
              throw globalThis.Error("Internal Error: unexpected continuation during handle block resumption");
            } else {
              tmp1 = null;
            }
          } else {
            tmp1 = null;
          }
          scrut4 = value.tail.next !== handleBlock.contHead.next;
          if (scrut4 === true) {
            handleBlock.contHead.next = handleBlock.contHead.next.next;
            tmp2 = null;
          } else {
            tmp2 = null;
          }
          value.tail.next = null;
          value.handleBlockList.tail.next = handleBlock;
          value.handleBlockList.tail = tailHandleBlock;
          return value;
        } else {
          handleBlock.contHead.next = handleBlock.contHead.next.next;
          tmp3 = null;
        }
        tmp4 = tmp3;
        continue tmp5;
      } else {
        scrut = handleBlock.next;
        if (scrut instanceof Predef.__HandleBlock.class) {
          handleBlock = handleBlock.next;
          tmp4 = null;
          continue tmp5;
        } else {
          return value;
        }
      }
      break;
    }
    return tmp4;
  }
  static toString() { return "Predef"; }
};
null
let Predef = Predef1; export default Predef;
