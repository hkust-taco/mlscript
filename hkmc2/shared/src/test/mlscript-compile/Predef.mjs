const Predef$class = class Predef {
  constructor() {
    this.assert = console.assert;
    this.foldl = this.fold;
    this.MatchResult = function MatchResult(captures1) { return new MatchResult.class(captures1); };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
      }
      toString() { return "MatchResult(" + this.captures + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) { return new MatchFailure.class(errors1); };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return "MatchFailure(" + this.errors + ")"; }
    };
    const TraceLogger$class = class TraceLogger {
      constructor() {
        this.enabled = false;
        this.indentLvl = 0;
      }
      indent() {
        let scrut, prev, tmp;
        scrut = this.enabled;
        if (scrut === true) {
          prev = this.indentLvl;
          tmp = prev + 1;
          this.indentLvl = tmp;
          return prev;
        } else {
          return null;
        }
      } 
      resetIndent(n) {
        let scrut;
        scrut = this.enabled;
        if (scrut === true) {
          this.indentLvl = n;
          return null;
        } else {
          return null;
        }
      } 
      log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = this.enabled;
        if (scrut === true) {
          tmp = "| ".repeat(this.indentLvl) ?? null;
          tmp1 = "  ".repeat(this.indentLvl) ?? null;
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return console.log(tmp4) ?? null;
        } else {
          return null;
        }
      }
      toString() { return "TraceLogger"; }
    };
    this.TraceLogger = new TraceLogger$class;
    this.TraceLogger.class = TraceLogger$class;
    const this$Predef = this;
    this.Test = class Test {
      constructor() {
        let tmp;
        tmp = this$Predef.print("Test");
        this.y = 1;
      }
      toString() { return "Test"; }
    };
    this.__Cont = function __Cont(next1) { return new __Cont.class(next1); };
    this.__Cont.class = class __Cont {
      constructor(next) {
        this.next = next;
      }
      toString() { return "__Cont(" + this.next + ")"; }
    };
    this.__List = function __List(next1) { return new __List.class(next1); };
    this.__List.class = class __List {
      constructor(next) {
        this.next = next;
      }
      toString() { return "__List(" + this.next + ")"; }
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
      toString() { return "__ListWithTail(" + this.next + ", " + this.tail + ")"; }
    };
    this.__HandleBlock = function __HandleBlock(contHead1, lastHandlerCont1, next1, handler1) { return new __HandleBlock.class(contHead1, lastHandlerCont1, next1, handler1); };
    this.__HandleBlock.class = class __HandleBlock {
      constructor(contHead, lastHandlerCont, next, handler) {
        this.contHead = contHead;
        this.lastHandlerCont = lastHandlerCont;
        this.next = next;
        this.handler = handler;
      }
      toString() { return "__HandleBlock(" + this.contHead + ", " + this.lastHandlerCont + ", " + this.next + ", " + this.handler + ")"; }
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
      toString() { return "__EffectSig(" + this.next + ", " + this.tail + ", " + this.handleBlockList + ", " + this.resumed + ", " + this.handler + ", " + this.handlerFun + ")"; }
    };
    this.__Return = function __Return(value1) { return new __Return.class(value1); };
    this.__Return.class = class __Return {
      constructor(value) {
        this.value = value;
      }
      toString() { return "__Return(" + this.value + ")"; }
    };
  }
  id(x) {
    return x;
  } 
  not(x1) {
    if (x1 === false) {
      return true;
    } else {
      return false;
    }
  } 
  pipeInto(x2, f) {
    return f(x2) ?? null;
  } 
  pipeFrom(f1, x3) {
    return f1(x3) ?? null;
  } 
  andThen(f2, g) {
    return (x4) => {
      let tmp;
      tmp = f2(x4) ?? null;
      return g(tmp) ?? null;
    };
  } 
  compose(f3, g1) {
    return (x4) => {
      let tmp;
      tmp = g1(x4) ?? null;
      return f3(tmp) ?? null;
    };
  } 
  passTo(receiver, f4) {
    return (...args) => {
      return f4(receiver, ...args) ?? null;
    };
  } 
  call(receiver1, f5) {
    return (...args) => {
      return f5.call(receiver1, ...args);
    };
  } 
  pass1(f6) {
    return (...xs) => {
      return f6(xs[0]) ?? null;
    };
  } 
  pass2(f7) {
    return (...xs) => {
      return f7(xs[0], xs[1]) ?? null;
    };
  } 
  pass3(f8) {
    return (...xs) => {
      return f8(xs[0], xs[1], xs[2]) ?? null;
    };
  } 
  print(...xs) {
    let tmp;
    tmp = xs.map(String) ?? null;
    return console.log(...tmp) ?? null;
  } 
  notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw Error(tmp);
  } 
  get notImplementedError() {
    throw Error("Not implemented");
  } 
  tuple(...xs1) {
    return xs1;
  } 
  tupleSlice(xs2, i, j) {
    let tmp;
    tmp = xs2.length - j;
    return globalThis.Array.prototype.slice.call(xs2, i, tmp) ?? null;
  } 
  tupleGet(xs3, i1) {
    return globalThis.Array.prototype.at.call(xs3, i1);
  } 
  fold(f9) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3;
      i2 = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i2 < len;
        if (scrut === true) {
          tmp = rest.at(i2) ?? null;
          tmp1 = f9(init, tmp) ?? null;
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
  foldr(f10) {
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
            tmp4 = f10(tmp3, init) ?? null;
            init = tmp4;
            tmp5 = null;
            continue tmp6;
          } else {
            tmp5 = null;
          }
          break;
        }
        return f10(first, init) ?? null;
      }
    };
  } 
  stringStartsWith(string, prefix) {
    return string.startsWith(prefix) ?? null;
  } 
  stringGet(string1, i2) {
    return string1.at(i2) ?? null;
  } 
  stringDrop(string2, n) {
    return string2.slice(n) ?? null;
  } 
  checkArgs(functionName, expected, isUB, got) {
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
      tmp5 = this.fold((arg1, arg2) => {
        return arg1 + arg2;
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
      throw Error(tmp8);
    } else {
      return null;
    }
  } 
  __mkListWithTail() {
    let res, tmp;
    tmp = new this.__ListWithTail.class(null, null);
    res = tmp;
    res.tail = res;
    return res;
  } 
  __mkEffect(handler, handlerFun) {
    let res, tmp, tmp1;
    tmp = this.__mkListWithTail();
    tmp1 = new this.__EffectSig.class(null, null, tmp, false, handler, handlerFun);
    res = tmp1;
    res.tail = res;
    return res;
  } 
  __handleBlockImpl(cur, handler1) {
    let handleBlock, nxt, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = this.__List(null);
    tmp1 = new this.__HandleBlock.class(tmp, null, null, handler1);
    handleBlock = tmp1;
    tmp2 = cur.handleBlockList.append(handleBlock) ?? null;
    tmp7: while (true) {
      if (cur instanceof this.__EffectSig.class) {
        tmp3 = this.__handleEffect(cur);
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
  __handleEffect(cur1) {
    let prevBlock, scrut, scrut1, scrut2, handleBlock, origTailBlock, savedNext, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    prevBlock = cur1.handleBlockList;
    tmp6: while (true) {
      scrut = prevBlock.next;
      if (scrut instanceof this.__HandleBlock.class) {
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
    tmp2 = this.__resume(cur1, handleBlock.contHead);
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
    if (cur1 instanceof this.__EffectSig.class) {
      cur1.handleBlockList.tail.next = handleBlock;
      cur1.handleBlockList.tail = origTailBlock;
      return cur1;
    } else {
      return this.__resumeHandleBlocks(handleBlock, origTailBlock, cur1);
    }
  } 
  __resume(cur2, tail) {
    return (value) => {
      let scrut, cont, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      scrut = cur2.resumed;
      if (scrut === true) {
        throw Error("Multiple resumption");
      } else {
        tmp = null;
      }
      cur2.resumed = true;
      cont = cur2.next;
      tmp7: while (true) {
        if (cont instanceof this.__Cont.class) {
          tmp1 = cont.resume(value) ?? null;
          value = tmp1;
          if (value instanceof this.__EffectSig.class) {
            value.tail = tail;
            scrut1 = cur2.handleBlockList.next !== null;
            if (scrut1 === true) {
              value.handleBlockList.tail.next = cur2.handleBlockList.next;
              value.handleBlockList.tail = cur2.handleBlockList.tail;
              tmp2 = null;
            } else {
              tmp2 = null;
            }
            return value;
          } else {
            cont = cont.next;
            tmp3 = null;
          }
          tmp4 = tmp3;
          continue tmp7;
        } else {
          tmp4 = null;
        }
        break;
      }
      scrut2 = cur2.handleBlockList.next === null;
      if (scrut2 === true) {
        return value;
      } else {
        tmp5 = this.__resumeHandleBlocks(cur2.handleBlockList.next, cur2.handleBlockList.tail, value);
        cur2 = tmp5;
        if (cur2 instanceof this.__EffectSig.class) {
          cur2.tail = tail;
          tmp6 = null;
        } else {
          tmp6 = null;
        }
        return cur2;
      }
    };
  } 
  __resumeHandleBlocks(handleBlock, tailHandleBlock, value) {
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3;
    tmp4: while (true) {
      scrut1 = handleBlock.contHead.next;
      if (scrut1 instanceof this.__Cont.class) {
        tmp = handleBlock.contHead.next.resume(value) ?? null;
        value = tmp;
        if (value instanceof this.__EffectSig.class) {
          scrut2 = handleBlock.contHead.next !== value.tail.next;
          if (scrut2 === true) {
            handleBlock.contHead.next = handleBlock.contHead.next.next;
            tmp1 = null;
          } else {
            tmp1 = null;
          }
          value.tail.next = null;
          value.handleBlockList.tail.next = handleBlock;
          value.handleBlockList.tail = tailHandleBlock;
          return value;
        } else {
          handleBlock.contHead.next = handleBlock.contHead.next.next;
          tmp2 = null;
        }
        tmp3 = tmp2;
        continue tmp4;
      } else {
        scrut = handleBlock.next;
        if (scrut instanceof this.__HandleBlock.class) {
          handleBlock = handleBlock.next;
          tmp3 = null;
          continue tmp4;
        } else {
          return value;
        }
      }
      break;
    }
    return tmp3;
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
