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
        return runtime.Unit
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
    this.__StackDelay = class __StackDelay {
      constructor() {}
      toString() { return "__StackDelay"; }
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
  static __mkListWithTail() {
    let res, tmp;
    tmp = new Runtime.__ListWithTail.class(null, null);
    res = tmp;
    res.tail = res;
    return res
  } 
  static __appendInCont(eff, cont) {
    let scrut, scrut1, tmp, tmp1;
    scrut = eff.tail;
    if (scrut instanceof Runtime.__TailList.class) {
      scrut1 = cont.next !== null;
      if (scrut1 === true) {
        throw globalThis.Error("unexpected handler continuation");
      } else {
        tmp = runtime.Unit;
      }
      cont.next = eff.tail.next;
      eff.tail.next = cont;
      tmp1 = runtime.Unit;
    } else {
      eff.tail.next = cont;
      tmp1 = runtime.Unit;
    }
    return eff
  } 
  static __mkEffect(handler, handlerFun) {
    let res, tmp, tmp1;
    tmp = Runtime.__mkListWithTail();
    tmp1 = new Runtime.__EffectSig.class(null, null, tmp, false, handler, handlerFun);
    res = tmp1;
    res.tail = res;
    return res
  } 
  static __handleBlockImpl(cur, handler1) {
    let handleBlock, nxt, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Runtime.__TailList(null);
    tmp1 = new Runtime.__HandleBlock.class(tmp, null, null, handler1);
    handleBlock = tmp1;
    tmp2 = runtime.safeCall(cur.handleBlockList.append(handleBlock));
    tmp7: while (true) {
      if (cur instanceof Runtime.__EffectSig.class) {
        tmp3 = Runtime.__handleEffect(cur);
        nxt = tmp3;
        scrut = cur === nxt;
        if (scrut === true) {
          scrut1 = handleBlock.lastHandlerCont === null;
          if (scrut1 === true) {
            cur.tail = handleBlock.contHead;
            tmp4 = runtime.Unit;
          } else {
            cur.tail = handleBlock.lastHandlerCont;
            tmp4 = runtime.Unit;
          }
          return cur
        } else {
          cur = nxt;
          tmp5 = runtime.Unit;
        }
        tmp6 = tmp5;
        continue tmp7;
      } else {
        return cur
      }
      break;
    }
    return tmp6
  } 
  static __handleEffect(cur1) {
    let prevBlock, scrut, scrut1, scrut2, handleBlock, origTailBlock, savedNext, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    prevBlock = cur1.handleBlockList;
    tmp6: while (true) {
      scrut = prevBlock.next;
      if (scrut instanceof Runtime.__HandleBlock.class) {
        scrut1 = prevBlock.next.handler !== cur1.handler;
        if (scrut1 === true) {
          prevBlock = prevBlock.next;
          tmp = runtime.Unit;
          continue tmp6;
        } else {
          tmp = runtime.Unit;
        }
      } else {
        tmp = runtime.Unit;
      }
      break;
    }
    scrut2 = prevBlock.next === null;
    if (scrut2 === true) {
      return cur1
    } else {
      tmp1 = runtime.Unit;
    }
    handleBlock = prevBlock.next;
    origTailBlock = cur1.handleBlockList.tail;
    prevBlock.next = null;
    cur1.handleBlockList.tail = prevBlock;
    savedNext = handleBlock.contHead.next;
    tmp2 = Runtime.__resume(cur1, handleBlock.contHead);
    tmp3 = runtime.safeCall(cur1.handlerFun(tmp2));
    cur1 = tmp3;
    scrut3 = savedNext !== handleBlock.contHead.next;
    if (scrut3 === true) {
      handleBlock.contHead.next.next = savedNext;
      scrut4 = handleBlock.lastHandlerCont === null;
      if (scrut4 === true) {
        handleBlock.lastHandlerCont = handleBlock.contHead.next;
        tmp4 = runtime.Unit;
      } else {
        tmp4 = runtime.Unit;
      }
      tmp5 = tmp4;
    } else {
      tmp5 = runtime.Unit;
    }
    if (cur1 instanceof Runtime.__EffectSig.class) {
      cur1.handleBlockList.tail.next = handleBlock;
      cur1.handleBlockList.tail = origTailBlock;
      return cur1
    } else {
      return Runtime.__resumeHandleBlocks(handleBlock, origTailBlock, cur1)
    }
  } 
  static __resume(cur2, tail) {
    return (value) => {
      let scrut, cont1, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
      scrut = cur2.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption");
      } else {
        tmp = runtime.Unit;
      }
      cur2.resumed = true;
      cont1 = cur2.next;
      tmp10: while (true) {
        if (cont1 instanceof Runtime.__Cont.class) {
          tmp1 = runtime.safeCall(cont1.resume(value));
          value = tmp1;
          if (value instanceof Runtime.__EffectSig.class) {
            scrut1 = value.tail.next !== cont1;
            if (scrut1 === true) {
              scrut2 = cont1.next !== null;
              if (scrut2 === true) {
                scrut3 = value.tail.next !== null;
                if (scrut3 === true) {
                  throw globalThis.Error("Internal Error: unexpected continuation");
                } else {
                  tmp2 = runtime.Unit;
                }
              } else {
                tmp2 = runtime.Unit;
              }
              tmp3 = tmp2;
            } else {
              tmp3 = runtime.Unit;
            }
            scrut4 = value.tail.next === null;
            if (scrut4 === true) {
              value.tail.next = cont1.next;
              tmp4 = runtime.Unit;
            } else {
              tmp4 = runtime.Unit;
            }
            value.tail = tail;
            scrut5 = cur2.handleBlockList.next !== null;
            if (scrut5 === true) {
              value.handleBlockList.tail.next = cur2.handleBlockList.next;
              value.handleBlockList.tail = cur2.handleBlockList.tail;
              tmp5 = runtime.Unit;
            } else {
              tmp5 = runtime.Unit;
            }
            return value
          } else {
            cont1 = cont1.next;
            tmp6 = runtime.Unit;
          }
          tmp7 = tmp6;
          continue tmp10;
        } else {
          tmp7 = runtime.Unit;
        }
        break;
      }
      scrut6 = cur2.handleBlockList.next === null;
      if (scrut6 === true) {
        return value
      } else {
        tmp8 = Runtime.__resumeHandleBlocks(cur2.handleBlockList.next, cur2.handleBlockList.tail, value);
        cur2 = tmp8;
        if (cur2 instanceof Runtime.__EffectSig.class) {
          cur2.tail = tail;
          tmp9 = runtime.Unit;
        } else {
          tmp9 = runtime.Unit;
        }
        return cur2
      }
    }
  } 
  static __resumeHandleBlocks(handleBlock, tailHandleBlock, value) {
    let scrut, scrut1, scrut2, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp5: while (true) {
      scrut1 = handleBlock.contHead.next;
      if (scrut1 instanceof Runtime.__Cont.class) {
        tmp = runtime.safeCall(handleBlock.contHead.next.resume(value));
        value = tmp;
        if (value instanceof Runtime.__EffectSig.class) {
          scrut2 = value.tail.next !== handleBlock.contHead.next;
          if (scrut2 === true) {
            scrut3 = value.tail.next !== null;
            if (scrut3 === true) {
              throw globalThis.Error("Internal Error: unexpected continuation during handle block resumption");
            } else {
              tmp1 = runtime.Unit;
            }
          } else {
            tmp1 = runtime.Unit;
          }
          scrut4 = value.tail.next !== handleBlock.contHead.next;
          if (scrut4 === true) {
            handleBlock.contHead.next = handleBlock.contHead.next.next;
            tmp2 = runtime.Unit;
          } else {
            tmp2 = runtime.Unit;
          }
          value.tail.next = null;
          value.handleBlockList.tail.next = handleBlock;
          value.handleBlockList.tail = tailHandleBlock;
          return value
        } else {
          handleBlock.contHead.next = handleBlock.contHead.next.next;
          tmp3 = runtime.Unit;
        }
        tmp4 = tmp3;
        continue tmp5;
      } else {
        scrut = handleBlock.next;
        if (scrut instanceof Runtime.__HandleBlock.class) {
          handleBlock = handleBlock.next;
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
    tmp = Runtime.__stackDepth - Runtime.__stackOffset;
    tmp1 = tmp >= Runtime.__stackLimit;
    tmp2 = Runtime.__stackHandler !== null;
    scrut = tmp1 && tmp2;
    if (scrut === true) {
      return runtime.safeCall(Runtime.__stackHandler.perform())
    } else {
      return runtime.Unit
    }
  } 
  static resetDepth(tmp, curDepth) {
    let scrut, tmp1;
    Runtime.__stackDepth = curDepth;
    scrut = curDepth < Runtime.__stackOffset;
    if (scrut === true) {
      Runtime.__stackOffset = curDepth;
      tmp1 = runtime.Unit;
    } else {
      tmp1 = runtime.Unit;
    }
    return tmp
  }
  static toString() { return "Runtime"; }
};
let Runtime = Runtime1; export default Runtime;
