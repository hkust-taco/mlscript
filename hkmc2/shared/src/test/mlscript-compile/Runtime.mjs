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
    this.Cont = function Cont(next1, completed1) { return new Cont.class(next1, completed1); };
    this.Cont.class = class Cont {
      constructor(next, completed) {
        this.next = next;
        this.completed = completed;
      }
      toString() { return "Cont(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.completed) + ")"; }
    };
    this.TailList = function TailList(next1) { return new TailList.class(next1); };
    this.TailList.class = class TailList {
      constructor(next) {
        this.next = next;
      }
      toString() { return "TailList(" + globalThis.Predef.render(this.next) + ")"; }
    };
    this.ListWithTail = function ListWithTail(next1, tail1) { return new ListWithTail.class(next1, tail1); };
    this.ListWithTail.class = class ListWithTail {
      constructor(next, tail) {
        this.next = next;
        this.tail = tail;
      }
      append(elem) {
        this.tail.next = elem;
        this.tail = elem;
        return runtime.Unit
      }
      toString() { return "ListWithTail(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    this.HandleBlock = function HandleBlock(contHead1, lastHandlerCont1, next1, handler1) { return new HandleBlock.class(contHead1, lastHandlerCont1, next1, handler1); };
    this.HandleBlock.class = class HandleBlock {
      constructor(contHead, lastHandlerCont, next, handler) {
        this.contHead = contHead;
        this.lastHandlerCont = lastHandlerCont;
        this.next = next;
        this.handler = handler;
      }
      toString() { return "HandleBlock(" + globalThis.Predef.render(this.contHead) + ", " + globalThis.Predef.render(this.lastHandlerCont) + ", " + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.handler) + ")"; }
    };
    this.EffectSig = function EffectSig(next1, tail1, handleBlockList1, resumed1, handler1, handlerFun1) { return new EffectSig.class(next1, tail1, handleBlockList1, resumed1, handler1, handlerFun1); };
    this.EffectSig.class = class EffectSig {
      constructor(next, tail, handleBlockList, resumed, handler, handlerFun) {
        this.next = next;
        this.tail = tail;
        this.handleBlockList = handleBlockList;
        this.resumed = resumed;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return "EffectSig(" + globalThis.Predef.render(this.next) + ", " + globalThis.Predef.render(this.tail) + ", " + globalThis.Predef.render(this.handleBlockList) + ", " + globalThis.Predef.render(this.resumed) + ", " + globalThis.Predef.render(this.handler) + ", " + globalThis.Predef.render(this.handlerFun) + ")"; }
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
  static mkListWithTail() {
    let res, tmp;
    tmp = new Runtime.ListWithTail.class(null, null);
    res = tmp;
    res.tail = res;
    return res
  } 
  static showContChain(cont, hl, vis, reps) {
    let scrut, result, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    if (cont instanceof Runtime.Cont.class) {
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
      tmp11 = Runtime.showContChain(cont.next, hl, vis, reps);
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
  static debugEff(eff) {
    let showHandlerChain, scrut, vis1, hl1, cur, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    if (eff instanceof Runtime.EffectSig.class) {
      showHandlerChain = function showHandlerChain(hndl) {
        let scrut2, tailStr, scrut3, handlerTailStr, scrut4, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
        if (hndl instanceof Runtime.HandleBlock.class) {
          scrut3 = hndl.contHead === eff.tail;
          if (scrut3 === true) {
            tmp15 = ", tail";
          } else {
            tmp15 = "";
          }
          tailStr = tmp15;
          scrut4 = hndl === eff.handleBlockList.tail;
          if (scrut4 === true) {
            tmp16 = ", handler-tail";
          } else {
            tmp16 = "";
          }
          handlerTailStr = tmp16;
          tmp17 = new globalThis.Set([
            hndl.lastHandlerCont
          ]);
          tmp18 = hl1.set("last-handler-cont", tmp17);
          tmp19 = hndl.handler.constructor.name + tailStr;
          tmp20 = tmp19 + handlerTailStr;
          tmp21 = tmp20 + " -> ";
          tmp22 = Runtime.showContChain(hndl.contHead.next, hl1, vis1, 0);
          return tmp21 + tmp22
        } else {
          scrut2 = hndl === null;
          if (scrut2 === true) {
            return "(null)"
          } else {
            return "(NOT HANDLE BLOCK)"
          }
        }
      };
      tmp = runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      tmp1 = globalThis.console.log("resumed: ", eff.resumed);
      tmp2 = globalThis.console.log("handler: ", eff.handler.constructor.name);
      tmp3 = globalThis.console.log("handlerFun: ", eff.handlerFun);
      scrut = eff.tail === eff;
      if (scrut === true) {
        tmp4 = runtime.safeCall(globalThis.console.log("<tail is self>"));
      } else {
        tmp4 = runtime.Unit;
      }
      tmp5 = new globalThis.Set();
      vis1 = tmp5;
      tmp6 = new globalThis.Map();
      hl1 = tmp6;
      tmp7 = new globalThis.Set([
        eff.tail
      ]);
      tmp8 = hl1.set("tail", tmp7);
      tmp9 = Runtime.showContChain(eff.next, hl1, vis1, 0);
      tmp10 = runtime.safeCall(globalThis.console.log(tmp9));
      cur = eff.handleBlockList.next;
      tmp15: while (true) {
        scrut1 = cur !== null;
        if (scrut1 === true) {
          tmp11 = showHandlerChain(cur);
          tmp12 = runtime.safeCall(globalThis.console.log(tmp11));
          cur = cur.next;
          tmp13 = runtime.Unit;
          continue tmp15;
        } else {
          tmp13 = runtime.Unit;
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    } else {
      tmp14 = runtime.safeCall(globalThis.console.log("Not an effect:"));
      return runtime.safeCall(globalThis.console.log(eff))
    }
  } 
  static mkEffect(handler, handlerFun) {
    let res, tmp, tmp1;
    tmp = Runtime.mkListWithTail();
    tmp1 = new Runtime.EffectSig.class(null, null, tmp, false, handler, handlerFun);
    res = tmp1;
    res.tail = res;
    return res
  } 
  static handleBlockImpl(cur, handler1) {
    let handleBlock, nxt, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Runtime.TailList(null);
    tmp1 = new Runtime.HandleBlock.class(tmp, null, null, handler1);
    handleBlock = tmp1;
    tmp2 = runtime.safeCall(cur.handleBlockList.append(handleBlock));
    tmp7: while (true) {
      if (cur instanceof Runtime.EffectSig.class) {
        tmp3 = Runtime.handleEffect(cur);
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
  static handleEffect(cur1) {
    let prevBlock, scrut, scrut1, scrut2, handleBlock, origTailBlock, savedNext, tmp, tmp1, tmp2, tmp3;
    prevBlock = cur1.handleBlockList;
    tmp4: while (true) {
      scrut = prevBlock.next;
      if (scrut instanceof Runtime.HandleBlock.class) {
        scrut1 = prevBlock.next.handler !== cur1.handler;
        if (scrut1 === true) {
          prevBlock = prevBlock.next;
          tmp = runtime.Unit;
          continue tmp4;
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
    tmp2 = Runtime.resume(cur1);
    tmp3 = cur1.handlerFun(tmp2, handleBlock);
    cur1 = tmp3;
    if (cur1 instanceof Runtime.EffectSig.class) {
      cur1.handleBlockList.tail.next = handleBlock;
      cur1.handleBlockList.tail = origTailBlock;
      return cur1
    } else {
      return Runtime.resumeHandleBlocks(handleBlock, origTailBlock, cur1)
    }
  } 
  static resume(cur2) {
    return (value) => {
      let scrut, cont1, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      scrut = cur2.resumed;
      if (scrut === true) {
        throw globalThis.Error("Multiple resumption");
      } else {
        tmp = runtime.Unit;
      }
      cur2.resumed = true;
      cont1 = cur2.next;
      tmp6: while (true) {
        if (cont1 instanceof Runtime.Cont.class) {
          tmp1 = runtime.safeCall(cont1.resume(value));
          value = tmp1;
          if (value instanceof Runtime.EffectSig.class) {
            scrut1 = cont1.completed;
            if (scrut1 === true) {
              value.tail.next = cont1.next;
              tmp2 = runtime.Unit;
            } else {
              value.tail.next = cont1;
              tmp2 = runtime.Unit;
            }
            scrut2 = cur2.handleBlockList.next !== null;
            if (scrut2 === true) {
              value.handleBlockList.tail.next = cur2.handleBlockList.next;
              value.handleBlockList.tail = cur2.handleBlockList.tail;
              tmp3 = runtime.Unit;
            } else {
              tmp3 = runtime.Unit;
            }
            return value
          } else {
            cont1 = cont1.next;
            tmp4 = runtime.Unit;
          }
          tmp5 = tmp4;
          continue tmp6;
        } else {
          tmp5 = runtime.Unit;
        }
        break;
      }
      scrut3 = cur2.handleBlockList.next === null;
      if (scrut3 === true) {
        return value
      } else {
        return Runtime.resumeHandleBlocks(cur2.handleBlockList.next, cur2.handleBlockList.tail, value)
      }
    }
  } 
  static resumeHandleBlocks(handleBlock, tailHandleBlock, value) {
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3;
    tmp4: while (true) {
      scrut1 = handleBlock.contHead.next;
      if (scrut1 instanceof Runtime.Cont.class) {
        tmp = runtime.safeCall(handleBlock.contHead.next.resume(value));
        value = tmp;
        scrut2 = handleBlock.contHead.next.completed;
        if (scrut2 === true) {
          handleBlock.contHead.next = handleBlock.contHead.next.next;
          tmp1 = runtime.Unit;
        } else {
          tmp1 = runtime.Unit;
        }
        if (value instanceof Runtime.EffectSig.class) {
          value.handleBlockList.tail.next = handleBlock;
          value.handleBlockList.tail = tailHandleBlock;
          return value
        } else {
          tmp2 = runtime.Unit;
        }
        tmp3 = tmp2;
        continue tmp4;
      } else {
        scrut = handleBlock.next;
        if (scrut instanceof Runtime.HandleBlock.class) {
          handleBlock = handleBlock.next;
          tmp3 = runtime.Unit;
          continue tmp4;
        } else {
          return value
        }
      }
      break;
    }
    return tmp3
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
