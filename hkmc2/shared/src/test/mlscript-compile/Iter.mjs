import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
import Option from "./Option.mjs";
import Stack from "./Stack.mjs";
let Iterable1, Iterator1, Iter1, Result1;
Iterable1 = function Iterable(mk1) {
  return new Iterable.class(mk1);
};
Iterable1.class = class Iterable {
  #mk;
  constructor(mk) {
    this.#mk = mk;
    this[globalThis.Symbol.iterator] = this.#mk;
    runtime.Unit
  }
  toString() { return "Iterable(" + "" + ")"; }
};
Iterator1 = function Iterator(next1) {
  return new Iterator.class(next1);
};
Iterator1.class = class Iterator {
  constructor(next) {
    this.next = next;
  }
  toString() { return "Iterator(" + globalThis.Predef.render(this.next) + ")"; }
};
(class Result {
  static {
    Result1 = Result;
    this.Next = function Next(value1) {
      return new Next.class(value1);
    };
    this.Next.class = class Next {
      constructor(value) {
        this.value = value;
        this.done = false;
      }
      toString() { return "Next(" + globalThis.Predef.render(this.value) + ")"; }
    };
    const Done$class = class Done {
      constructor() {
        this.done = true;
      }
      toString() { return "Done"; }
    };
    this.Done = new Done$class;
    this.Done.class = Done$class;
  }
  static toString() { return "Result"; }
});
(class Iter {
  static {
    Iter1 = Iter;
  }
  static getIterator(something) {
    let test, prototype, tmp, tmp1;
    test = something[globalThis.Symbol.iterator];
    if (test === undefined) {
      if (something === undefined) {
        tmp = "undefined";
      } else if (something === null) {
        tmp = "null";
      } else {
        prototype = runtime.safeCall(globalThis.Reflect.getPrototypeOf(something));
        if (prototype === null) {
          tmp = "object";
        } else {
          tmp = prototype.constructor.name;
        }
      }
      tmp1 = "Not an iterable: " + tmp;
      throw globalThis.TypeError(tmp1);
    } else {
      return runtime.safeCall(test.call(something))
    }
  } 
  static adaptIterable(iterable, makeNext) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let iterator, tmp1, tmp2;
      tmp1 = Iter.getIterator(iterable);
      iterator = tmp1;
      tmp2 = runtime.safeCall(makeNext(iterator));
      return Iterator1(tmp2)
    });
    tmp = lambda;
    return Iterable1(tmp)
  } 
  static mapping(xs, op) {
    let lambda;
    lambda = (undefined, function (iterator) {
      let lambda1;
      lambda1 = (undefined, function () {
        let next, scrut, tmp, tmp1;
        tmp = runtime.safeCall(iterator.next());
        next = tmp;
        scrut = next.done;
        if (scrut === true) {
          return Result1.Done
        } else {
          tmp1 = runtime.safeCall(op(next.value));
          return Result1.Next(tmp1)
        }
      });
      return lambda1
    });
    return Iter.adaptIterable(xs, lambda)
  } 
  static flattening(xss) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let skipEmptyIterables, iterableIterator, currentIterator, firstIterableResult, scrut, tmp1, tmp2, tmp3, tmp4, lambda1;
      skipEmptyIterables = function skipEmptyIterables() {
        let nextIterableResult, nextIterator, nextResult, scrut1, scrut2;
        nextIterableResult = runtime.safeCall(iterableIterator.next());
        scrut2 = nextIterableResult.done;
        if (scrut2 === true) {
          return Option.None
        } else {
          nextIterator = Iter.getIterator(nextIterableResult.value);
          nextResult = runtime.safeCall(nextIterator.next());
          scrut1 = nextResult.done;
          if (scrut1 === true) {
            return skipEmptyIterables()
          } else {
            return Option.Some([
              nextIterator,
              nextResult.value
            ])
          }
        }
      };
      tmp1 = Iter.getIterator(xss);
      iterableIterator = tmp1;
      firstIterableResult = runtime.safeCall(iterableIterator.next());
      scrut = firstIterableResult.done;
      if (scrut === true) {
        tmp2 = Option.None;
      } else {
        tmp3 = Iter.getIterator(firstIterableResult.value);
        tmp2 = Option.Some(tmp3);
      }
      currentIterator = tmp2;
      lambda1 = (undefined, function () {
        let param0, iterator, next, scrut1, scrut2, param01, first1, first0, nextIterator, value, tmp5;
        if (currentIterator instanceof Option.None.class) {
          return Result1.Done
        } else if (currentIterator instanceof Option.Some.class) {
          param0 = currentIterator.value;
          iterator = param0;
          next = runtime.safeCall(iterator.next());
          scrut1 = next.done;
          if (scrut1 === true) {
            scrut2 = skipEmptyIterables();
            if (scrut2 instanceof Option.Some.class) {
              param01 = scrut2.value;
              if (globalThis.Array.isArray(param01) && param01.length === 2) {
                first0 = param01[0];
                first1 = param01[1];
                nextIterator = first0;
                value = first1;
                tmp5 = Option.Some(nextIterator);
                currentIterator = tmp5;
                return Result1.Next(value)
              } else {
                return Result1.Next(next.value)
              }
            } else if (scrut2 instanceof Option.None.class) {
              currentIterator = Option.None;
              return Result1.Done
            } else {
              return Result1.Next(next.value)
            }
          } else {
            return Result1.Next(next.value)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp4 = lambda1;
      return Iterator1(tmp4)
    });
    tmp = lambda;
    return Iterable1(tmp)
  } 
  static filtering(xs1, op1) {
    let lambda;
    lambda = (undefined, function (iterator) {
      let lambda1;
      lambda1 = (undefined, function () {
        let next, scrut, scrut1, scrut2, tmp, tmp1, tmp2;
        tmp = runtime.safeCall(iterator.next());
        next = tmp;
        tmp3: while (true) {
          scrut = next.done;
          if (scrut === false) {
            scrut1 = runtime.safeCall(op1(next.value));
            if (scrut1 === false) {
              tmp1 = runtime.safeCall(iterator.next());
              next = tmp1;
              tmp2 = runtime.Unit;
              continue tmp3;
            } else {
              tmp2 = runtime.Unit;
            }
          } else {
            tmp2 = runtime.Unit;
          }
          break;
        }
        scrut2 = next.done;
        if (scrut2 === true) {
          return Result1.Done
        } else {
          return Result1.Next(next.value)
        }
      });
      return lambda1
    });
    return Iter.adaptIterable(xs1, lambda)
  } 
  static taking(xs2, n) {
    let i, lambda;
    i = 0;
    lambda = (undefined, function (_) {
      let tmp;
      tmp = i + 1;
      i = tmp;
      return i <= n
    });
    return Iter.filtering(xs2, lambda)
  } 
  static zippingWithIndex(xs3) {
    let i, lambda;
    i = 0;
    lambda = (undefined, function (x) {
      let j, tmp;
      j = i;
      tmp = i + 1;
      i = tmp;
      return [
        x,
        j
      ]
    });
    return Iter.mapping(xs3, lambda)
  } 
  static foldingImpl(iterator, acc, op2) {
    let next, scrut, tmp, tmp1, tmp2, tmp3;
    tmp = runtime.safeCall(iterator.next());
    next = tmp;
    tmp4: while (true) {
      scrut = next.done;
      if (scrut === false) {
        tmp1 = runtime.safeCall(op2(acc, next.value));
        acc = tmp1;
        tmp2 = runtime.safeCall(iterator.next());
        next = tmp2;
        tmp3 = runtime.Unit;
        continue tmp4;
      } else {
        tmp3 = runtime.Unit;
      }
      break;
    }
    return acc
  } 
  static appended(xs4, ys) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let xsIterator, currentIterator, tmp1, tmp2, lambda1;
      tmp1 = Iter.getIterator(xs4);
      xsIterator = tmp1;
      currentIterator = xsIterator;
      lambda1 = (undefined, function () {
        let next, scrut, scrut1, doTemp, next1, scrut2, tmp3;
        next = runtime.safeCall(currentIterator.next());
        scrut = next.done;
        if (scrut === true) {
          scrut1 = currentIterator == xsIterator;
          if (scrut1 === true) {
            tmp3 = Iter.getIterator(ys);
            currentIterator = tmp3;
            doTemp = runtime.Unit;
            next1 = runtime.safeCall(currentIterator.next());
            scrut2 = next1.done;
            if (scrut2 === true) {
              return Result1.Done
            } else {
              return Result1.Next(next1.value)
            }
          } else {
            return Result1.Done
          }
        } else {
          return Result1.Next(next.value)
        }
      });
      tmp2 = lambda1;
      return Iterator1(tmp2)
    });
    tmp = lambda;
    return Iterable1(tmp)
  } 
  static reduced(xs5, op3) {
    let iterator1, next, scrut, tmp, tmp1, tmp2;
    tmp = Iter.getIterator(xs5);
    iterator1 = tmp;
    tmp1 = runtime.safeCall(iterator1.next());
    next = tmp1;
    scrut = next.done;
    if (scrut === true) {
      throw new globalThis.Error("Empty iterator");
    } else {
      tmp2 = runtime.Unit;
    }
    return Iter.foldingImpl(iterator1, next.value, op3)
  } 
  static folded(xs6, z, op4) {
    let iterator1, tmp;
    tmp = Iter.getIterator(xs6);
    iterator1 = tmp;
    return Iter.foldingImpl(iterator1, z, op4)
  } 
  static rightFolded(xs7, z1, op5) {
    let go, iterator1, tmp;
    go = function go() {
      let next, scrut, tmp1;
      next = runtime.safeCall(iterator1.next());
      scrut = next.done;
      if (scrut === true) {
        return z1
      } else {
        tmp1 = go();
        return runtime.safeCall(op5(next.value, tmp1))
      }
    };
    tmp = Iter.getIterator(xs7);
    iterator1 = tmp;
    return go()
  } 
  static joined(xs8, sep) {
    let iterator1, next, sep$_, scrut, tmp, tmp1, tmp2, tmp3, lambda;
    tmp = Iter.getIterator(xs8);
    iterator1 = tmp;
    tmp1 = runtime.safeCall(iterator1.next());
    next = tmp1;
    scrut = next.done;
    if (scrut === true) {
      return ""
    } else {
      tmp2 = globalThis.String(sep);
      sep$_ = tmp2;
      tmp3 = globalThis.String(next.value);
      lambda = (undefined, function (acc1, x) {
        let tmp4, tmp5;
        tmp4 = acc1 + sep;
        tmp5 = globalThis.String(x);
        return tmp4 + tmp5
      });
      return Iter.foldingImpl(iterator1, tmp3, lambda)
    }
  } 
  static firstDefined(xs9, op6) {
    let iterator1, next, result, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Iter.getIterator(xs9);
    iterator1 = tmp;
    tmp1 = runtime.safeCall(iterator1.next());
    next = tmp1;
    result = Option.None;
    tmp5: while (true) {
      scrut = next.done;
      if (scrut === false) {
        if (result instanceof Option.None.class) {
          tmp2 = runtime.safeCall(op6(next.value));
          result = tmp2;
          tmp3 = runtime.safeCall(iterator1.next());
          next = tmp3;
          tmp4 = runtime.Unit;
          continue tmp5;
        } else {
          tmp4 = runtime.Unit;
        }
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    return result
  } 
  static some(xs10, op7) {
    let iterator1, next, result, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Iter.getIterator(xs10);
    iterator1 = tmp;
    tmp1 = runtime.safeCall(iterator1.next());
    next = tmp1;
    result = Option.None;
    tmp7: while (true) {
      if (result instanceof Option.None.class) {
        scrut1 = next.done;
        if (scrut1 === true) {
          tmp2 = Option.Some(false);
          result = tmp2;
          tmp3 = runtime.Unit;
        } else {
          scrut = runtime.safeCall(op7(next.value));
          if (scrut === true) {
            tmp4 = Option.Some(true);
            result = tmp4;
            tmp3 = runtime.Unit;
          } else {
            tmp5 = runtime.safeCall(iterator1.next());
            next = tmp5;
            tmp3 = runtime.Unit;
          }
        }
        tmp6 = tmp3;
        continue tmp7;
      } else {
        tmp6 = runtime.Unit;
      }
      break;
    }
    return Option.getOrElse(result, false)
  } 
  static each(xs11, op8) {
    let iterator1, next, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Iter.getIterator(xs11);
    iterator1 = tmp;
    tmp1 = runtime.safeCall(iterator1.next());
    next = tmp1;
    tmp5: while (true) {
      scrut = next.done;
      if (scrut === false) {
        tmp2 = runtime.safeCall(op8(next.value));
        tmp3 = runtime.safeCall(iterator1.next());
        next = tmp3;
        tmp4 = runtime.Unit;
        continue tmp5;
      } else {
        tmp4 = runtime.Unit;
      }
      break;
    }
    return tmp4
  } 
  static toArray(view) {
    return runtime.safeCall(globalThis.Array.from(view))
  } 
  static fromStack(stack) {
    let lambda;
    lambda = (undefined, function () {
      let current, tmp, lambda1;
      current = stack;
      lambda1 = (undefined, function () {
        let param0, param1, head, tail;
        if (current instanceof Stack.Cons.class) {
          param0 = current.head;
          param1 = current.tail;
          head = param0;
          tail = param1;
          current = tail;
          return Result1.Next(head)
        } else if (current instanceof Stack.Nil.class) {
          return Result1.Done
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp = lambda1;
      return Iterator1(tmp)
    });
    return Iterable1(lambda)
  } 
  static toStack(xs12) {
    return Iter.rightFolded(xs12, Stack.Nil, Stack.Cons)
  }
  static toString() { return "Iter"; }
});
let Iter = Iter1; export default Iter;
