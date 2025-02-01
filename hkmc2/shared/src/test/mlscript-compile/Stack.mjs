import Predef from "./Predef.mjs";
let Stack1;
Stack1 = class Stack {
  static {
    this.Cons = function Cons(head1, tail1) { return new Cons.class(head1, tail1); };
    this.Cons.class = class Cons {
      constructor(head, tail) {
        this.head = head;
        this.tail = tail;
      }
      toString() { return "Cons(" + globalThis.Predef.render(this.head) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    const Nil$class = class Nil {
      constructor() {}
      toString() { return "Nil"; }
    };
    this.Nil = new Nil$class;
    this.Nil.class = Nil$class;
  }
  static isEmpty(xs) {
    if (xs instanceof Stack.Nil.class) {
      return true;
    } else {
      return false;
    }
  } 
  static reverseAndAppend(xs1, tail) {
    let param0, param1, h, t, tmp;
    if (xs1 instanceof Stack.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      h = param0;
      t = param1;
      tmp = Stack.Cons(h, tail);
      return Stack.reverseAndAppend(t, tmp);
    } else {
      if (xs1 instanceof Stack.Nil.class) {
        return tail;
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static reverse(xs2) {
    return Stack.reverseAndAppend(xs2, Stack.Nil);
  } 
  static fromArray(arr) {
    let ls, i, len, scrut, tmp, tmp1, tmp2, tmp3;
    ls = Stack.Nil;
    i = 0;
    len = arr.length;
    tmp4: while (true) {
      scrut = i < len;
      if (scrut === true) {
        tmp = arr.at(i) ?? null;
        tmp1 = Stack.Cons(tmp, ls);
        ls = tmp1;
        tmp2 = i + 1;
        i = tmp2;
        tmp3 = null;
        continue tmp4;
      } else {
        tmp3 = null;
      }
      break;
    }
    return ls;
  } 
  static toReverseArray(xs3) {
    let arr1, i, param0, param1, h, t, tmp, tmp1;
    arr1 = [];
    i = 0;
    tmp2: while (true) {
      if (xs3 instanceof Stack.Cons.class) {
        param0 = xs3.head;
        param1 = xs3.tail;
        h = param0;
        t = param1;
        tmp = arr1.push(h) ?? null;
        xs3 = t;
        tmp1 = null;
        continue tmp2;
      } else {
        tmp1 = null;
      }
      break;
    }
    return arr1;
  } 
  static zip(...xss) {
    let go, tmp, tmp1;
    go = function go(heads, tails) {
      return (caseScrut) => {
        let param0, param1, h, t, param01, param11, h2, t2, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
        if (caseScrut instanceof Stack.Cons.class) {
          param0 = caseScrut.head;
          param1 = caseScrut.tail;
          h = param0;
          t = param1;
          if (h instanceof Stack.Cons.class) {
            param01 = h.head;
            param11 = h.tail;
            h2 = param01;
            t2 = param11;
            tmp2 = Stack.Cons(h2, heads);
            tmp3 = Stack.Cons(t2, tails);
            tmp4 = go(tmp2, tmp3);
            return tmp4(t) ?? null;
          } else {
            if (h instanceof Stack.Nil.class) {
              tmp5 = go(heads, tails);
              return tmp5(t) ?? null;
            } else {
              throw new globalThis.Error("match error");
            }
          }
        } else {
          if (caseScrut instanceof Stack.Nil.class) {
            if (heads instanceof Stack.Nil.class) {
              if (tails instanceof Stack.Nil.class) {
                tmp6 = true;
              } else {
                tmp6 = false;
              }
              tmp7 = Predef.assert(tmp6) ?? null;
              return (tmp7 , Stack.Nil);
            } else {
              tmp8 = Stack.toReverseArray(heads);
              tmp9 = go(Stack.Nil, Stack.Nil);
              tmp10 = Stack.reverse(tails);
              tmp11 = tmp9(tmp10) ?? null;
              return Stack.Cons(tmp8, tmp11);
            }
          } else {
            throw new globalThis.Error("match error");
          }
        }
      };
    };
    tmp = go(Stack.Nil, Stack.Nil);
    tmp1 = Stack.fromArray(xss);
    return tmp(tmp1) ?? null;
  }
  static toString() { return "Stack"; }
};
null
let Stack = Stack1; export default Stack;
