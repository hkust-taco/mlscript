import Predef from "./Predef.mjs";
let Stack1;
const Stack$class = class Stack {
  constructor() {
    this.Cons = function Cons(head1, tail1) { return new Cons.class(head1, tail1); };
    this.Cons.class = class Cons {
      constructor(head, tail) {
        this.head = head;
        this.tail = tail;
      }
      toString() { return "Cons(" + this.head + ", " + this.tail + ")"; }
    };
    const Nil$class = class Nil {
      constructor() {}
      toString() { return "Nil"; }
    };
    this.Nil = new Nil$class;
    this.Nil.class = Nil$class;
  }
  isEmpty(xs) {
    if (xs instanceof this.Nil.class) {
      return true;
    } else {
      return false;
    }
  } 
  reverseAndAppend(xs1, tail) {
    let param0, param1, h, t, tmp;
    if (xs1 instanceof this.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      h = param0;
      t = param1;
      tmp = this.Cons(h, tail);
      return this.reverseAndAppend(t, tmp);
    } else {
      if (xs1 instanceof this.Nil.class) {
        return tail;
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  reverse(xs2) {
    return this.reverseAndAppend(xs2, this.Nil);
  } 
  fromArray(arr) {
    let ls, i, len, scrut, tmp, tmp1, tmp2, tmp3;
    ls = this.Nil;
    i = 0;
    len = arr.length;
    tmp4: while (true) {
      scrut = i < len;
      if (scrut === true) {
        tmp = arr.at(i) ?? null;
        tmp1 = this.Cons(tmp, ls);
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
  toReverseArray(xs3) {
    let arr1, i, param0, param1, h, t, tmp, tmp1;
    arr1 = [];
    i = 0;
    tmp2: while (true) {
      if (xs3 instanceof this.Cons.class) {
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
  zip(...xss) {
    let go, tmp, tmp1;
    const this$Stack = this;
    go = function go(heads, tails) {
      return (caseScrut) => {
        let param0, param1, h, t, param01, param11, h2, t2, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
        if (caseScrut instanceof this$Stack.Cons.class) {
          param0 = caseScrut.head;
          param1 = caseScrut.tail;
          h = param0;
          t = param1;
          if (h instanceof this$Stack.Cons.class) {
            param01 = h.head;
            param11 = h.tail;
            h2 = param01;
            t2 = param11;
            tmp2 = this$Stack.Cons(h2, heads);
            tmp3 = this$Stack.Cons(t2, tails);
            tmp4 = go(tmp2, tmp3);
            return tmp4(t) ?? null;
          } else {
            if (h instanceof this$Stack.Nil.class) {
              tmp5 = go(heads, tails);
              return tmp5(t) ?? null;
            } else {
              throw new globalThis.Error("match error");
            }
          }
        } else {
          if (caseScrut instanceof this$Stack.Nil.class) {
            if (heads instanceof this$Stack.Nil.class) {
              if (tails instanceof this$Stack.Nil.class) {
                tmp6 = true;
              } else {
                tmp6 = false;
              }
              tmp7 = Predef.assert(tmp6) ?? null;
              return (tmp7 , this$Stack.Nil);
            } else {
              tmp8 = this$Stack.toReverseArray(heads);
              tmp9 = go(this$Stack.Nil, this$Stack.Nil);
              tmp10 = this$Stack.reverse(tails);
              tmp11 = tmp9(tmp10) ?? null;
              return this$Stack.Cons(tmp8, tmp11);
            }
          } else {
            throw new globalThis.Error("match error");
          }
        }
      };
    };
    tmp = go(this.Nil, this.Nil);
    tmp1 = this.fromArray(xss);
    return tmp(tmp1) ?? null;
  }
  toString() { return "Stack"; }
}; Stack1 = new Stack$class;
Stack1.class = Stack$class;
null
let Stack = Stack1; export default Stack;
