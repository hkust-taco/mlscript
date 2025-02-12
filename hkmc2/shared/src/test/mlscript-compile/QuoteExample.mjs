import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
let QuoteExample1;
QuoteExample1 = class QuoteExample {
  static {}
  static foo() {
    let tmp, x, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp = globalThis.Predef.term.freshName("x");
    x = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = new globalThis.Predef.term.Ref(x);
    tmp2 = new globalThis.Predef.term.Symbol("+");
    tmp3 = new globalThis.Predef.term.Lit(1);
    tmp4 = new globalThis.Predef.term.Lit(1);
    tmp5 = new globalThis.Predef.term.Ref(tmp2);
    tmp6 = new globalThis.Predef.term.Tup([
      tmp3,
      tmp4
    ]);
    tmp7 = new globalThis.Predef.term.App(tmp5, tmp6);
    tmp8 = new globalThis.Predef.term.Lam([
      x
    ], tmp1);
    tmp9 = new globalThis.Predef.term.Tup([
      tmp7
    ]);
    return new globalThis.Predef.term.App(tmp8, tmp9)
  } 
  static inc() {
    let tmp, x, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = globalThis.Predef.term.freshName("x");
    x = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = new globalThis.Predef.term.Symbol("+");
    tmp2 = new globalThis.Predef.term.Ref(x);
    tmp3 = new globalThis.Predef.term.Lit(1);
    tmp4 = new globalThis.Predef.term.Ref(tmp1);
    tmp5 = new globalThis.Predef.term.Tup([
      tmp2,
      tmp3
    ]);
    tmp6 = new globalThis.Predef.term.App(tmp4, tmp5);
    return new globalThis.Predef.term.Lam([
      x
    ], tmp6)
  } 
  static power(x) {
    return (caseScrut) => {
      let n, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (caseScrut === 0) {
        return new globalThis.Predef.term.Lit(1.0)
      } else {
        n = caseScrut;
        tmp = new globalThis.Predef.term.Symbol("*");
        tmp1 = x;
        tmp2 = QuoteExample.power(x);
        tmp3 = n - 1;
        tmp4 = runtime.safeCall(tmp2(tmp3));
        tmp5 = new globalThis.Predef.term.Ref(tmp);
        tmp6 = new globalThis.Predef.term.Tup([
          tmp1,
          tmp4
        ]);
        return new globalThis.Predef.term.App(tmp5, tmp6)
      }
    }
  } 
  static bind(rhs, k) {
    let tmp, x1, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = globalThis.Predef.term.freshName("x");
    x1 = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = rhs;
    tmp2 = new globalThis.Predef.term.Ref(x1);
    tmp3 = runtime.safeCall(k(tmp2));
    tmp4 = new globalThis.Predef.term.LetDecl(x1);
    tmp5 = new globalThis.Predef.term.DefineVar(x1, tmp1);
    return new globalThis.Predef.term.Blk([
      tmp4,
      tmp5
    ], tmp3)
  } 
  static body(x1, y) {
    return (caseScrut) => {
      let n, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      if (caseScrut === 0) {
        return x1
      } else {
        if (caseScrut === 1) {
          return y
        } else {
          n = caseScrut;
          tmp = new globalThis.Predef.term.Symbol("+");
          tmp1 = x1;
          tmp2 = y;
          tmp3 = new globalThis.Predef.term.Ref(tmp);
          tmp4 = new globalThis.Predef.term.Tup([
            tmp1,
            tmp2
          ]);
          tmp5 = new globalThis.Predef.term.App(tmp3, tmp4);
          return QuoteExample.bind(tmp5, (z) => {
            let tmp6, tmp7;
            tmp6 = QuoteExample.body(y, z);
            tmp7 = n - 1;
            return runtime.safeCall(tmp6(tmp7))
          })
        }
      }
    }
  } 
  static gib(n) {
    let tmp, x2, tmp1, y1, tmp2, tmp3, tmp4, tmp5;
    tmp = globalThis.Predef.term.freshName("x");
    x2 = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = globalThis.Predef.term.freshName("y");
    y1 = new globalThis.Predef.term.Symbol(tmp1);
    tmp2 = new globalThis.Predef.term.Ref(x2);
    tmp3 = new globalThis.Predef.term.Ref(y1);
    tmp4 = QuoteExample.body(tmp2, tmp3);
    tmp5 = runtime.safeCall(tmp4(n));
    return new globalThis.Predef.term.Lam([
      x2,
      y1
    ], tmp5)
  } 
  static safeDiv() {
    let tmp, x2, tmp1, y1, tmp2, d, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
    tmp = globalThis.Predef.term.freshName("x");
    x2 = new globalThis.Predef.term.Symbol(tmp);
    tmp1 = globalThis.Predef.term.freshName("y");
    y1 = new globalThis.Predef.term.Symbol(tmp1);
    tmp2 = globalThis.Predef.term.freshName("d");
    d = new globalThis.Predef.term.Symbol(tmp2);
    tmp3 = globalThis.Predef.term.freshName("scrut");
    tmp4 = new globalThis.Predef.term.Symbol(tmp3);
    tmp5 = new globalThis.Predef.term.Symbol("==");
    tmp6 = new globalThis.Predef.term.Ref(y1);
    tmp7 = new globalThis.Predef.term.Lit(0.0);
    tmp8 = new globalThis.Predef.term.Ref(tmp5);
    tmp9 = new globalThis.Predef.term.Tup([
      tmp6,
      tmp7
    ]);
    tmp10 = new globalThis.Predef.term.App(tmp8, tmp9);
    tmp11 = new globalThis.Predef.term.Ref(tmp4);
    tmp12 = new globalThis.Predef.term.LitPattern(true);
    tmp13 = new globalThis.Predef.term.Ref(d);
    tmp14 = new globalThis.Predef.term.Else(tmp13);
    tmp15 = new globalThis.Predef.term.Branch(tmp11, tmp12, tmp14);
    tmp16 = new globalThis.Predef.term.Symbol("/");
    tmp17 = new globalThis.Predef.term.Ref(x2);
    tmp18 = new globalThis.Predef.term.Ref(y1);
    tmp19 = new globalThis.Predef.term.Ref(tmp16);
    tmp20 = new globalThis.Predef.term.Tup([
      tmp17,
      tmp18
    ]);
    tmp21 = new globalThis.Predef.term.App(tmp19, tmp20);
    tmp22 = new globalThis.Predef.term.Else(tmp21);
    tmp23 = new globalThis.Predef.term.Cons(tmp15, tmp22);
    tmp24 = new globalThis.Predef.term.Let(tmp4, tmp10, tmp23);
    tmp25 = new globalThis.Predef.term.IfLike(globalThis.Predef.term.KeywordIf, tmp24);
    return new globalThis.Predef.term.Lam([
      x2,
      y1,
      d
    ], tmp25)
  }
  static toString() { return "QuoteExample"; }
};
let QuoteExample = QuoteExample1; export default QuoteExample;
