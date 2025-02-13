import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
let QuoteExample1;
QuoteExample1 = class QuoteExample {
  static {}
  static foo() {
    let tmp, tmp1, tmp2, tmp3;
    tmp = new runtime.term.Lit(1);
    tmp1 = new runtime.term.Lit(1);
    tmp2 = new runtime.term.Builtin("+");
    tmp3 = new runtime.term.Tup([
      tmp,
      tmp1
    ]);
    return new runtime.term.App(tmp2, tmp3)
  } 
  static inc() {
    let tmp, x, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.term.freshName("x");
    x = new runtime.term.Symbol(tmp);
    tmp1 = new runtime.term.Ref(x);
    tmp2 = new runtime.term.Lit(1);
    tmp3 = new runtime.term.Builtin("+");
    tmp4 = new runtime.term.Tup([
      tmp1,
      tmp2
    ]);
    tmp5 = new runtime.term.App(tmp3, tmp4);
    return new runtime.term.Lam([
      x
    ], tmp5)
  } 
  static power(x) {
    return (caseScrut) => {
      let n, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      if (caseScrut === 0) {
        return new runtime.term.Lit(1.0)
      } else {
        n = caseScrut;
        tmp = x;
        tmp1 = QuoteExample.power(x);
        tmp2 = n - 1;
        tmp3 = runtime.safeCall(tmp1(tmp2));
        tmp4 = new runtime.term.Builtin("*");
        tmp5 = new runtime.term.Tup([
          tmp,
          tmp3
        ]);
        return new runtime.term.App(tmp4, tmp5)
      }
    }
  } 
  static bind(rhs, k) {
    let tmp, x1, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.term.freshName("x");
    x1 = new runtime.term.Symbol(tmp);
    tmp1 = rhs;
    tmp2 = new runtime.term.Ref(x1);
    tmp3 = runtime.safeCall(k(tmp2));
    tmp4 = new runtime.term.LetDecl(x1);
    tmp5 = new runtime.term.DefineVar(x1, tmp1);
    return new runtime.term.Blk([
      tmp4,
      tmp5
    ], tmp3)
  } 
  static body(x1, y) {
    return (caseScrut) => {
      let n, tmp, tmp1, tmp2, tmp3, tmp4;
      if (caseScrut === 0) {
        return x1
      } else if (caseScrut === 1) {
        return y
      } else {
        n = caseScrut;
        tmp = x1;
        tmp1 = y;
        tmp2 = new runtime.term.Builtin("+");
        tmp3 = new runtime.term.Tup([
          tmp,
          tmp1
        ]);
        tmp4 = new runtime.term.App(tmp2, tmp3);
        return QuoteExample.bind(tmp4, (z) => {
          let tmp5, tmp6;
          tmp5 = QuoteExample.body(y, z);
          tmp6 = n - 1;
          return runtime.safeCall(tmp5(tmp6))
        })
      }
    }
  } 
  static gib(n) {
    let tmp, x2, tmp1, y1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.term.freshName("x");
    x2 = new runtime.term.Symbol(tmp);
    tmp1 = runtime.term.freshName("y");
    y1 = new runtime.term.Symbol(tmp1);
    tmp2 = new runtime.term.Ref(x2);
    tmp3 = new runtime.term.Ref(y1);
    tmp4 = QuoteExample.body(tmp2, tmp3);
    tmp5 = runtime.safeCall(tmp4(n));
    return new runtime.term.Lam([
      x2,
      y1
    ], tmp5)
  } 
  static safeDiv() {
    let tmp, x2, tmp1, y1, tmp2, d, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
    tmp = runtime.term.freshName("x");
    x2 = new runtime.term.Symbol(tmp);
    tmp1 = runtime.term.freshName("y");
    y1 = new runtime.term.Symbol(tmp1);
    tmp2 = runtime.term.freshName("d");
    d = new runtime.term.Symbol(tmp2);
    tmp3 = runtime.term.freshName("scrut");
    tmp4 = new runtime.term.Symbol(tmp3);
    tmp5 = new runtime.term.Ref(y1);
    tmp6 = new runtime.term.Lit(0.0);
    tmp7 = new runtime.term.Builtin("==");
    tmp8 = new runtime.term.Tup([
      tmp5,
      tmp6
    ]);
    tmp9 = new runtime.term.App(tmp7, tmp8);
    tmp10 = new runtime.term.Ref(tmp4);
    tmp11 = new runtime.term.LitPattern(true);
    tmp12 = new runtime.term.Ref(d);
    tmp13 = new runtime.term.Else(tmp12);
    tmp14 = new runtime.term.Branch(tmp10, tmp11, tmp13);
    tmp15 = new runtime.term.Ref(x2);
    tmp16 = new runtime.term.Ref(y1);
    tmp17 = new runtime.term.Builtin("/");
    tmp18 = new runtime.term.Tup([
      tmp15,
      tmp16
    ]);
    tmp19 = new runtime.term.App(tmp17, tmp18);
    tmp20 = new runtime.term.Else(tmp19);
    tmp21 = new runtime.term.Cons(tmp14, tmp20);
    tmp22 = new runtime.term.Let(tmp4, tmp9, tmp21);
    tmp23 = new runtime.term.IfLike(runtime.term.KeywordIf, tmp22);
    return new runtime.term.Lam([
      x2,
      y1,
      d
    ], tmp23)
  }
  static toString() { return "QuoteExample"; }
};
let QuoteExample = QuoteExample1; export default QuoteExample;
