import runtime from "./Runtime.mjs";
import Term from "./Term.mjs";
import Predef from "./Predef.mjs";
let QuoteExample1;
(class QuoteExample {
  static {
    QuoteExample1 = QuoteExample;
  }
  static foo() {
    let tmp, tmp1, tmp2, tmp3;
    tmp = new Term.Lit(1);
    tmp1 = new Term.Lit(1);
    tmp2 = new Term.Builtin("+");
    tmp3 = new Term.Tup([
      tmp,
      tmp1
    ]);
    return new Term.App(tmp2, tmp3)
  } 
  static inc() {
    let x, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = Term.freshName("x");
    tmp1 = new Term.Symbol(tmp);
    x = new Term.Ref(tmp1);
    tmp2 = x;
    tmp3 = new Term.Lit(1);
    tmp4 = new Term.Builtin("+");
    tmp5 = new Term.Tup([
      tmp2,
      tmp3
    ]);
    tmp6 = new Term.App(tmp4, tmp5);
    return new Term.Lam([
      tmp1
    ], tmp6)
  } 
  static power(x) {
    let lambda;
    lambda = (undefined, function (caseScrut) {
      let n, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      if (caseScrut === 0) {
        return new Term.Lit(1.0)
      } else {
        n = caseScrut;
        tmp = x;
        tmp1 = QuoteExample.power(x);
        tmp2 = n - 1;
        tmp3 = runtime.safeCall(tmp1(tmp2));
        tmp4 = new Term.Builtin("*");
        tmp5 = new Term.Tup([
          tmp,
          tmp3
        ]);
        return new Term.App(tmp4, tmp5)
      }
    });
    return lambda
  } 
  static bind(rhs, k) {
    let x1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = Term.freshName("x");
    tmp1 = new Term.Symbol(tmp);
    x1 = new Term.Ref(tmp1);
    tmp2 = rhs;
    tmp3 = runtime.safeCall(k(x1));
    tmp4 = new Term.LetDecl(tmp1);
    tmp5 = new Term.DefineVar(tmp1, tmp2);
    return new Term.Blk([
      tmp4,
      tmp5
    ], tmp3)
  } 
  static body(x1, y) {
    let lambda;
    lambda = (undefined, function (caseScrut) {
      let n, tmp, tmp1, tmp2, tmp3, tmp4, lambda1;
      if (caseScrut === 0) {
        return x1
      } else if (caseScrut === 1) {
        return y
      } else {
        n = caseScrut;
        tmp = x1;
        tmp1 = y;
        tmp2 = new Term.Builtin("+");
        tmp3 = new Term.Tup([
          tmp,
          tmp1
        ]);
        tmp4 = new Term.App(tmp2, tmp3);
        lambda1 = (undefined, function (z) {
          let tmp5, tmp6;
          tmp5 = QuoteExample.body(y, z);
          tmp6 = n - 1;
          return runtime.safeCall(tmp5(tmp6))
        });
        return QuoteExample.bind(tmp4, lambda1)
      }
    });
    return lambda
  } 
  static gib(n) {
    let x2, y1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = Term.freshName("x");
    tmp1 = new Term.Symbol(tmp);
    x2 = new Term.Ref(tmp1);
    tmp2 = Term.freshName("y");
    tmp3 = new Term.Symbol(tmp2);
    y1 = new Term.Ref(tmp3);
    tmp4 = QuoteExample.body(x2, y1);
    tmp5 = runtime.safeCall(tmp4(n));
    return new Term.Lam([
      tmp1,
      tmp3
    ], tmp5)
  } 
  static safeDiv() {
    let x2, y1, d, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
    tmp = Term.freshName("x");
    tmp1 = new Term.Symbol(tmp);
    x2 = new Term.Ref(tmp1);
    tmp2 = Term.freshName("y");
    tmp3 = new Term.Symbol(tmp2);
    y1 = new Term.Ref(tmp3);
    tmp4 = Term.freshName("d");
    tmp5 = new Term.Symbol(tmp4);
    d = new Term.Ref(tmp5);
    tmp6 = Term.freshName("scrut");
    tmp7 = new Term.Symbol(tmp6);
    scrut = new Term.Ref(tmp7);
    tmp23 = y1;
    tmp24 = new Term.Lit(0.0);
    tmp25 = new Term.Builtin("==");
    tmp26 = new Term.Tup([
      tmp23,
      tmp24
    ]);
    tmp8 = new Term.App(tmp25, tmp26);
    tmp12 = scrut;
    tmp13 = new Term.LitPattern(true);
    tmp22 = d;
    tmp14 = new Term.Else(tmp22);
    tmp15 = new Term.Branch(tmp12, tmp13, tmp14);
    tmp17 = x2;
    tmp18 = y1;
    tmp19 = new Term.Builtin("/");
    tmp20 = new Term.Tup([
      tmp17,
      tmp18
    ]);
    tmp21 = new Term.App(tmp19, tmp20);
    tmp16 = new Term.Else(tmp21);
    tmp9 = new Term.Cons(tmp15, tmp16);
    tmp10 = new Term.Let(tmp7, tmp8, tmp9);
    tmp11 = new Term.IfLike(Term.Keyword.If, tmp10);
    return new Term.Lam([
      tmp1,
      tmp3,
      tmp5
    ], tmp11)
  }
  static toString() { return "QuoteExample"; }
});
let QuoteExample = QuoteExample1; export default QuoteExample;
