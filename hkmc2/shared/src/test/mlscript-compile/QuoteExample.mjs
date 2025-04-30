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
    let x, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = new Term.Symbol("x");
    x = new Term.Ref(tmp);
    tmp1 = x;
    tmp2 = new Term.Lit(1);
    tmp3 = new Term.Builtin("+");
    tmp4 = new Term.Tup([
      tmp1,
      tmp2
    ]);
    tmp5 = new Term.App(tmp3, tmp4);
    return new Term.Lam([
      tmp
    ], tmp5)
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
    let x1, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new Term.Symbol("x");
    x1 = new Term.Ref(tmp);
    tmp1 = rhs;
    tmp2 = runtime.safeCall(k(x1));
    tmp3 = new Term.LetDecl(tmp);
    tmp4 = new Term.DefineVar(tmp, tmp1);
    return new Term.Blk([
      tmp3,
      tmp4
    ], tmp2)
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
    let x2, y1, tmp, tmp1, tmp2, tmp3;
    tmp = new Term.Symbol("x");
    x2 = new Term.Ref(tmp);
    tmp1 = new Term.Symbol("y");
    y1 = new Term.Ref(tmp1);
    tmp2 = QuoteExample.body(x2, y1);
    tmp3 = runtime.safeCall(tmp2(n));
    return new Term.Lam([
      tmp,
      tmp1
    ], tmp3)
  } 
  static safeDiv() {
    let x2, y1, d, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
    tmp = new Term.Symbol("x");
    x2 = new Term.Ref(tmp);
    tmp1 = new Term.Symbol("y");
    y1 = new Term.Ref(tmp1);
    tmp2 = new Term.Symbol("d");
    d = new Term.Ref(tmp2);
    tmp3 = new Term.Symbol("scrut");
    scrut = new Term.Ref(tmp3);
    tmp19 = y1;
    tmp20 = new Term.Lit(0.0);
    tmp21 = new Term.Builtin("==");
    tmp22 = new Term.Tup([
      tmp19,
      tmp20
    ]);
    tmp4 = new Term.App(tmp21, tmp22);
    tmp8 = scrut;
    tmp9 = new Term.LitPattern(true);
    tmp18 = d;
    tmp10 = new Term.Else(tmp18);
    tmp11 = new Term.Branch(tmp8, tmp9, tmp10);
    tmp13 = x2;
    tmp14 = y1;
    tmp15 = new Term.Builtin("/");
    tmp16 = new Term.Tup([
      tmp13,
      tmp14
    ]);
    tmp17 = new Term.App(tmp15, tmp16);
    tmp12 = new Term.Else(tmp17);
    tmp5 = new Term.Cons(tmp11, tmp12);
    tmp6 = new Term.Let(tmp3, tmp4, tmp5);
    tmp7 = new Term.IfLike(Term.Keyword.If, tmp6);
    return new Term.Lam([
      tmp,
      tmp1,
      tmp2
    ], tmp7)
  }
  static toString() { return "QuoteExample"; }
});
let QuoteExample = QuoteExample1; export default QuoteExample;
