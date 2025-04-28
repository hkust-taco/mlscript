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
    let tmp, x, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = Term.freshName("x");
    x = new Term.Symbol(tmp);
    tmp1 = new Term.Ref(x);
    tmp2 = new Term.Lit(1);
    tmp3 = new Term.Builtin("+");
    tmp4 = new Term.Tup([
      tmp1,
      tmp2
    ]);
    tmp5 = new Term.App(tmp3, tmp4);
    return new Term.Lam([
      x
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
    let tmp, x1, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = Term.freshName("x");
    x1 = new Term.Symbol(tmp);
    tmp1 = rhs;
    tmp2 = new Term.Ref(x1);
    tmp3 = runtime.safeCall(k(tmp2));
    tmp4 = new Term.LetDecl(x1);
    tmp5 = new Term.DefineVar(x1, tmp1);
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
    let tmp, x2, tmp1, y1, tmp2, tmp3, tmp4, tmp5;
    tmp = Term.freshName("x");
    x2 = new Term.Symbol(tmp);
    tmp1 = Term.freshName("y");
    y1 = new Term.Symbol(tmp1);
    tmp2 = new Term.Ref(x2);
    tmp3 = new Term.Ref(y1);
    tmp4 = QuoteExample.body(tmp2, tmp3);
    tmp5 = runtime.safeCall(tmp4(n));
    return new Term.Lam([
      x2,
      y1
    ], tmp5)
  } 
  static safeDiv() {
    let tmp, x2, tmp1, y1, tmp2, d, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
    tmp = Term.freshName("x");
    x2 = new Term.Symbol(tmp);
    tmp1 = Term.freshName("y");
    y1 = new Term.Symbol(tmp1);
    tmp2 = Term.freshName("d");
    d = new Term.Symbol(tmp2);
    tmp3 = Term.freshName("scrut");
    tmp4 = new Term.Symbol(tmp3);
    tmp5 = new Term.Ref(y1);
    tmp6 = new Term.Lit(0.0);
    tmp7 = new Term.Builtin("==");
    tmp8 = new Term.Tup([
      tmp5,
      tmp6
    ]);
    tmp9 = new Term.App(tmp7, tmp8);
    tmp10 = new Term.Ref(tmp4);
    tmp11 = new Term.LitPattern(true);
    tmp12 = new Term.Ref(d);
    tmp13 = new Term.Else(tmp12);
    tmp14 = new Term.Branch(tmp10, tmp11, tmp13);
    tmp15 = new Term.Ref(x2);
    tmp16 = new Term.Ref(y1);
    tmp17 = new Term.Builtin("/");
    tmp18 = new Term.Tup([
      tmp15,
      tmp16
    ]);
    tmp19 = new Term.App(tmp17, tmp18);
    tmp20 = new Term.Else(tmp19);
    tmp21 = new Term.Cons(tmp14, tmp20);
    tmp22 = new Term.Let(tmp4, tmp9, tmp21);
    tmp23 = new Term.IfLike(Term.Keyword.If, tmp22);
    return new Term.Lam([
      x2,
      y1,
      d
    ], tmp23)
  }
  static toString() { return "QuoteExample"; }
});
let QuoteExample = QuoteExample1; export default QuoteExample;
