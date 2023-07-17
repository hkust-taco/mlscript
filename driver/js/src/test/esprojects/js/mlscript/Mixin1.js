import { Mixin2 } from "./Mixin2.js"

const Mixin1 = new class Mixin1 {
  #Neg;
  #MyLang;
  constructor() {
  }
  get show() {
    const self = this;
    return ((() => {
      let program = Mixin2.Add(Mixin2.Lit(48), self.Neg(Mixin2.Lit(6)));
      return console.log(self.MyLang.eval(program));
    })());
  }
  EvalNeg(base) {
    const outer = this;
    return (class EvalNeg extends base {
      constructor(...rest) {
        super(...rest);
      }
      eval(e) {
        const self = this;
        return ((() => {
          return e instanceof outer.Neg.class ? ((d) => 0 - self.eval(d))(e.expr) : super.eval(e);
        })());
      }
    });
  }
  get MyLang() {
    const outer = this;
    if (this.#MyLang === undefined) {
      class MyLang extends outer.EvalNeg(Mixin2.EvalBase(Object)) {
        constructor() {
          super();
        }
      }
      this.#MyLang = new MyLang();
      this.#MyLang.class = MyLang;
    }
    return this.#MyLang;
  }
  get Neg() {
    const outer = this;
    if (this.#Neg === undefined) {
      class Neg {
        #expr;
        get expr() { return this.#expr; }
        constructor(expr) {
          this.#expr = expr;
        }
      };
      this.#Neg = ((expr) => Object.freeze(new Neg(expr)));
      this.#Neg.class = Neg;
    }
    return this.#Neg;
  }
  $init() {
    const self = this;
    self.show;
  }
};
Mixin1.$init();
