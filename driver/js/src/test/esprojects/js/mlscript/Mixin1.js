import { Mixin2 } from "./Mixin2.js"

const Mixin1 = new class Mixin1 {
  #Neg;
  #MyLang;
  constructor() {
  }
  get show() {
    const qualifier = this;
    return ((() => {
      let program = Mixin2.Add(Mixin2.Lit(48), qualifier.Neg(Mixin2.Lit(6)));
      return console.log(qualifier.MyLang.eval(program));
    })());
  }
  EvalNeg(base) {
    const qualifier = this;
    return (class EvalNeg extends base {
      constructor(...rest) {
        super(...rest);
      }
      eval(e) {
        const qualifier1 = this;
        return ((() => {
          return e instanceof qualifier.Neg.class ? (([d]) => 0 - qualifier1.eval(d))(qualifier.Neg.unapply(e)) : super.eval(e);
        })());
      }
    });
  }
  get MyLang() {
    const qualifier = this;
    if (this.#MyLang === undefined) {
      class MyLang extends qualifier.EvalNeg(Mixin2.EvalBase(Object)) {
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
    const qualifier = this;
    if (this.#Neg === undefined) {
      class Neg {
        #expr;
        constructor(expr) {
          this.#expr = expr;
        }
      static
        unapply(x) {
          return [x.#expr];
        }
      };
      this.#Neg = ((expr) => Object.freeze(new Neg(expr)));
      this.#Neg.class = Neg;
      this.#Neg.unapply = Neg.unapply;
    }
    return this.#Neg;
  }
  $init() {
    const qualifier = this;
    qualifier.show;
  }
};
Mixin1.$init();
