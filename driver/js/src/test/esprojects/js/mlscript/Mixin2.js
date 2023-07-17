export const Mixin2 = new class Mixin2 {
  #Add;
  #Lit;
  constructor() {
  }
  eval(e) {
    const self = this;
    return ((() => {
      let a;
      return (a = e, a instanceof self.Lit.class ? ((n) => n)(e.n) : a instanceof self.Add.class ? ((l) => ((r) => self.eval(l) + self.eval(r))(e.rhs))(e.lhs) : (() => {
        throw new Error("non-exhaustive case expression");
      })());
    })());
  }
  EvalBase(base) {
    const outer = this;
    return (class EvalBase extends base {
      constructor(...rest) {
        super(...rest);
      }
      eval(e) {
        const self = this;
        return ((() => {
          let a;
          return (a = e, a instanceof outer.Lit.class ? ((n) => n)(e.n) : a instanceof outer.Add.class ? ((l) => ((r) => self.eval(l) + self.eval(r))(e.rhs))(e.lhs) : (() => {
            throw new Error("non-exhaustive case expression");
          })());
        })());
      }
    });
  }
  get Add() {
    const outer = this;
    if (this.#Add === undefined) {
      class Add {
        #lhs;
        get lhs() { return this.#lhs; }
        #rhs;
        get rhs() { return this.#rhs; }
        constructor(lhs, rhs) {
          this.#lhs = lhs;
          this.#rhs = rhs;
        }
      };
      this.#Add = ((lhs, rhs) => Object.freeze(new Add(lhs, rhs)));
      this.#Add.class = Add;
    }
    return this.#Add;
  }
  get Lit() {
    const outer = this;
    if (this.#Lit === undefined) {
      class Lit {
        #n;
        get n() { return this.#n; }
        constructor(n) {
          this.#n = n;
        }
      };
      this.#Lit = ((n) => Object.freeze(new Lit(n)));
      this.#Lit.class = Lit;
    }
    return this.#Lit;
  }
  $init() {}
};
Mixin2.$init();
