export const Mixin2 = new class Mixin2 {
  #Add;
  #Lit;
  constructor() {
  }
  eval(e) {
    const qualifier = this;
    return ((() => {
      let a;
      return (a = e, a instanceof qualifier.Lit.class ? (([n]) => n)(qualifier.Lit.unapply(e)) : a instanceof qualifier.Add.class ? (([
        l,
        r
      ]) => qualifier.eval(l) + qualifier.eval(r))(qualifier.Add.unapply(e)) : (() => {
        throw new Error("non-exhaustive case expression");
      })());
    })());
  }
  EvalBase(base) {
    const qualifier = this;
    return (class EvalBase extends base {
      constructor(...rest) {
        super(...rest);
      }
      eval(e) {
        const qualifier1 = this;
        return ((() => {
          let a;
          return (a = e, a instanceof qualifier.Lit.class ? (([n]) => n)(qualifier.Lit.unapply(e)) : a instanceof qualifier.Add.class ? (([
            l,
            r
          ]) => qualifier1.eval(l) + qualifier1.eval(r))(qualifier.Add.unapply(e)) : (() => {
            throw new Error("non-exhaustive case expression");
          })());
        })());
      }
    });
  }
  get Add() {
    const qualifier = this;
    if (this.#Add === undefined) {
      class Add {
        #lhs;
        #rhs;
        constructor(lhs, rhs) {
          this.#lhs = lhs;
          this.#rhs = rhs;
        }
      static
        unapply(x) {
          return ([
            x.#lhs,
            x.#rhs
          ]);
        }
      };
      this.#Add = ((lhs, rhs) => Object.freeze(new Add(lhs, rhs)));
      this.#Add.class = Add;
      this.#Add.unapply = Add.unapply;
    }
    return this.#Add;
  }
  get Lit() {
    const qualifier = this;
    if (this.#Lit === undefined) {
      class Lit {
        #n;
        constructor(n) {
          this.#n = n;
        }
      static
        unapply(x) {
          return [x.#n];
        }
      };
      this.#Lit = ((n) => Object.freeze(new Lit(n)));
      this.#Lit.class = Lit;
      this.#Lit.unapply = Lit.unapply;
    }
    return this.#Lit;
  }
  $init() {}
};
Mixin2.$init();
