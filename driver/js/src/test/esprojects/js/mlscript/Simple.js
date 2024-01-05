import { Opened } from "./Opened.js"

function log(x) {
  return console.info(x);
}
const Simple = new class Simple {
  #A;
  #C;
  constructor() {
  }
  B(base) {
    const qualifier = this;
    return (class B extends base {
      constructor(...rest) {
        super(...rest);
      }
      get foo() {
        const qualifier1 = this;
        return qualifier1.n;
      }
    });
  }
  get C() {
    const qualifier = this;
    if (this.#C === undefined) {
      class C {
        constructor() {
          const b = 1;
        }
      }
      this.#C = new C();
      this.#C.class = C;
    }
    return this.#C;
  }
  get A() {
    const qualifier = this;
    if (this.#A === undefined) {
      class A extends qualifier.B(Object) {
        #n;
        get n() { return this.#n; }
        constructor(n) {
          super();
          this.#n = n;
        }
      static
        unapply(x) {
          return [x.#n];
        }
      };
      this.#A = ((n) => Object.freeze(new A(n)));
      this.#A.class = A;
      this.#A.unapply = A.unapply;
    }
    return this.#A;
  }
  $init() {
    const qualifier = this;
    const a = qualifier.A(42);
    log(a.foo);
    Opened.hello(a.n);
  }
};
Simple.$init();
