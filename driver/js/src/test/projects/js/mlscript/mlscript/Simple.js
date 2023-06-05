import { Opened } from "./Opened.js"

function log(x) {
  return console.info(x);
}
const Simple = new class Simple {
  #A;
  #C;
  #a;
  get a() { return this.#a; }
  constructor() {
  }
  B(base) {
    const outer = this;
    return (class B extends base {
      constructor(...rest) {
        super(...rest);
      }
      get foo() {
        const self = this;
        return self.n;
      }
    });
  }
  get C() {
    const outer = this;
    if (this.#C === undefined) {
      class C {
        #b;
        get b() { return this.#b; }
        constructor() {
          this.#b = 1;
          const b = this.#b;
        }
      }
      this.#C = new C();
      this.#C.class = C;
    }
    return this.#C;
  }
  get A() {
    const outer = this;
    if (this.#A === undefined) {
      class A extends outer.B(Object) {
        #n;
        get n() { return this.#n; }
        constructor(n) {
          super();
          this.#n = n;
        }
      };
      this.#A = ((n) => Object.freeze(new A(n)));
      this.#A.class = A;
    }
    return this.#A;
  }
  $init() {
    const self = this;
    this.#a = self.A(42);
    const a = this.#a;
    log(a.foo);
    Opened.hello(a.n);
  }
};
Simple.$init();
