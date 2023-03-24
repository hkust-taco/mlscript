import * as Opened from "./Opened.js"
function B(base) {
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
(() => {
  if (globalThis.C === undefined) {
    class C {
      #b;
      get b() { return this.#b; }
      constructor() {
        this.#b = 1;
        const b = this.#b;
      }
    }
    globalThis.C = new C();
    globalThis.C["class"] = C;
  }
  return globalThis.C;
})();
(() => {
  if (globalThis.A === undefined) {
    class A extends B(Object) {
      #n;
      get n() { return this.#n; }
      constructor(n) {
        super();
        this.#n = n;
      }
    };
    globalThis.A = ((n) => new A(n));
    globalThis.A["class"] = A;
  }
  return globalThis.A;
})();
const C = globalThis.C;
const A = globalThis.A;
const a = A(42);
console.log(a.foo);
Opened.hello(a.n);
