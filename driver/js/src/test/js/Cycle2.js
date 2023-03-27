import { Cycle1 } from "./Cycle1.js"

(() => {
  if (globalThis.A === undefined) {
    class A {
      #x;
      get x() { return this.#x; }
      constructor(x) {
        this.#x = x;
      }
    };
    globalThis.A = ((x) => new A(x));
    globalThis.A["class"] = A;
  }
  return globalThis.A;
})();
const A = globalThis.A;
const a = Cycle1.f(42);
