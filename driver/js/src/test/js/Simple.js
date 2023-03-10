let typing_unit = {
  cache: {},
  get A() {
    if (this.cache.A === undefined) {
      class A {
        #n;
        get n() { return this.#n; }
        constructor(n) {
          this.#n = n;
        }
      };
      this.cache.A = ((n) => new A(n));
      this.cache.A["class"] = A;
    }
    return this.cache.A;
  }
};
globalThis.A = typing_unit.A;
const a = A(42);