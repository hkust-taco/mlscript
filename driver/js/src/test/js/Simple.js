let typing_unit = {
  cache: {},
  B(base) {
    return (class B extends base {
      constructor(...rest) {
        super(...rest);
      }
      get foo() {
        const self = this;
        return self.n;
      }
    });
  },
  get A() {
    if (this.cache.A === undefined) {
      class A extends B(Object) {
        #n;
        get n() { return this.#n; }
        constructor(n) {
          super();
          this.#n = n;
        }
      };
      this.cache.A = ((n) => new A(n));
      this.cache.A["class"] = A;
    }
    return this.cache.A;
  }
};
globalThis.B = typing_unit.B;
globalThis.A = typing_unit.A;
const a = A(42);
console.log(a.foo + 1);
