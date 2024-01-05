const TyperDebug = new class TyperDebug {
  #A;
  constructor() {
  }
  get A() {
    const qualifier = this;
    if (this.#A === undefined) {
      class A {
        #x;
        constructor(x) {
          this.#x = x;
        }
        add(y) {
          const x = this.#x;
          return x + y;
        }
      static
        unapply(x) {
          return [x.#x];
        }
      };
      this.#A = ((x) => Object.freeze(new A(x)));
      this.#A.class = A;
      this.#A.unapply = A.unapply;
    }
    return this.#A;
  }
  $init() {
    const qualifier = this;
    const aa = qualifier.A(42);
    console.log(aa.add(6));
  }
};
TyperDebug.$init();
