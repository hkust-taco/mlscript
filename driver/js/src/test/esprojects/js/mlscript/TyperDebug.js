const TyperDebug = new class TyperDebug {
  #A;
  #aa;
  get aa() { return this.#aa; }
  constructor() {
  }
  get A() {
    const outer = this;
    if (this.#A === undefined) {
      class A {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          this.#x = x;
        }
        add(y) {
          const x = this.#x;
          return x + y;
        }
      };
      this.#A = ((x) => Object.freeze(new A(x)));
      this.#A.class = A;
    }
    return this.#A;
  }
  $init() {
    const self = this;
    this.#aa = self.A(42);
    const aa = this.#aa;
    console.log(aa.add(6));
  }
};
TyperDebug.$init();
