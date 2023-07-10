import { Parent } from "./Parent.js"

const Child = new class Child {
  #Child1;
  #Child2;
  #c1;
  get c1() { return this.#c1; }
  #c2;
  get c2() { return this.#c2; }
  constructor() {
  }
  get Child1() {
    const outer = this;
    if (this.#Child1 === undefined) {
      class Child1 extends Parent.Parent1.class {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          super(x + 1);
          this.#x = x;
        }
      };
      this.#Child1 = ((x) => Object.freeze(new Child1(x)));
      this.#Child1.class = Child1;
    }
    return this.#Child1;
  }
  get Child2() {
    const outer = this;
    if (this.#Child2 === undefined) {
      class Child2 extends Parent.Parent2 {
        #y;
        get y() { return this.#y; }
        constructor(y) {
          super();
          this.#y = y;
        }
      };
      this.#Child2 = ((y) => Object.freeze(new Child2(y)));
      this.#Child2.class = Child2;
    }
    return this.#Child2;
  }
  $init() {
    const self = this;
    this.#c1 = self.Child1(2);
    const c1 = this.#c1;
    this.#c2 = self.Child2(3);
    const c2 = this.#c2;
    console.log(c1.inc);
    console.log(c2.x);
  }
};
Child.$init();
