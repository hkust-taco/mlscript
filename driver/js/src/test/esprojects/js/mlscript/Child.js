import { Parent } from "./Parent.js"

const Child = new class Child {
  #Child1;
  #Child2;
  constructor() {
  }
  get Child1() {
    const qualifier = this;
    if (this.#Child1 === undefined) {
      class Child1 extends Parent.Parent1.class {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          super(x + 1);
          this.#x = x;
        }
      static
        unapply(x) {
          return [x.#x];
        }
      };
      this.#Child1 = ((x) => Object.freeze(new Child1(x)));
      this.#Child1.class = Child1;
      this.#Child1.unapply = Child1.unapply;
    }
    return this.#Child1;
  }
  get Child2() {
    const qualifier = this;
    if (this.#Child2 === undefined) {
      class Child2 extends Parent.Parent2 {
        #y;
        get y() { return this.#y; }
        constructor(y) {
          super();
          this.#y = y;
        }
      static
        unapply(x) {
          return [x.#y];
        }
      };
      this.#Child2 = ((y) => Object.freeze(new Child2(y)));
      this.#Child2.class = Child2;
      this.#Child2.unapply = Child2.unapply;
    }
    return this.#Child2;
  }
  $init() {
    const qualifier = this;
    const c1 = qualifier.Child1(2);
    const c2 = qualifier.Child2(3);
    console.log(c1.inc);
    console.log(c2.x);
  }
};
Child.$init();
