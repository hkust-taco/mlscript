import * as MyClass from "../my_ts_path/MyClass.js"

const NewTSClass = new class NewTSClass {
  #Bar;
  constructor() {
  }
  get Bar() {
    const qualifier = this;
    if (this.#Bar === undefined) {
      class Bar extends MyClass.FooClass {
        constructor() {
          super();
        }
      static
        unapply(x) {
          return [];
        }
      };
      this.#Bar = (() => Object.freeze(new Bar()));
      this.#Bar.class = Bar;
      this.#Bar.unapply = Bar.unapply;
    }
    return this.#Bar;
  }
  $init() {
    const qualifier = this;
    qualifier.Bar().foo();
  }
};
NewTSClass.$init();
