import * as MyClass from "../my_ts_path/MyClass.js"

const NewTSClass = new class NewTSClass {
  #Bar;
  constructor() {
  }
  get Bar() {
    const outer = this;
    if (this.#Bar === undefined) {
      class Bar extends MyClass.FooClass {
        constructor() {
          super();
        }
      };
      this.#Bar = (() => Object.freeze(new Bar()));
      this.#Bar.class = Bar;
    }
    return this.#Bar;
  }
  $init() {
    const self = this;
    self.Bar().foo();
  }
};
NewTSClass.$init();
