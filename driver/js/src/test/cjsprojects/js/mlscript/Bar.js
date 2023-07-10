const Foo = require("../ts/Foo.js")

const Bar = new class Bar {
  #Bar;
  #bf;
  get bf() { return this.#bf; }
  constructor() {
  }
  get Bar() {
    const outer = this;
    if (this.#Bar === undefined) {
      class Bar extends Foo {
        constructor() {
          super();
        }
        get bar() {
          return "bar";
        }
      };
      this.#Bar = (() => Object.freeze(new Bar()));
      this.#Bar.class = Bar;
    }
    return this.#Bar;
  }
  $init() {
    const self = this;
    this.#bf = self.Bar();
    const bf = this.#bf;
    console.log(bf.bar);
    console.log(bf.foo());
  }
};
Bar.$init();
