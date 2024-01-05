const Foo = require("../ts/Foo.js")

const Bar = new class Bar {
  #Bar;
  constructor() {
  }
  get Bar() {
    const qualifier = this;
    if (this.#Bar === undefined) {
      class Bar extends Foo {
        constructor() {
          super();
        }
        get bar() {
          return "bar";
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
    const bf = qualifier.Bar();
    console.log(bf.bar);
    console.log(bf.foo());
  }
};
Bar.$init();
