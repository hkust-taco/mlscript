const Baz = require("../ts/Baz.js")

const BazBaz = new class BazBaz {
  #BazBaz;
  constructor() {
  }
  get BazBaz() {
    const qualifier = this;
    if (this.#BazBaz === undefined) {
      class BazBaz extends Baz.Baz {
        constructor() {
          super(2);
        }
      static
        unapply(x) {
          return [];
        }
      };
      this.#BazBaz = (() => Object.freeze(new BazBaz()));
      this.#BazBaz.class = BazBaz;
      this.#BazBaz.unapply = BazBaz.unapply;
    }
    return this.#BazBaz;
  }
  $init() {
    const qualifier = this;
    const bazbaz = qualifier.BazBaz();
    bazbaz.baz();
  }
};
BazBaz.$init();
