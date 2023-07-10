const Baz = require("../ts/Baz.js")

const BazBaz = new class BazBaz {
  #BazBaz;
  #bazbaz;
  get bazbaz() { return this.#bazbaz; }
  constructor() {
  }
  get BazBaz() {
    const outer = this;
    if (this.#BazBaz === undefined) {
      class BazBaz extends Baz.Baz {
        constructor() {
          super(2);
        }
      };
      this.#BazBaz = (() => Object.freeze(new BazBaz()));
      this.#BazBaz.class = BazBaz;
    }
    return this.#BazBaz;
  }
  $init() {
    const self = this;
    this.#bazbaz = self.BazBaz();
    const bazbaz = this.#bazbaz;
    bazbaz.baz();
  }
};
BazBaz.$init();
