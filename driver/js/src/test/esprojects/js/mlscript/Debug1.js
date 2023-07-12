import { Debug2 } from "./Debug2.js"

import { Debug4 } from "./Debug4.js"

const Debug1 = new class Debug1 {
  #x;
  get x() { return this.#x; }
  constructor() {
  }
  $init() {
    this.#x = 42;
    const x = this.#x;
  }
};
Debug1.$init();
