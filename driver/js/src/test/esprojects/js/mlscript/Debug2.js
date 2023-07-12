import { Debug3 } from "./Debug3.js"

export const Debug2 = new class Debug2 {
  #y;
  get y() { return this.#y; }
  constructor() {
  }
  $init() {
    this.#y = 42;
    const y = this.#y;
  }
};
Debug2.$init();
