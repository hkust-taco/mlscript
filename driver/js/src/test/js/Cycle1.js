import { Cycle2 } from "./Cycle2.js"

export const Cycle1 = new class Cycle1 {
  constructor() {
  }
  f(x) {
    return x === 0 ? 114 : Cycle2.g(x - 1);
  }
  $init() {}
};
Cycle1.$init();
