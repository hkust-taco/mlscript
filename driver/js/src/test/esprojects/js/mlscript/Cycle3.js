import { Cycle4 } from "./Cycle4.js"

export const Cycle3 = new class Cycle3 {
  constructor() {
  }
  f(x) {
    return x === 0 ? 114 : Cycle4.g(x - 1);
  }
  $init() {}
};
Cycle3.$init();
