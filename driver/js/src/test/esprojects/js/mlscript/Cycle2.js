import { Cycle1 } from "./Cycle1.js"

function log(x) {
  return console.info(x);
}
export const Cycle2 = new class Cycle2 {
  constructor() {
  }
  g(x) {
    return Cycle1.f(x);
  }
  $init() {
    const qualifier = this;
    log(qualifier.g(42));
  }
};
Cycle2.$init();
