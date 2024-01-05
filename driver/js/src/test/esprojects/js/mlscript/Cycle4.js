import { Cycle3 } from "./Cycle3.js"

function log(x) {
  return console.info(x);
}
export const Cycle4 = new class Cycle4 {
  constructor() {
  }
  g(x) {
    return Cycle3.f(x);
  }
  $init() {
    const qualifier = this;
    log(qualifier.g(42));
  }
};
Cycle4.$init();
