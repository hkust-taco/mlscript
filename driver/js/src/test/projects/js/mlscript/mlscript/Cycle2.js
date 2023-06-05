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
    const self = this;
    log(self.g(42));
  }
};
Cycle2.$init();
