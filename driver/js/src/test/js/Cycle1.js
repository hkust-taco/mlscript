import { Cycle2 } from "./Cycle2.js"

(() => {
  if (globalThis.Cycle1 === undefined) {
    class Cycle1 {
      constructor() {
      }
      f(x) {
        return Cycle2.A(x + 1);
      }
    }
    globalThis.Cycle1 = new Cycle1();
    globalThis.Cycle1["class"] = Cycle1;
  }
  return globalThis.Cycle1;
})();
const Cycle1 = globalThis.Cycle1;
export {Cycle1}
