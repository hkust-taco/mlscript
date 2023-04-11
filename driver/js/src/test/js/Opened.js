import { Inc } from "./tools/Inc.js"

function log(x) {
  return console.info(x);
}
export const Opened = (() => new class Opened {
  constructor() {
    const self = this;
    self.hello(114513);
  }
  hello(x) {
    return (log([
      "hello!",
      Inc.inc(x)
    ]));
  }
})();
