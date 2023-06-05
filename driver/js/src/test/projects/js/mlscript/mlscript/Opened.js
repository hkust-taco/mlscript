import { Inc } from "./tools/Inc.js"

function log(x) {
  return console.info(x);
}
export const Opened = new class Opened {
  constructor() {
  }
  hello(x) {
    return (log([
      "hello!",
      Inc.inc(x)
    ]));
  }
  $init() {
    const self = this;
    self.hello(114513);
  }
};
Opened.$init();
