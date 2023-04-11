import { _Inc as Inc } from "./tools/Inc.js"

function log(x) {
  return console.info(x);
}
class Opened {
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
}
export const _Opened = new Opened;
