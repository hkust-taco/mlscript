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
    const qualifier = this;
    qualifier.hello(114513);
  }
};
Opened.$init();
