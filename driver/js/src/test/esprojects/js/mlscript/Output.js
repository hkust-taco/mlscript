import * as ConfigGen from "../my_ts_path/ConfigGen.js"

function log(x) {
  return console.info(x);
}
const Output = new class Output {
  #res;
  get res() { return this.#res; }
  constructor() {
  }
  $init() {
    this.#res = ConfigGen.generate("foo");
    const res = this.#res;
    log(res);
  }
};
Output.$init();
