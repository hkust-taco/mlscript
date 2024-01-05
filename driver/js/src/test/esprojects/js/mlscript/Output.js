import * as ConfigGen from "../my_ts_path/ConfigGen.js"

function log(x) {
  return console.info(x);
}
const Output = new class Output {
  constructor() {
  }
  $init() {
    const res = ConfigGen.generate("foo");
    log(res);
  }
};
Output.$init();
