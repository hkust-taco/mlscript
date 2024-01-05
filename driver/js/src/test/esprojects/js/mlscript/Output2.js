import json5 from "json5"

function log(x) {
  return console.info(x);
}
const Output2 = new class Output2 {
  constructor() {
  }
  createConfig(path) {
    return ((() => {
      let options = { outDir: path };
      let config = { compilerOptions: options };
      return json5.stringify(config);
    })());
  }
  $init() {
    const qualifier = this;
    const config = qualifier.createConfig("bar");
    log(config);
  }
};
Output2.$init();
