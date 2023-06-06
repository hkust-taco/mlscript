import json5 from "json5"

function log(x) {
  return console.info(x);
}
const Output2 = new class Output2 {
  #config;
  get config() { return this.#config; }
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
    const self = this;
    this.#config = self.createConfig("bar");
    const config = this.#config;
    log(config);
  }
};
Output2.$init();
