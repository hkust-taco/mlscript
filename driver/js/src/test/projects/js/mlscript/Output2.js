import * as json5 from "json5"

function log(x) {
  return console.info(x);
}
const Output2 = new class Output2 {
  #CompilerOptions;
  #TSConfig;
  #config;
  get config() { return this.#config; }
  constructor() {
  }
  get CompilerOptions() {
    const outer = this;
    if (this.#CompilerOptions === undefined) {
      class CompilerOptions {
        #outDir;
        get outDir() { return this.#outDir; }
        constructor(outDir) {
          this.#outDir = outDir;
        }
      };
      this.#CompilerOptions = ((outDir) => Object.freeze(new CompilerOptions(outDir)));
      this.#CompilerOptions.class = CompilerOptions;
    }
    return this.#CompilerOptions;
  }
  get TSConfig() {
    const outer = this;
    if (this.#TSConfig === undefined) {
      class TSConfig {
        #compilerOptions;
        get compilerOptions() { return this.#compilerOptions; }
        constructor(compilerOptions) {
          this.#compilerOptions = compilerOptions;
        }
      };
      this.#TSConfig = ((compilerOptions) => Object.freeze(new TSConfig(compilerOptions)));
      this.#TSConfig.class = TSConfig;
    }
    return this.#TSConfig;
  }
  $init() {
    const self = this;
    this.#config = json5.stringify(self.TSConfig(self.CompilerOptions("bar")));
    const config = this.#config;
    log(config);
  }
};
Output2.$init();
