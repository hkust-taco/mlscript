const fp = require("lodash/fp")

const Lodash = new class Lodash {
  constructor() {
  }
  inc(x) {
    return x + 1;
  }
  $init() {
    const qualifier = this;
    console.log(fp.map(qualifier.inc)([
      1,
      2,
      3
    ]));
  }
};
Lodash.$init();
