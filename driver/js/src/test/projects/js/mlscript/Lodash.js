import fp from "lodash/fp"

const Lodash = new class Lodash {
  constructor() {
  }
  inc(x) {
    return x + 1;
  }
  $init() {
    const self = this;
    console.log(fp.map(self.inc)([
      1,
      2,
      3
    ]));
  }
};
Lodash.$init();
