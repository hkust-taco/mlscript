const CJS2 = require("./CJS2.js")

const CJS1 = new class CJS1 {
  constructor() {
  }
  $init() {
    console.log(CJS2.add(42, 24));
  }
};
CJS1.$init();
