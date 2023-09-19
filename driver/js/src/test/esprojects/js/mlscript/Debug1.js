import { Debug2 } from "./Debug2.js"

import { Debug4 } from "./Debug4.js"

const Debug1 = new class Debug1 {
  constructor() {
  }
  $init() {
    const x = 42;
  }
};
Debug1.$init();
