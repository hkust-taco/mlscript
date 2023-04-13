import { B } from "./B.js"

function log(x) {
  return console.info(x);
}
const C = new class C {
  #a;
  get a() { return this.#a; }
  constructor() {
  }
  $init() {
    this.#a = B.foo;
    const a = this.#a;
    log(a.x);
  }
};
C.$init();
