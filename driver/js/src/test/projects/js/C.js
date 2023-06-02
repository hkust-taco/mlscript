import { B } from "./B.js"

function log(x) {
  return console.info(x);
}
const C = new class C {
  #a;
  #b;
  get a() { return this.#a; }
  get b() { return this.#b; }
  constructor() {
  }
  $init() {
    this.#a = B.foo;
    const a = this.#a;
    this.#b = A.Foo(0);
    const b = this.#b;
    log(a.x);
  }
};
C.$init();
