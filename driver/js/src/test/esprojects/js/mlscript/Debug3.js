export const Debug3 = new class Debug3 {
  #z;
  get z() { return this.#z; }
  constructor() {
  }
  $init() {
    this.#z = 1;
    const z = this.#z;
  }
};
Debug3.$init();
