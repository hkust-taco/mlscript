export const Debug4 = new class Debug4 {
  #w;
  get w() { return this.#w; }
  constructor() {
  }
  $init() {
    this.#w = "wuwuwu";
    const w = this.#w;
  }
};
Debug4.$init();
