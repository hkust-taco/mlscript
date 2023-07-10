export const Parent = new class Parent {
  #Parent1;
  #Parent2;
  constructor() {
  }
  get Parent1() {
    const outer = this;
    if (this.#Parent1 === undefined) {
      class Parent1 {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          this.#x = x;
        }
        get inc() {
          const x = this.#x;
          return x + 1;
        }
      };
      this.#Parent1 = ((x) => Object.freeze(new Parent1(x)));
      this.#Parent1.class = Parent1;
    }
    return this.#Parent1;
  }
  get Parent2() {
    const outer = this;
    if (this.#Parent2 === undefined) {
      class Parent2 {
        constructor() {
        }
        get x() {
          return 42;
        }
      };
      this.#Parent2 = Parent2;
    }
    return this.#Parent2;
  }
  $init() {}
};
Parent.$init();
