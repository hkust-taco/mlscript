export const A = new class A {
  #Foo;
  constructor() {
  }
  get Foo() {
    const outer = this;
    if (this.#Foo === undefined) {
      class Foo {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          this.#x = x;
        }
      };
      this.#Foo = ((x) => new Foo(x));
      this.#Foo.class = Foo;
    }
    return this.#Foo;
  }
  $init() {}
};
A.$init();
