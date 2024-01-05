export const A = new class A {
  #Foo;
  constructor() {
  }
  get Foo() {
    const qualifier = this;
    if (this.#Foo === undefined) {
      class Foo {
        #x;
        get x() { return this.#x; }
        constructor(x) {
          this.#x = x;
        }
      static
        unapply(x) {
          return [x.#x];
        }
      };
      this.#Foo = ((x) => Object.freeze(new Foo(x)));
      this.#Foo.class = Foo;
      this.#Foo.unapply = Foo.unapply;
    }
    return this.#Foo;
  }
  $init() {}
};
A.$init();
