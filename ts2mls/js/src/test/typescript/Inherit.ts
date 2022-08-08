class A {
  constructor() {}

  foo() {
      console.log("foo")
  }
}

class B extends A {}

class C<T> {
  constructor() {}

  private t: T

  set(x: T) { this.t = x; }
  get() { return this.t; } 
}

class D extends C<number> {
}