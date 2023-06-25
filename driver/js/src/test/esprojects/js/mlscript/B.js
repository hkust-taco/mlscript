import { A } from "./A.js"

export const B = new class B {
  constructor() {
  }
  get foo() {
    return A.Foo(12);
  }
  $init() {}
};
B.$init();
