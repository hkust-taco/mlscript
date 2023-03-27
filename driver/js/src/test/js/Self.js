import { Self } from "./Self.js"

(() => {
  if (globalThis.Foo === undefined) {
    class Foo {};
    globalThis.Foo = (() => new Foo());
    globalThis.Foo["class"] = Foo;
  }
  return globalThis.Foo;
})();
const Foo = globalThis.Foo;
