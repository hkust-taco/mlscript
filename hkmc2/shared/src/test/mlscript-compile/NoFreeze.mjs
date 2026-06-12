const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
let NoFreeze1;
(class NoFreeze {
  static {
    NoFreeze1 = this
  }
  static {
    NoFreeze.Foo = function Foo(x) {
      return (new Foo.class(x));
    };
    (class Foo {
      static {
        NoFreeze.Foo.class = this
      }
      constructor(x) {
        this.x = x;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Foo", ["x"]];
    });
  }
  static foo() {
    return (new NoFreeze.Foo.class(0))
  }
  static bar() {
    return runtime.safeCall(NoFreeze["foo"]())
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "NoFreeze"];
});
let NoFreeze = NoFreeze1; export default NoFreeze;
