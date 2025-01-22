import Predef from "./Predef.mjs";
let Option1;
const Option$class = class Option {
  constructor() {
    this.Some = function Some(value1) { return new Some.class(value1); };
    this.Some.class = class Some {
      constructor(value) {
        this.value = value;
      }
      toString() { return "Some(" + this.value + ")"; }
    };
    const None$class = class None {
      constructor() {}
      toString() { return "None"; }
    };
    this.None = new None$class;
    this.None.class = None$class;
    this.Both = function Both(fst1, snd1) { return new Both.class(fst1, snd1); };
    this.Both.class = class Both {
      constructor(fst, snd) {
        this.fst = fst;
        this.snd = snd;
      }
      toString() { return "Both(" + this.fst + ", " + this.snd + ")"; }
    };
  }
  isDefined(x) {
    if (x instanceof this.Some.class) {
      return true;
    } else {
      if (x instanceof this.None.class) {
        return false;
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  test() {
    return Predef.pipeInto(2134, Predef.print);
  }
  toString() { return "Option"; }
}; Option1 = new Option$class;
Option1.class = Option$class;
null
let Option = Option1; export default Option;
