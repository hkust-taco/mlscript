import Predef from "./Predef.mjs";
let Option1;
Option1 = class Option {
  static {
    this.Some = function Some(value1) { return new Some.class(value1); };
    this.Some.class = class Some {
      constructor(value) {
        this.value = value;
      }
      toString() { return "Some(" + globalThis.Predef.render(this.value) + ")"; }
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
      toString() { return "Both(" + globalThis.Predef.render(this.fst) + ", " + globalThis.Predef.render(this.snd) + ")"; }
    };
  }
  static isDefined(x) {
    if (x instanceof Option.Some.class) {
      return true;
    } else {
      if (x instanceof Option.None.class) {
        return false;
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static test() {
    return Predef.pipeInto(2134, Predef.print);
  }
  static toString() { return "Option"; }
};
null
let Option = Option1; export default Option;
