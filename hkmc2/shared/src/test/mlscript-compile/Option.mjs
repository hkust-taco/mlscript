const Option = new class Option {
  constructor() {
    this.Some = class Some {
      constructor(value) {
        this.value = value;
        
      }
      toString() { return "Some(" + this.value + ")"; }
    };
    this.None = new class None {
      constructor() {
        
      }
      toString() { return "None"; }
    };
    this.Both = class Both {
      constructor(fst, snd) {
        this.fst = fst;
        this.snd = snd;
        
      }
      toString() { return "Both(" + this.fst + ", " + this.snd + ")"; }
    };
  }
  isDefined(x) {
    if (x instanceof this.Some) {
      return true
    } else {
      if (x === this.None) {
        return false
      } else {
        throw new globalThis.Error("match error")
      }
    }
  } 
  test() {
    return 2134
  }
  toString() { return "Option"; }
};
undefined
export default Option;
