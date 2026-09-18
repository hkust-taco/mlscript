const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import Term from "./Term.mjs";
let Predef1, lambda, lambda1, lambda2, lambda$, lambda$1, lambda$2;
lambda$2 = (undefined, function (Predef2) {
  return (acc, x) => {
    return lambda2(Predef2, acc, x)
  }
});
lambda2 = (undefined, function (Predef2, acc, x) {
  let tmp, args;
  if (typeof x === 'string') {
    tmp = true;
  } else {
    tmp = false;
  }
  args = [
    tmp
  ];
  runtime.safeCall(Predef2.js_assert(...args));
  return acc + x
});
lambda$1 = (undefined, function (Predef2, b) {
  return (a, i) => {
    let tmp;
    tmp = runtime.safeCall(b.at(i));
    return Predef2.equals(a, tmp)
  }
});
lambda$ = (undefined, function (Predef2, a, b) {
  return (field) => {
    return lambda(Predef2, a, b, field)
  }
});
lambda1 = (undefined, function (Predef2, b, a, i) {
  let tmp;
  tmp = runtime.safeCall(b.at(i));
  return Predef2.equals(a, tmp)
});
lambda = (undefined, function (Predef2, a, b, field) {
  let scrut, scrut1;
  scrut = field !== null;
  if (scrut === true) {
    scrut1 = Predef2.equals(a[field], b[field]);
    if (scrut1 === true) {
      return true
    }
    return false;
  }
  return false;
});
(class Predef {
  static {
    Predef1 = this
  }
  static {
    (class Symbols {
      static {
        new this
      }
      constructor() {
        Predef.Symbols = this;
        this.prettyPrint = RuntimeJS.symbols.prettyPrint;
        this.definitionMetadata = RuntimeJS.symbols.definitionMetadata;
        Object.defineProperty(this, "class", {
          value: Symbols
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Symbols"];
    });
    (class Sub {
      static {
        Predef.Sub = this
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Sub"];
    });
    (class Eq extends Predef.Sub {
      static {
        Predef.Eq = this
      }
      constructor() {
        super();
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Eq"];
    });
    (class Refl extends Predef.Eq {
      static {
        new this
      }
      constructor() {
        super();
        Predef.Refl = this;
        Object.defineProperty(this, "class", {
          value: Refl
        });
        globalThis.Object.freeze(this);
      }
      apply(x) {
        return x
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Refl"];
    });
    Predef.js_assert = globalThis.console["assert"];
    Predef.foldl = Predef.fold;
    (class meta {
      static {
        Predef.meta = this
      }
      static codegen(t, file) {
        return runtime.safeCall(Term.codegen(t, file))
      }
      static print(t) {
        return runtime.safeCall(Term.print(t))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "meta"];
    });
  }
  static id(x) {
    return x
  }
  static hide(x) {
    return x
  }
  static get maybe() {
    return Predef.hide(true);
  }
  static apply(f, ...args) {
    return runtime.safeCall(f(...args))
  }
  static pipeInto(x, f) {
    return runtime.safeCall(f(x))
  }
  static pipeFrom(f, x) {
    return runtime.safeCall(f(x))
  }
  static pipeIntoHi(x, f) {
    return runtime.safeCall(f(x))
  }
  static pipeFromHi(f, x) {
    return runtime.safeCall(f(x))
  }
  static tap(x, f) {
    runtime.safeCall(f(x));
    return x
  }
  static pat(f, x) {
    runtime.safeCall(f(x));
    return x
  }
  static alsoDo(x, eff) {
    return x
  }
  static andThen(f, g) {
    return (x) => {
      let tmp;
      tmp = runtime.safeCall(f(x));
      return runtime.safeCall(g(tmp))
    }
  }
  static compose(f, g) {
    return (x) => {
      let tmp;
      tmp = runtime.safeCall(g(x));
      return runtime.safeCall(f(tmp))
    }
  }
  static passTo(receiver, f) {
    return (...args) => {
      return runtime.safeCall(f(receiver, ...args))
    }
  }
  static passToLo(receiver, f) {
    return (...args) => {
      return runtime.safeCall(f(receiver, ...args))
    }
  }
  static call(receiver, f) {
    return (...args) => {
      return runtime.safeCall(f.call(receiver, ...args))
    }
  }
  static equals(a, b) {
    let scrut, scrut1, scrut2, ac, scrut3, md, scrut4, scrut5, scrut6, scrut7, scrut8, scrut9, lambda$here, lambda$here1;
    scrut = a === b;
    if (scrut === true) {
      return true
    }
    if (a instanceof globalThis.Array) {
      if (b instanceof globalThis.Array) {
        scrut1 = a.length === b.length;
        if (scrut1 === true) {
          lambda$here = lambda$1(Predef, b);
          return runtime.safeCall(a.every(lambda$here))
        }
      }
    }
    scrut2 = a !== undefined;
    if (scrut2 === true) {
      scrut9 = a !== null;
      if (scrut9 === true) {
        scrut8 = b !== undefined;
        if (scrut8 === true) {
          scrut7 = b !== null;
          if (scrut7 === true) {
            ac = a.constructor;
            scrut3 = ac !== undefined;
            if (scrut3 === true) {
              scrut6 = ac === b.constructor;
              if (scrut6 === true) {
                md = ac[Predef.Symbols.definitionMetadata];
                scrut4 = md !== undefined;
                if (scrut4 === true) {
                  lambda$here1 = lambda$(Predef, a, b);
                  scrut5 = runtime.safeCall(md[2].every(lambda$here1));
                  if (scrut5 === true) {
                    return true
                  }
                  return false;
                }
                return false;
              }
              return false;
            }
            return false;
          }
          return false;
        }
        return false;
      }
      return false;
    }
    return false;
  }
  static nequals(a, b) {
    let tmp;
    tmp = Predef.equals(a, b);
    return ! tmp
  }
  static get pass1() {
    return Rendering.pass1;
  }
  static get pass2() {
    return Rendering.pass2;
  }
  static get pass3() {
    return Rendering.pass3;
  }
  static get passing() {
    return Rendering.passing;
  }
  static get map() {
    return Rendering.map;
  }
  static get fold() {
    return Rendering.fold;
  }
  static get interleave() {
    return Rendering.interleave;
  }
  static get render() {
    return Rendering.render;
  }
  static print(...xs) {
    let callPrefix, tmp;
    callPrefix = runtime.safeCall(Predef.map(Predef.renderAsStr));
    tmp = runtime.safeCall(callPrefix(...xs));
    return runtime.safeCall(globalThis.console.log(...tmp))
  }
  static renderAsStr(arg) {
    if (typeof arg === 'string') {
      return arg
    }
    return runtime.safeCall(Predef.render(arg));
  }
  static check(...args) {
    return runtime.safeCall(Predef.js_assert(...args))
  }
  static notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw runtime.safeCall(globalThis.Error(tmp))
  }
  static get notImplementedError() {
    throw runtime.safeCall(globalThis.Error("Not implemented"));
  }
  static tuple(...xs) {
    return xs
  }
  static mkSet(...xs) {
    return globalThis.Object.freeze(new globalThis.Set(xs))
  }
  static foldr(f) {
    return (first, ...rest) => {
      let len, scrut, i, init;
      len = rest.length;
      scrut = len === 0;
      if (scrut === true) {
        return first
      }
      i = len - 1;
      init = runtime.safeCall(rest.at(i));
      lbl: while (true) {
        let scrut1, tmp, tmp1, tmp2;
        scrut1 = i > 0;
        if (scrut1 === true) {
          tmp = i - 1;
          i = tmp;
          tmp1 = runtime.safeCall(rest.at(tmp));
          tmp2 = runtime.safeCall(f(tmp1, init));
          init = tmp2;
          continue lbl
        }
        break;
      }
      return runtime.safeCall(f(first, init));
    }
  }
  static mkStr(...xs) {
    let callPrefix, lambda$here;
    lambda$here = lambda$2(Predef);
    callPrefix = runtime.safeCall(Predef.fold(lambda$here));
    return runtime.safeCall(callPrefix(...xs))
  }
  static use(instance) {
    return instance
  }
  static enterHandleBlock(handler, body) {
    return runtime.safeCall(runtime.enterHandleBlock(handler, body))
  }
  static raiseUnhandledEffect() {
    return runtime.safeCall(runtime.mkEffect(runtime.FatalEffect, null))
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Predef"];
});
export { Predef1 as _$_modulePrivate_$_Predef };
export { lambda as _$_modulePrivate_$_lambda };
export { lambda1 as _$_modulePrivate_$_lambda1 };
export { lambda2 as _$_modulePrivate_$_lambda2 };
export { lambda$ as _$_modulePrivate_$_lambda$ };
export { lambda$1 as _$_modulePrivate_$_lambda$1 };
export { lambda$2 as _$_modulePrivate_$_lambda$2 };
let Predef = Predef1; export default Predef;
