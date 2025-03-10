import runtime from "./Runtime.mjs";
let render;
render = function render(arg) {
  let ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (arg === undefined) {
    return "undefined"
  } else if (arg === null) {
    return "null"
  } else if (arg instanceof globalThis.Array) {
    /* error */
  } else if (typeof arg === 'string') {
    return runtime.safeCall(globalThis.JSON.stringify(arg))
  } else if (arg instanceof globalThis.Set) {
    /* error */
  } else if (arg instanceof globalThis.Map) {
    /* error */
  } else if (arg instanceof globalThis.Function) {
    p = globalThis.Object.getOwnPropertyDescriptor(arg, "prototype");
    if (p instanceof globalThis.Object) {
      scrut1 = p["writable"];
      if (scrut1 === true) {
        tmp = true;
      } else {
        tmp = false;
      }
    } else {
      tmp = false;
    }
    if (p === undefined) {
      tmp1 = true;
    } else {
      tmp1 = false;
    }
    scrut2 = tmp || tmp1;
    if (scrut2 === true) {
      scrut3 = arg.name;
      if (scrut3 === "") {
        tmp2 = "";
      } else {
        nme = scrut3;
        tmp2 = " " + nme;
      }
      tmp3 = "[function" + tmp2;
      return tmp3 + "]"
    } else {
      scrut = arg.constructor.name;
      if (scrut === "Object") {
        tmp4 = runtime.safeCall(globalThis.Object.entries(arg));
        es = tmp4;
        /* error */
      } else {
        return globalThis.String(arg)
      }
    }
  } else if (arg instanceof globalThis.Object) {
    scrut = arg.constructor.name;
    if (scrut === "Object") {
      tmp5 = runtime.safeCall(globalThis.Object.entries(arg));
      es = tmp5;
      /* error */
    } else {
      return globalThis.String(arg)
    }
  } else {
    ts = arg["toString"];
    if (ts === undefined) {
      tmp6 = typeof arg;
      tmp7 = "[" + tmp6;
      return tmp7 + "]"
    } else {
      return runtime.safeCall(ts.call(arg))
    }
  }
};