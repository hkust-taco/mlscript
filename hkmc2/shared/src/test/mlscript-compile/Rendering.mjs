import runtime from "./Runtime.mjs";
let Rendering1;
(class Rendering {
  static {
    Rendering1 = Rendering;
  }
  static pass1(f) {
    return (...xs) => {
      return runtime.safeCall(f(xs[0]))
    }
  } 
  static pass2(f1) {
    return (...xs) => {
      return runtime.safeCall(f1(xs[0], xs[1]))
    }
  } 
  static pass3(f2) {
    return (...xs) => {
      return runtime.safeCall(f2(xs[0], xs[1], xs[2]))
    }
  } 
  static passing(f3, ...args) {
    return f3.bind(null, ...args)
  } 
  static map(f4) {
    return (...xs) => {
      let tmp;
      tmp = Rendering.pass1(f4);
      return runtime.safeCall(xs.map(tmp))
    }
  } 
  static fold(f5) {
    return (init, ...rest) => {
      let i, len, scrut, tmp, tmp1, tmp2, tmp3;
      i = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i < len;
        if (scrut === true) {
          tmp = runtime.safeCall(rest.at(i));
          tmp1 = runtime.safeCall(f5(init, tmp));
          init = tmp1;
          tmp2 = i + 1;
          i = tmp2;
          tmp3 = runtime.Unit;
          continue tmp4;
        } else {
          tmp3 = runtime.Unit;
        }
        break;
      }
      return init
    }
  } 
  static interleave(sep) {
    return (...args1) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
      scrut2 = args1.length === 0;
      if (scrut2 === true) {
        return []
      } else {
        tmp = args1.length * 2;
        tmp1 = tmp - 1;
        tmp2 = globalThis.Array(tmp1);
        res = tmp2;
        len = args1.length;
        i = 0;
        tmp8: while (true) {
          scrut = i < len;
          if (scrut === true) {
            tmp3 = i * 2;
            idx = tmp3;
            res[idx] = args1[i];
            tmp4 = i + 1;
            i = tmp4;
            scrut1 = i < len;
            if (scrut1 === true) {
              tmp5 = idx + 1;
              res[tmp5] = sep;
              tmp6 = runtime.Unit;
            } else {
              tmp6 = runtime.Unit;
            }
            tmp7 = tmp6;
            continue tmp8;
          } else {
            tmp7 = runtime.Unit;
          }
          break;
        }
        return res
      }
    }
  } 
  static render(arg) {
    let ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6;
    if (arg === undefined) {
      return "undefined"
    } else if (arg === null) {
      return "null"
    } else if (arg instanceof globalThis.Array) {
      lambda = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp = Rendering.fold(lambda);
      tmp1 = Rendering.interleave(", ");
      tmp2 = Rendering.map(Rendering.render);
      tmp3 = runtime.safeCall(tmp2(...arg));
      tmp4 = runtime.safeCall(tmp1(...tmp3));
      return runtime.safeCall(tmp("[", ...tmp4, "]"))
    } else if (typeof arg === 'string') {
      return runtime.safeCall(globalThis.JSON.stringify(arg))
    } else if (arg instanceof globalThis.Set) {
      lambda1 = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp5 = Rendering.fold(lambda1);
      tmp6 = Rendering.interleave(", ");
      tmp7 = Rendering.map(Rendering.render);
      tmp8 = runtime.safeCall(tmp7(...arg));
      tmp9 = runtime.safeCall(tmp6(...tmp8));
      return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
    } else if (arg instanceof globalThis.Map) {
      lambda2 = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp10 = Rendering.fold(lambda2);
      tmp11 = Rendering.interleave(", ");
      tmp12 = Rendering.map(Rendering.render);
      tmp13 = runtime.safeCall(tmp12(...arg));
      tmp14 = runtime.safeCall(tmp11(...tmp13));
      return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
    } else if (arg instanceof globalThis.Function) {
      p = globalThis.Object.getOwnPropertyDescriptor(arg, "prototype");
      if (p instanceof globalThis.Object) {
        scrut1 = p["writable"];
        if (scrut1 === true) {
          tmp15 = true;
        } else {
          tmp15 = false;
        }
      } else {
        tmp15 = false;
      }
      if (p === undefined) {
        tmp16 = true;
      } else {
        tmp16 = false;
      }
      scrut2 = tmp15 || tmp16;
      if (scrut2 === true) {
        scrut3 = arg.name;
        if (scrut3 === "") {
          tmp17 = "";
        } else {
          nme = scrut3;
          tmp17 = " " + nme;
        }
        tmp18 = "[function" + tmp17;
        return tmp18 + "]"
      } else {
        scrut = arg.constructor.name;
        if (scrut === "Object") {
          tmp19 = runtime.safeCall(globalThis.Object.entries(arg));
          es = tmp19;
          lambda3 = (undefined, function (arg1, arg2) {
            return arg1 + arg2
          });
          tmp20 = Rendering.fold(lambda3);
          tmp21 = Rendering.interleave(", ");
          lambda4 = (undefined, function (caseScrut) {
            let first1, first0, k, v, tmp35, tmp36;
            if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
              first0 = caseScrut[0];
              first1 = caseScrut[1];
              k = first0;
              v = first1;
              tmp35 = k + ": ";
              tmp36 = Rendering.render(v);
              return tmp35 + tmp36
            } else {
              throw new globalThis.Error("match error");
            }
          });
          tmp22 = lambda4;
          tmp23 = Rendering.map(tmp22);
          tmp24 = runtime.safeCall(tmp23(...es));
          tmp25 = runtime.safeCall(tmp21(...tmp24));
          return runtime.safeCall(tmp20("{", ...tmp25, "}"))
        } else {
          return globalThis.String(arg)
        }
      }
    } else if (arg instanceof globalThis.Object) {
      scrut = arg.constructor.name;
      if (scrut === "Object") {
        tmp26 = runtime.safeCall(globalThis.Object.entries(arg));
        es = tmp26;
        lambda5 = (undefined, function (arg1, arg2) {
          return arg1 + arg2
        });
        tmp27 = Rendering.fold(lambda5);
        tmp28 = Rendering.interleave(", ");
        lambda6 = (undefined, function (caseScrut) {
          let first1, first0, k, v, tmp35, tmp36;
          if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
            first0 = caseScrut[0];
            first1 = caseScrut[1];
            k = first0;
            v = first1;
            tmp35 = k + ": ";
            tmp36 = Rendering.render(v);
            return tmp35 + tmp36
          } else {
            throw new globalThis.Error("match error");
          }
        });
        tmp29 = lambda6;
        tmp30 = Rendering.map(tmp29);
        tmp31 = runtime.safeCall(tmp30(...es));
        tmp32 = runtime.safeCall(tmp28(...tmp31));
        return runtime.safeCall(tmp27("{", ...tmp32, "}"))
      } else {
        return globalThis.String(arg)
      }
    } else {
      ts = arg["toString"];
      if (ts === undefined) {
        tmp33 = typeof arg;
        tmp34 = "[" + tmp33;
        return tmp34 + "]"
      } else {
        return runtime.safeCall(ts.call(arg))
      }
    }
  }
  static toString() { return "Rendering"; }
});
let Rendering = Rendering1; export default Rendering;
