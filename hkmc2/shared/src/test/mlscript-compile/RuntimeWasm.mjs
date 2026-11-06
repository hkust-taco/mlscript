const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import binaryen from "binaryen";
import fs from "node:fs/promises";
let RuntimeWasm1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, mlx_str_from_utf16, lambda8, get, lambda$, lambda$1, lambda$2, mlx_str_from_utf16$, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, Capture$scope231, Capture$scope241, get$;
get$ = function get$(RuntimeWasm2, exports, tag, native1, member) {
  return () => {
    return RuntimeWasm2.facade(exports, tag, member.value, native1)
  }
};
get = function get(RuntimeWasm2, exports, tag, native1, member) {
  return RuntimeWasm2.facade(exports, tag, member.value, native1)
};
(class Capture$scope24 {
  static {
    Capture$scope241 = this
  }
  constructor(get$0, enumerable$1, configurable$2, tmp$3) {
    this.tmp$3 = tmp$3;
    this.configurable$2 = configurable$2;
    this.enumerable$1 = enumerable$1;
    this.get$0 = get$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope24"];
});
(class Capture$scope23 {
  static {
    Capture$scope231 = this
  }
  constructor(i$0) {
    this.i$0 = i$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope23"];
});
lambda$7 = (undefined, function (RuntimeWasm2, exports, tag, descriptor, native1) {
  return (...args) => {
    return lambda8(RuntimeWasm2, exports, tag, descriptor, native1, ...args)
  }
});
lambda8 = (undefined, function (RuntimeWasm2, exports, tag, descriptor, native1, ...args) {
  let padded, i, fn, args1, result, lambda$here, lambda$here1;
  padded = [
    ...args
  ];
  i = 0;
  lbl: while (true) {
    let scrut, index, scrut1, tmp;
    scrut = i < descriptor.optionalParams.length;
    if (scrut === true) {
      index = descriptor.optionalParams.at(i);
      scrut1 = args.length <= index;
      if (scrut1 === true) {
        padded[index] = null;
      }
      tmp = i + 1;
      i = tmp;
      continue lbl
    }
    break;
  }
  fn = exports[descriptor.name];
  args1 = padded;
  lambda$here = lambda$5(native1, fn, args1);
  lambda$here1 = lambda$4(native1, tag);
  result = runtime.safeCall(runtime.try_catch(lambda$here, lambda$here1));
  return result.value
});
lambda$6 = (undefined, function (RuntimeWasm2, entry, native1) {
  return (instance) => {
    return lambda7(RuntimeWasm2, entry, native1, instance)
  }
});
lambda7 = (undefined, function (RuntimeWasm2, entry, native1, instance) {
  let exports, tmp, tag, fn, result, lambda$here, lambda$here1;
  exports = instance.exports;
  tmp = ([]);
  tag = exports.mlx_exn;
  fn = exports[entry];
  lambda$here = lambda$5(native1, fn, tmp);
  lambda$here1 = lambda$4(native1, tag);
  result = runtime.safeCall(runtime.try_catch(lambda$here, lambda$here1));
  result.value;
  return exports
});
lambda$5 = (undefined, function (native1, fn, args) {
  return () => {
    return runtime.safeCall(native1.apply(fn, undefined, args))
  }
});
lambda$4 = (undefined, function (native1, tag) {
  return (error) => {
    return lambda6(native1, tag, error)
  }
});
lambda5 = (undefined, function (native1, fn, args) {
  return runtime.safeCall(native1.apply(fn, undefined, args))
});
lambda6 = (undefined, function (native1, tag, error) {
  let payload, scrut, tmp;
  if (error instanceof globalThis.WebAssembly.Exception) {
    scrut = runtime.safeCall(error.is(tag));
    if (scrut === true) {
      tmp = ([
        tag,
        0
      ]);
      payload = runtime.safeCall(native1.apply(error["getArg"], error, tmp));
      throw payload.value
    }
    throw error;
  }
  throw error;
});
lambda$3 = (undefined, function (url) {
  return (error) => {
    return lambda4(url, error)
  }
});
lambda4 = (undefined, function (url, error) {
  let scrut, tmp, tmp1, tmp2;
  scrut = error.code === "ENOENT";
  if (scrut === true) {
    tmp = "Cannot load WASM module " + url;
    tmp1 = tmp + ": compiled WAT output is missing. Rebuild before running.";
    tmp2 = ({
      cause: error
    });
    throw runtime.safeCall(globalThis.Error(tmp1, tmp2))
  }
  throw error;
});
mlx_str_from_utf16$ = function mlx_str_from_utf16$(memory, decoder) {
  return (ptr, length) => {
    let tmp;
    tmp = (new globalThis.Uint8Array(memory.buffer, ptr, length));
    return runtime.safeCall(decoder.decode(tmp))
  }
};
mlx_str_from_utf16 = function mlx_str_from_utf16(memory, decoder, ptr, length) {
  let tmp;
  tmp = (new globalThis.Uint8Array(memory.buffer, ptr, length));
  return runtime.safeCall(decoder.decode(tmp))
};
lambda3 = (undefined, function (mod) {
  return runtime.safeCall(mod.emitBinary())
});
lambda$2 = (undefined, function (folded) {
  return (mod) => {
    return lambda2(folded, mod)
  }
});
lambda2 = (undefined, function (folded, mod) {
  if (folded === true) {
    return runtime.safeCall(mod.emitText())
  }
  return runtime.safeCall(mod.emitStackIR());
});
lambda$1 = (undefined, function (description, use, mod) {
  return () => {
    return lambda(description, use, mod)
  }
});
lambda$ = (undefined, function (mod) {
  return (error) => {
    runtime.safeCall(mod.dispose());
    throw error
  }
});
lambda = (undefined, function (description, use, mod) {
  let scrut, tmp, tmp1;
  tmp = runtime.safeCall(mod.validate());
  scrut = ! tmp;
  if (scrut === true) {
    tmp1 = "Invalid generated WASM module: " + description;
    throw runtime.safeCall(globalThis.Error(tmp1))
  }
  return runtime.safeCall(use(mod));
});
lambda1 = (undefined, function (mod, error) {
  runtime.safeCall(mod.dispose());
  throw error
});
(class RuntimeWasm {
  static {
    RuntimeWasm1 = this
  }
  static #runtimes;
  static {
    let tmp;
    RuntimeWasm.RuntimeLoad = function RuntimeLoad(entry, exports) {
      return (new RuntimeLoad.class(entry, exports));
    };
    (class RuntimeLoad {
      static {
        RuntimeWasm.RuntimeLoad.class = this
      }
      constructor(entry, exports) {
        this.entry = entry;
        this.exports = exports;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "RuntimeLoad", ["entry", "exports"]];
    });
    tmp = (new globalThis.Map(undefined));
    RuntimeWasm.#runtimes = tmp;
    RuntimeWasm.Worksheet = function Worksheet(system, native1) {
      return (new Worksheet.class(system, native1));
    };
    (class Worksheet {
      static {
        RuntimeWasm.Worksheet.class = this
      }
      constructor(system, native1) {
        let system1, tmp1;
        this.system = system;
        this.native = native1;
        system1 = this.system;
        tmp1 = ({
          system: system1
        });
        this.#imports = tmp1;
      }
      #imports;
      loadFiles(paths) {
        let loadFiles$async;
        const this$Worksheet = this;
        loadFiles$async = function loadFiles$async() {
          let tmp1, pc;
          if (runtime.resumePc === -1) {
            pc = 0;
          } else {
            pc = runtime.resumePc;
            runtime.resumePc = -1;
          }
          switch (pc) {
            case 0:
              runtime.resumeValue = RuntimeWasm.loadImports("file:///", paths, this$Worksheet.#imports, this$Worksheet.native);
              if (runtime.curEffect === null) {
                pc = 2;
              } else {
                runtime.unwind(this$Worksheet.loadFiles, 2, "RuntimeWasm.mls:179:20", null, this$Worksheet, 1, 1, paths, 0);
                return runtime.Unit
              }
            case 2:
              tmp1 = runtime.resumeValue;
              runtime.resumeValue = runtime.safeCall(runtime.await(tmp1));
              if (runtime.curEffect === null) {
                pc = 1;
              } else {
                runtime.unwind(this$Worksheet.loadFiles, 1, "RuntimeWasm.mls:179:5", null, this$Worksheet, 1, 1, paths, 0);
                return runtime.Unit
              }
            case 1:
              runtime.resumeValue;
              return runtime.Unit;
          }
        };
        return runtime.toJsAsync(loadFiles$async)
      }
      run(wat, entry, pages, index) {
        let instance, result, tmp1, tmp2, tmp3;
        tmp1 = RuntimeWasm.instanceImports(this.#imports, pages);
        instance = RuntimeWasm.compileWat(wat, tmp1, "worksheet");
        tmp2 = ([]);
        result = RuntimeWasm.invoke(this.native, this.system.mlx_exn, instance.exports[entry], tmp2);
        tmp3 = "repl" + index;
        this.#imports[tmp3] = instance.exports;
        return result
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Worksheet", ["system", "native"]];
    });
  }
  static relativeUrl(path, base) {
    let tmp;
    tmp = (new globalThis.URL(path, base));
    return tmp.href
  }
  static withWat(wat, description, use) {
    let mod, result, lambda$here, lambda$here1;
    mod = runtime.safeCall(binaryen.parseText(wat, binaryen.Features.All));
    lambda$here = lambda$1(description, use, mod);
    lambda$here1 = lambda$(mod);
    result = runtime.safeCall(runtime.try_catch(lambda$here, lambda$here1));
    runtime.safeCall(mod.dispose());
    return result
  }
  static formatWat(wat, folded) {
    let lambda$here;
    lambda$here = lambda$2(folded);
    return RuntimeWasm.withWat(wat, "worksheet", lambda$here)
  }
  static instantiateBinary(binary, imports) {
    let scrut, tmp;
    scrut = runtime.safeCall(globalThis.WebAssembly.validate(binary));
    if (scrut === true) {
      tmp = (new globalThis.WebAssembly.Module(binary));
      return (new globalThis.WebAssembly.Instance(tmp, imports))
    }
    return runtime.assertFail("mlscript-compile/RuntimeWasm.mls", "66");
  }
  static compileWat(wat, imports, description) {
    let binary;
    binary = RuntimeWasm.withWat(wat, description, lambda3);
    return RuntimeWasm.instantiateBinary(binary, imports)
  }
  static instanceImports(imports, pages) {
    let memory, decoder, mlx_str_from_utf161, system, tmp;
    tmp = ({
      initial: pages
    });
    memory = (new globalThis.WebAssembly.Memory(tmp));
    decoder = (new globalThis.TextDecoder("utf-16le"));
    mlx_str_from_utf161 = mlx_str_from_utf16$(memory, decoder);
    system = ({
      ...imports.system,
      mem: memory,
      mlx_str_from_utf16: mlx_str_from_utf161
    });
    return ({
      ...imports,
      system: system
    })
  }
  static instantiate(url, imports, pages) {
    let instantiate$async;
    instantiate$async = function instantiate$async() {
      let wat, tmp, tmp1, tmp2, tmp3, lambda$here, pc;
      if (runtime.resumePc === -1) {
        pc = 0;
      } else {
        let saveOffset;
        pc = runtime.resumePc;
        saveOffset = runtime.resumeIdx;
        wat = runtime.resumeArr.at(saveOffset);
        runtime.resumePc = -1;
      }
      switch (pc) {
        case 0:
          tmp = (new globalThis.URL(url, undefined));
          runtime.resumeValue = runtime.safeCall(fs.readFile(tmp, "utf8"));
          if (runtime.curEffect === null) {
            pc = 4;
          } else {
            runtime.unwind(RuntimeWasm.instantiate, 4, "RuntimeWasm.mls:85:28", null, RuntimeWasm, 1, 3, url, imports, pages, 1, wat);
            return runtime.Unit
          }
        case 4:
          tmp1 = runtime.resumeValue;
          lambda$here = lambda$3(url);
          runtime.resumeValue = runtime.safeCall(tmp1.catch(lambda$here));
          if (runtime.curEffect === null) {
            pc = 3;
          } else {
            runtime.unwind(RuntimeWasm.instantiate, 3, "RuntimeWasm.mls:85:28", null, RuntimeWasm, 1, 3, url, imports, pages, 1, wat);
            return runtime.Unit
          }
        case 3:
          tmp2 = runtime.resumeValue;
          runtime.resumeValue = runtime.safeCall(runtime.await(tmp2));
          if (runtime.curEffect === null) {
            pc = 2;
          } else {
            runtime.unwind(RuntimeWasm.instantiate, 2, "RuntimeWasm.mls:85:13", null, RuntimeWasm, 1, 3, url, imports, pages, 1, wat);
            return runtime.Unit
          }
        case 2:
          wat = runtime.resumeValue;
          runtime.resumeValue = RuntimeWasm.instanceImports(imports, pages);
          if (runtime.curEffect === null) {
            pc = 1;
          } else {
            runtime.unwind(RuntimeWasm.instantiate, 1, "RuntimeWasm.mls:89:19", null, RuntimeWasm, 1, 3, url, imports, pages, 1, wat);
            return runtime.Unit
          }
        case 1:
          tmp3 = runtime.resumeValue;
          return RuntimeWasm.compileWat(wat, tmp3, url);
      }
    };
    return runtime.toJsAsync(instantiate$async)
  }
  static invoke(native1, tag, fn, args) {
    let result, lambda$here, lambda$here1;
    lambda$here = lambda$5(native1, fn, args);
    lambda$here1 = lambda$4(native1, tag);
    result = runtime.safeCall(runtime.try_catch(lambda$here, lambda$here1));
    return result.value
  }
  static loadRuntime(url, entry, native1) {
    let scrut, loaded, scrut1, promise, tmp, tmp1, tmp2, lambda$here;
    scrut = runtime.safeCall(RuntimeWasm.#runtimes.has(url));
    if (scrut === true) {
      loaded = runtime.safeCall(RuntimeWasm.#runtimes.get(url));
      scrut1 = loaded.entry === entry;
      if (scrut1 === true) {
        return loaded.exports
      }
      return runtime.assertFail("mlscript-compile/RuntimeWasm.mls", "108");
    }
    tmp = ({});
    tmp1 = RuntimeWasm.instantiate(url, tmp, 0);
    lambda$here = lambda$6(RuntimeWasm, entry, native1);
    promise = runtime.safeCall(tmp1.then(lambda$here));
    tmp2 = (new RuntimeWasm.RuntimeLoad.class(entry, promise));
    runtime.safeCall(RuntimeWasm.#runtimes.set(url, tmp2));
    return promise;
  }
  static loadImports(base, paths, imports, native1) {
    let loadImports$async;
    loadImports$async = function loadImports$async() {
      let i, scrut, loaded, tmp, tmp1, tmp2, tmp3, pc;
      if (runtime.resumePc === -1) {
        pc = 0;
      } else {
        let saveOffset;
        pc = runtime.resumePc;
        saveOffset = runtime.resumeIdx;
        i = runtime.resumeArr.at(saveOffset);
        runtime.resumePc = -1;
      }
      main: while (true) {
        switch (pc) {
          case 6:
            return imports;
          case 5:
            tmp = runtime.resumeValue;
            runtime.resumeValue = runtime.safeCall(native1.importModule(tmp));
            if (runtime.curEffect === null) {
              pc = 4;
            } else {
              runtime.unwind(RuntimeWasm.loadImports, 4, "RuntimeWasm.mls:123:33", null, RuntimeWasm, 1, 4, base, paths, imports, native1, 1, i);
              return runtime.Unit
            }
          case 4:
            tmp1 = runtime.resumeValue;
            runtime.resumeValue = runtime.safeCall(runtime.await(tmp1));
            if (runtime.curEffect === null) {
              pc = 3;
            } else {
              runtime.unwind(RuntimeWasm.loadImports, 3, "RuntimeWasm.mls:123:18", null, RuntimeWasm, 1, 4, base, paths, imports, native1, 1, i);
              return runtime.Unit
            }
          case 3:
            loaded = runtime.resumeValue;
            tmp2 = "module" + i;
            imports[tmp2] = loaded.wasmExports;
            pc = 2;
          case 2:
            tmp3 = i + 1;
            i = tmp3;
            pc = 1;
            continue main;
          case 0:
            i = 0;
            pc = 1;
          case 1:
            scrut = i < paths.length;
            if (scrut === true) {
              runtime.resumeValue = RuntimeWasm.relativeUrl(paths.at(i), base);
              if (runtime.curEffect === null) {
                pc = 5;
                continue main
              }
              runtime.unwind(RuntimeWasm.loadImports, 5, "RuntimeWasm.mls:123:53", null, RuntimeWasm, 1, 4, base, paths, imports, native1, 1, i);
              return runtime.Unit;
            }
            pc = 6;
            continue main;
        }
        break;
      }
    };
    return runtime.toJsAsync(loadImports$async)
  }
  static #callable(exports, tag, descriptor, native1) {
    return lambda$7(RuntimeWasm, exports, tag, descriptor, native1)
  }
  static facade(exports, tag, descriptor, native1) {
    let scrut, fn, scrut1, scrut2, scrut3, result, tmp, scope23$cap;
    scope23$cap = new Capture$scope231(undefined);
    scrut = descriptor.kind === "function";
    if (scrut === true) {
      fn = RuntimeWasm.#callable(exports, tag, descriptor, native1);
      scrut1 = descriptor.constructor !== null;
      if (scrut1 === true) {
        tmp = RuntimeWasm.#callable(exports, tag, descriptor.constructor, native1);
        fn["class"] = tmp;
        return fn
      }
      return fn;
    }
    scrut2 = descriptor.kind === "global";
    if (scrut2 === true) {
      return exports[descriptor.name].value
    }
    scrut3 = descriptor.kind === "namespace";
    if (scrut3 === true) {
      result = ({});
      scope23$cap.i$0 = 0;
      lbl: while (true) {
        let scrut4, member, property, scrut5, value, tmp1, scope24$cap;
        scope24$cap = new Capture$scope241(undefined, undefined, undefined, undefined);
        scrut4 = scope23$cap.i$0 < descriptor.members.length;
        if (scrut4 === true) {
          member = descriptor.members.at(scope23$cap.i$0);
          scrut5 = member.getter;
          if (scrut5 === true) {
            scope24$cap.get$0 = get$(RuntimeWasm, exports, tag, native1, member);
            scope24$cap.enumerable$1 = true;
            scope24$cap.configurable$2 = true;
            scope24$cap.tmp$3 = ({
              get: scope24$cap.get$0,
              enumerable: scope24$cap.enumerable$1,
              configurable: scope24$cap.configurable$2
            });
          } else {
            value = RuntimeWasm.facade(exports, tag, member.value, native1);
            scope24$cap.tmp$3 = ({
              value: value,
              writable: true,
              enumerable: true,
              configurable: true
            });
          }
          property = scope24$cap.tmp$3;
          runtime.safeCall(globalThis.Object.defineProperty(result, member.name, property));
          tmp1 = scope23$cap.i$0 + 1;
          scope23$cap.i$0 = tmp1;
          continue lbl
        }
        break;
      }
      return result
    }
    return runtime.assertFail("mlscript-compile/RuntimeWasm.mls", "149");
  }
  static loadModule(base, metadata, native1) {
    let loadModule$async;
    loadModule$async = function loadModule$async() {
      let system, imports, instance, exports, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, pc;
      if (runtime.resumePc === -1) {
        pc = 0;
      } else {
        let saveOffset;
        pc = runtime.resumePc;
        saveOffset = runtime.resumeIdx;
        system = runtime.resumeArr.at(saveOffset);
        saveOffset = saveOffset + 1;
        imports = runtime.resumeArr.at(saveOffset);
        saveOffset = saveOffset + 1;
        exports = runtime.resumeArr.at(saveOffset);
        runtime.resumePc = -1;
      }
      main: while (true) {
        switch (pc) {
          case 0:
            runtime.resumeValue = RuntimeWasm.relativeUrl(metadata.runtime.path, base);
            if (runtime.curEffect === null) {
              pc = 11;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 11, "RuntimeWasm.mls:162:43", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 11:
            tmp = runtime.resumeValue;
            runtime.resumeValue = RuntimeWasm.loadRuntime(tmp, metadata.runtime.entry, native1);
            if (runtime.curEffect === null) {
              pc = 10;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 10, "RuntimeWasm.mls:162:31", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 10:
            tmp1 = runtime.resumeValue;
            runtime.resumeValue = runtime.safeCall(runtime.await(tmp1));
            if (runtime.curEffect === null) {
              pc = 9;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 9, "RuntimeWasm.mls:162:16", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 9:
            system = runtime.resumeValue;
            tmp2 = ({
              system: system
            });
            runtime.resumeValue = RuntimeWasm.loadImports(base, metadata.dependencies, tmp2, native1);
            if (runtime.curEffect === null) {
              pc = 8;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 8, "RuntimeWasm.mls:163:32", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 8:
            tmp3 = runtime.resumeValue;
            runtime.resumeValue = runtime.safeCall(runtime.await(tmp3));
            if (runtime.curEffect === null) {
              pc = 7;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 7, "RuntimeWasm.mls:163:17", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 7:
            imports = runtime.resumeValue;
            runtime.resumeValue = RuntimeWasm.relativeUrl(metadata.wat, base);
            if (runtime.curEffect === null) {
              pc = 6;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 6, "RuntimeWasm.mls:164:45", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 6:
            tmp4 = runtime.resumeValue;
            runtime.resumeValue = RuntimeWasm.instantiate(tmp4, imports, metadata.pages);
            if (runtime.curEffect === null) {
              pc = 5;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 5, "RuntimeWasm.mls:164:33", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 5:
            tmp5 = runtime.resumeValue;
            runtime.resumeValue = runtime.safeCall(runtime.await(tmp5));
            if (runtime.curEffect === null) {
              pc = 4;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 4, "RuntimeWasm.mls:164:18", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 4:
            instance = runtime.resumeValue;
            exports = instance.exports;
            tmp6 = ([]);
            runtime.resumeValue = RuntimeWasm.invoke(native1, system.mlx_exn, exports[metadata.entry], tmp6);
            if (runtime.curEffect === null) {
              pc = 3;
            } else {
              runtime.unwind(RuntimeWasm.loadModule, 3, "RuntimeWasm.mls:166:3", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
              return runtime.Unit
            }
          case 3:
            runtime.resumeValue;
            scrut = metadata.export.kind === "undefined";
            if (scrut === true) {
              tmp7 = undefined;
              pc = 1;
              continue main
            }
            runtime.resumeValue = RuntimeWasm.facade(exports, system.mlx_exn, metadata.export, native1);
            if (runtime.curEffect === null) {
              pc = 2;
              continue main
            }
            runtime.unwind(RuntimeWasm.loadModule, 2, "RuntimeWasm.mls:171:10", null, RuntimeWasm, 1, 3, base, metadata, native1, 3, system, imports, exports);
            return runtime.Unit;
          case 2:
            tmp7 = runtime.resumeValue;
            pc = 1;
            continue main;
          case 1:
            return ({
              wasmExports: exports,
              defaultExport: tmp7
            });
        }
        break;
      }
    };
    return runtime.toJsAsync(loadModule$async)
  }
  static worksheet(url, entry, native1) {
    let worksheet$async;
    worksheet$async = function worksheet$async() {
      let system, tmp, pc;
      if (runtime.resumePc === -1) {
        pc = 0;
      } else {
        pc = runtime.resumePc;
        runtime.resumePc = -1;
      }
      switch (pc) {
        case 0:
          runtime.resumeValue = RuntimeWasm.loadRuntime(url, entry, native1);
          if (runtime.curEffect === null) {
            pc = 2;
          } else {
            runtime.unwind(RuntimeWasm.worksheet, 2, "RuntimeWasm.mls:192:31", null, RuntimeWasm, 1, 3, url, entry, native1, 0);
            return runtime.Unit
          }
        case 2:
          tmp = runtime.resumeValue;
          runtime.resumeValue = runtime.safeCall(runtime.await(tmp));
          if (runtime.curEffect === null) {
            pc = 1;
          } else {
            runtime.unwind(RuntimeWasm.worksheet, 1, "RuntimeWasm.mls:192:16", null, RuntimeWasm, 1, 3, url, entry, native1, 0);
            return runtime.Unit
          }
        case 1:
          system = runtime.resumeValue;
          return (new RuntimeWasm.Worksheet.class(system, native1));
      }
    };
    return runtime.toJsAsync(worksheet$async)
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "RuntimeWasm"];
});
export { RuntimeWasm1 as _$_modulePrivate_$_RuntimeWasm };
export { lambda as _$_modulePrivate_$_lambda };
export { lambda1 as _$_modulePrivate_$_lambda1 };
export { lambda2 as _$_modulePrivate_$_lambda2 };
export { lambda3 as _$_modulePrivate_$_lambda3 };
export { lambda4 as _$_modulePrivate_$_lambda4 };
export { lambda5 as _$_modulePrivate_$_lambda5 };
export { lambda6 as _$_modulePrivate_$_lambda6 };
export { lambda7 as _$_modulePrivate_$_lambda7 };
export { mlx_str_from_utf16 as _$_modulePrivate_$_mlx_str_from_utf16 };
export { lambda8 as _$_modulePrivate_$_lambda8 };
export { get as _$_modulePrivate_$_get };
export { lambda$ as _$_modulePrivate_$_lambda$ };
export { lambda$1 as _$_modulePrivate_$_lambda$1 };
export { lambda$2 as _$_modulePrivate_$_lambda$2 };
export { mlx_str_from_utf16$ as _$_modulePrivate_$_mlx_str_from_utf16$ };
export { lambda$3 as _$_modulePrivate_$_lambda$3 };
export { lambda$4 as _$_modulePrivate_$_lambda$4 };
export { lambda$5 as _$_modulePrivate_$_lambda$5 };
export { lambda$6 as _$_modulePrivate_$_lambda$6 };
export { lambda$7 as _$_modulePrivate_$_lambda$7 };
export { Capture$scope231 as _$_modulePrivate_$_Capture$scope23 };
export { Capture$scope241 as _$_modulePrivate_$_Capture$scope24 };
export { get$ as _$_modulePrivate_$_get$ };
export default RuntimeWasm1;
