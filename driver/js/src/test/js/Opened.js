(() => {
  if (globalThis.SubModule === undefined) {
    class SubModule {
      constructor() {
      }
      hello(x) {
        return (console.log([
          "hello!",
          x
        ]));
      }
    }
    globalThis.SubModule = new SubModule();
    globalThis.SubModule["class"] = SubModule;
  }
  return globalThis.SubModule;
})();
