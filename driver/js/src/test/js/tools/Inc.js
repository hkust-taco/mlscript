(() => {
  if (globalThis.Inc === undefined) {
    class Inc {
      constructor() {
      }
      inc(x) {
        return x + 1;
      }
    }
    globalThis.Inc = new Inc();
    globalThis.Inc["class"] = Inc;
  }
  return globalThis.Inc;
})();
const Inc = globalThis.Inc;
export {Inc}
