function log(x) {
  return console.info(x);
}
(() => {
  if (globalThis.Opened === undefined) {
    class Opened {
      constructor() {
      }
      hello(x) {
        return (log([
          "hello!",
          x
        ]));
      }
    }
    globalThis.Opened = new Opened();
    globalThis.Opened["class"] = Opened;
  }
  return globalThis.Opened;
})();
const Opened = globalThis.Opened;
export {Opened}
