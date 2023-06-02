import * as MyPrint from "./MyPrint.js"

const TS = new class TS {
  #tspt;
  get tspt() { return this.#tspt; }
  #printer;
  get printer() { return this.#printer; }
  constructor() {
  }
  $init() {
    this.#tspt = MyPrint.DatePrint;
    const tspt = this.#tspt;
    this.#printer = new tspt("love from ts");
    const printer = this.#printer;
    printer.print("hello world!");
  }
};
TS.$init();
