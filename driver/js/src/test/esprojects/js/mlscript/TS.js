import * as MyPrint from "../my_ts_path/MyPrint.js"

const TS = new class TS {
  constructor() {
  }
  $init() {
    const tspt = MyPrint.DatePrint;
    const printer = new tspt("love from ts");
    printer.print("hello world!");
  }
};
TS.$init();
