import runtime from "./../Runtime.mjs";
import fs from "fs";
import Str from "./../Str.mjs";
import Predef from "./../Predef.mjs";
let Accounting1;
Accounting1 = class Accounting {
  constructor() {
    this.warnings = [];
    this.Project = function Project(num1) {
      return new Project.class(num1);
    };
    this.Project.class = class Project {
      constructor(num) {
        this.num = num;
      }
      toString() { return "Project(" + globalThis.Predef.render(this.num) + ")"; }
    };
    const this$Accounting = this;
    this.Line = function Line(name1, proj1, starting_balance1, isMatchable1) {
      return new Line.class(name1, proj1, starting_balance1, isMatchable1);
    };
    this.Line.class = class Line {
      constructor(name, proj, starting_balance, isMatchable) {
        this.name = name;
        this.proj = proj;
        this.starting_balance = starting_balance;
        this.isMatchable = isMatchable;
        this.balance = this.starting_balance;
      }
      expense(amt) {
        let tmp;
        tmp = this.balance - amt;
        this.balance = tmp;
        return runtime.Unit
      } 
      mustBeEmpty() {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = this.balance > 10000;
        if (scrut === true) {
          tmp = Str.concat2("> **\u2757\uFE0F** Unspent balance of ", this.name);
          tmp1 = Str.concat2(tmp, ": `");
          tmp2 = this$Accounting.display(this.balance);
          tmp3 = Str.concat2(tmp1, tmp2);
          tmp4 = Str.concat2(tmp3, "`");
          return runtime.safeCall(this$Accounting.warnings.push(tmp4))
        } else {
          return runtime.Unit
        }
      }
      toString() { return "Line(" + globalThis.Predef.render(this.name) + ", " + globalThis.Predef.render(this.proj) + ", " + globalThis.Predef.render(this.starting_balance) + ", " + globalThis.Predef.render(this.isMatchable) + ")"; }
    };
    this.lines = [];
    this.Report = function Report(fileName1) {
      return new Report.class(fileName1);
    };
    this.Report.class = class Report {
      constructor(fileName) {
        this.fileName = fileName;
        let tmp;
        tmp = fs.writeFileSync(this.fileName, "# Accounting\n");
      }
      w(txt) {
        return fs.appendFileSync(this.fileName, txt)
      } 
      wln(txt1) {
        let tmp;
        tmp = Str.concat2(txt1, "\n");
        return fs.appendFileSync(this.fileName, tmp)
      } 
      init() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, lambda, lambda1;
        tmp = this.wln("");
        tmp1 = Str.concat2("|", "Year");
        tmp2 = Str.concat2(tmp1, "|");
        lambda = (undefined, function (x) {
          return x.name
        });
        tmp3 = runtime.safeCall(this$Accounting.lines.map(lambda));
        tmp4 = runtime.safeCall(tmp3.join("|"));
        tmp5 = Str.concat2(tmp2, tmp4);
        tmp6 = Str.concat2(tmp5, "|");
        tmp7 = this.wln(tmp6);
        tmp8 = Str.concat2("|", "---");
        tmp9 = Str.concat2(tmp8, "|");
        lambda1 = (undefined, function (x) {
          return "--:"
        });
        tmp10 = runtime.safeCall(this$Accounting.lines.map(lambda1));
        tmp11 = runtime.safeCall(tmp10.join("|"));
        tmp12 = Str.concat2(tmp9, tmp11);
        tmp13 = Str.concat2(tmp12, "|");
        return this.wln(tmp13)
      } 
      snapShot(label) {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda;
        tmp = runtime.safeCall(globalThis.String(label));
        tmp1 = Str.concat2("|", tmp);
        tmp2 = Str.concat2(tmp1, "|");
        lambda = (undefined, function (x) {
          return this$Accounting.display(x.balance)
        });
        tmp3 = runtime.safeCall(this$Accounting.lines.map(lambda));
        tmp4 = runtime.safeCall(tmp3.join("|"));
        tmp5 = Str.concat2(tmp2, tmp4);
        tmp6 = Str.concat2(tmp5, "|");
        return this.wln(tmp6)
      } 
      wrapUp() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6;
        tmp = this.wln("");
        const this$Report = this;
        lambda = (undefined, function (x) {
          let tmp27;
          tmp27 = this$Report.wln(x);
          return this$Report.wln("")
        });
        tmp1 = runtime.safeCall(this$Accounting.warnings.forEach(lambda));
        tmp2 = this.wln("### Remaining Available Funds");
        tmp3 = this.wln("");
        tmp4 = Str.concat2("|", "Summary");
        tmp5 = Str.concat2(tmp4, "|   |");
        tmp6 = this.wln(tmp5);
        tmp7 = Str.concat2("|", "---");
        tmp8 = Str.concat2(tmp7, "|--:|");
        tmp9 = this.wln(tmp8);
        tmp10 = Str.concat2("|", "Matchable");
        tmp11 = Str.concat2(tmp10, "|");
        lambda1 = (undefined, function (x) {
          return x.isMatchable
        });
        tmp12 = runtime.safeCall(this$Accounting.lines.filter(lambda1));
        lambda2 = (undefined, function (x) {
          return x.balance
        });
        tmp13 = runtime.safeCall(tmp12.map(lambda2));
        lambda3 = (undefined, function (a, b) {
          return a + b
        });
        tmp14 = tmp13.reduce(lambda3, 0);
        tmp15 = this$Accounting.display(tmp14);
        tmp16 = Str.concat2(tmp11, tmp15);
        tmp17 = Str.concat2(tmp16, "|");
        tmp18 = this.wln(tmp17);
        tmp19 = Str.concat2("|", "Non-matchable");
        tmp20 = Str.concat2(tmp19, "|");
        lambda4 = (undefined, function (x) {
          return Predef.not(x.isMatchable)
        });
        tmp21 = runtime.safeCall(this$Accounting.lines.filter(lambda4));
        lambda5 = (undefined, function (x) {
          return x.balance
        });
        tmp22 = runtime.safeCall(tmp21.map(lambda5));
        lambda6 = (undefined, function (a, b) {
          return a + b
        });
        tmp23 = tmp22.reduce(lambda6, 0);
        tmp24 = this$Accounting.display(tmp23);
        tmp25 = Str.concat2(tmp20, tmp24);
        tmp26 = Str.concat2(tmp25, "|");
        return this.wln(tmp26)
      }
      toString() { return "Report(" + globalThis.Predef.render(this.fileName) + ")"; }
    };
  }
  display(amt) {
    let tmp;
    tmp = amt / 1000;
    return runtime.safeCall(tmp.toFixed(1))
  } 
  mkLine(nme, proj, starting_balance, matchable) {
    let line, tmp, tmp1;
    tmp = this.Line(nme, proj, starting_balance, matchable);
    line = tmp;
    tmp1 = runtime.safeCall(this.lines.push(line));
    return line
  } 
  process(filename, k) {
    let report, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = this.Report(filename);
    report = tmp;
    tmp1 = runtime.safeCall(report.init());
    tmp2 = runtime.safeCall(k(report));
    tmp3 = runtime.safeCall(report.wrapUp());
    tmp4 = Str.concat2("Report written to ", filename);
    return Predef.print(tmp4)
  }
  toString() { return "Accounting"; }
};
let Accounting = Accounting1; export default Accounting;
