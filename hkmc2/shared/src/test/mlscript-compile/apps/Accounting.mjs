import fs from "fs";
import Str from "./../Str.mjs";
import Predef from "./../Predef.mjs";
let Accounting1;
Accounting1 = class Accounting {
  constructor() {
    this.warnings = [];
    this.Project = function Project(num1) { return new Project.class(num1); };
    this.Project.class = class Project {
      constructor(num) {
        this.num = num;
      }
      toString() { return "Project(" + globalThis.Predef.render(this.num) + ")"; }
    };
    const this$Accounting = this;
    this.Line = function Line(name1, proj1, starting_balance1, isMatchable1) { return new Line.class(name1, proj1, starting_balance1, isMatchable1); };
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
        return null;
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
          return this$Accounting.warnings.push(tmp4) ?? null;
        } else {
          return null;
        }
      }
      toString() { return "Line(" + globalThis.Predef.render(this.name) + ", " + globalThis.Predef.render(this.proj) + ", " + globalThis.Predef.render(this.starting_balance) + ", " + globalThis.Predef.render(this.isMatchable) + ")"; }
    };
    this.lines = [];
    this.Report = function Report(fileName1) { return new Report.class(fileName1); };
    this.Report.class = class Report {
      constructor(fileName) {
        this.fileName = fileName;
        let tmp;
        tmp = fs.writeFileSync(this.fileName, "# Accounting\n");
      }
      w(txt) {
        return fs.appendFileSync(this.fileName, txt);
      } 
      wln(txt1) {
        let tmp;
        tmp = Str.concat2(txt1, "\n");
        return fs.appendFileSync(this.fileName, tmp);
      } 
      init() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
        tmp = this.wln("");
        tmp1 = Str.concat2("|", "Year");
        tmp2 = Str.concat2(tmp1, "|");
        tmp3 = this$Accounting.lines.map((x) => {
          return x.name;
        }) ?? null;
        tmp4 = tmp3.join("|") ?? null;
        tmp5 = Str.concat2(tmp2, tmp4);
        tmp6 = Str.concat2(tmp5, "|");
        tmp7 = this.wln(tmp6);
        tmp8 = Str.concat2("|", "---");
        tmp9 = Str.concat2(tmp8, "|");
        tmp10 = this$Accounting.lines.map((x) => {
          return "--:";
        }) ?? null;
        tmp11 = tmp10.join("|") ?? null;
        tmp12 = Str.concat2(tmp9, tmp11);
        tmp13 = Str.concat2(tmp12, "|");
        return this.wln(tmp13);
      } 
      snapShot(label) {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
        tmp = globalThis.String(label) ?? null;
        tmp1 = Str.concat2("|", tmp);
        tmp2 = Str.concat2(tmp1, "|");
        tmp3 = this$Accounting.lines.map((x) => {
          return this$Accounting.display(x.balance);
        }) ?? null;
        tmp4 = tmp3.join("|") ?? null;
        tmp5 = Str.concat2(tmp2, tmp4);
        tmp6 = Str.concat2(tmp5, "|");
        return this.wln(tmp6);
      } 
      wrapUp() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
        tmp = this.wln("");
        tmp1 = this$Accounting.warnings.forEach((x) => {
          let tmp27;
          tmp27 = this.wln(x);
          return this.wln("");
        }) ?? null;
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
        tmp12 = this$Accounting.lines.filter((x) => {
          return x.isMatchable;
        }) ?? null;
        tmp13 = tmp12.map((x) => {
          return x.balance;
        }) ?? null;
        tmp14 = tmp13.reduce((a, b) => {
          return a + b;
        }, 0);
        tmp15 = this$Accounting.display(tmp14);
        tmp16 = Str.concat2(tmp11, tmp15);
        tmp17 = Str.concat2(tmp16, "|");
        tmp18 = this.wln(tmp17);
        tmp19 = Str.concat2("|", "Non-matchable");
        tmp20 = Str.concat2(tmp19, "|");
        tmp21 = this$Accounting.lines.filter((x) => {
          return Predef.not(x.isMatchable);
        }) ?? null;
        tmp22 = tmp21.map((x) => {
          return x.balance;
        }) ?? null;
        tmp23 = tmp22.reduce((a, b) => {
          return a + b;
        }, 0);
        tmp24 = this$Accounting.display(tmp23);
        tmp25 = Str.concat2(tmp20, tmp24);
        tmp26 = Str.concat2(tmp25, "|");
        return this.wln(tmp26);
      }
      toString() { return "Report(" + globalThis.Predef.render(this.fileName) + ")"; }
    };
  }
  display(amt) {
    let tmp;
    tmp = amt / 1000;
    return tmp.toFixed(1) ?? null;
  } 
  mkLine(nme, proj, starting_balance, matchable) {
    let line, tmp, tmp1;
    tmp = this.Line(nme, proj, starting_balance, matchable);
    line = tmp;
    tmp1 = this.lines.push(line) ?? null;
    return line;
  } 
  process(filename, k) {
    let report, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = this.Report(filename);
    report = tmp;
    tmp1 = report.init() ?? null;
    tmp2 = k(report) ?? null;
    tmp3 = report.wrapUp() ?? null;
    tmp4 = Str.concat2("Report written to ", filename);
    return Predef.print(tmp4);
  }
  toString() { return "Accounting"; }
};
null
let Accounting = Accounting1; export default Accounting;
