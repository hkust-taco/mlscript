import fs from "fs";
import Str from "./../Str.mjs";
import Predef from "./../Predef.mjs";
class Num {
  constructor() {
    
  }
  toString() { return "Num"; }
}
class Bool {
  constructor() {
    
  }
  toString() { return "Bool"; }
}
class Accounting {
  constructor() {
    this.warnings = [
      
    ];
    this.Project = function Project(num1) { return new Project.class(num1); };
    this.Project.class = class Project {
      constructor(num) {
        this.num = num;
        
      }
      toString() { return "Project(" + this.num + ")"; }
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
        if (scrut) {
          tmp = ((Str.concat("> **\u2757\uFE0F** Unspent balance of ", this.name)) ?? null);
          tmp1 = ((Str.concat(tmp, ": `")) ?? null);
          tmp2 = ((this$Accounting.display(this.balance)) ?? null);
          tmp3 = ((Str.concat(tmp1, tmp2)) ?? null);
          tmp4 = ((Str.concat(tmp3, "`")) ?? null);
          return ((this$Accounting.warnings.push(tmp4)) ?? null);
        } else {
          return null;
        }
      }
      toString() { return "Line(" + this.name + ", " + this.proj + ", " + this.starting_balance + ", " + this.isMatchable + ")"; }
    };
    this.lines = [
      
    ];
    this.Report = function Report(fileName1) { return new Report.class(fileName1); };
    this.Report.class = class Report {
      constructor(fileName) {
        this.fileName = fileName;
        let tmp;
        tmp = ((fs.writeFileSync(this.fileName, "# Accounting\n")) ?? null);
      }
      w(txt) {
        return ((fs.appendFileSync(this.fileName, txt)) ?? null);
      } 
      wln(txt1) {
        let tmp;
        tmp = ((Str.concat(txt1, "\n")) ?? null);
        return ((fs.appendFileSync(this.fileName, tmp)) ?? null);
      } 
      init() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
        tmp = ((this.wln("")) ?? null);
        tmp1 = ((Str.concat("|", "Year")) ?? null);
        tmp2 = ((Str.concat(tmp1, "|")) ?? null);
        tmp3 = ((this$Accounting.lines.map((x) => {
          let selRes;
          selRes = x.name;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'name' yielded 'undefined'");
          } else {
            return selRes;
          }
        })) ?? null);
        tmp4 = ((tmp3.join("|")) ?? null);
        tmp5 = ((Str.concat(tmp2, tmp4)) ?? null);
        tmp6 = ((Str.concat(tmp5, "|")) ?? null);
        tmp7 = ((this.wln(tmp6)) ?? null);
        tmp8 = ((Str.concat("|", "---")) ?? null);
        tmp9 = ((Str.concat(tmp8, "|")) ?? null);
        tmp10 = ((this$Accounting.lines.map((x) => {
          return "--:";
        })) ?? null);
        tmp11 = ((tmp10.join("|")) ?? null);
        tmp12 = ((Str.concat(tmp9, tmp11)) ?? null);
        tmp13 = ((Str.concat(tmp12, "|")) ?? null);
        return ((this.wln(tmp13)) ?? null);
      } 
      snapShot(label) {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
        tmp = ((String(label)) ?? null);
        tmp1 = ((Str.concat("|", tmp)) ?? null);
        tmp2 = ((Str.concat(tmp1, "|")) ?? null);
        tmp3 = ((this$Accounting.lines.map((x) => {
          let selRes, tmp7;
          selRes = x.balance;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'balance' yielded 'undefined'");
          } else {
            tmp7 = selRes;
          }
          return ((this$Accounting.display(tmp7)) ?? null);
        })) ?? null);
        tmp4 = ((tmp3.join("|")) ?? null);
        tmp5 = ((Str.concat(tmp2, tmp4)) ?? null);
        tmp6 = ((Str.concat(tmp5, "|")) ?? null);
        return ((this.wln(tmp6)) ?? null);
      } 
      wrapUp() {
        let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
        tmp = ((this.wln("")) ?? null);
        tmp1 = ((this$Accounting.warnings.forEach((x) => {
          let tmp27;
          tmp27 = ((this.wln(x)) ?? null);
          return ((this.wln("")) ?? null);
        })) ?? null);
        tmp2 = ((this.wln("### Remaining Available Funds")) ?? null);
        tmp3 = ((this.wln("")) ?? null);
        tmp4 = ((Str.concat("|", "Summary")) ?? null);
        tmp5 = ((Str.concat(tmp4, "|   |")) ?? null);
        tmp6 = ((this.wln(tmp5)) ?? null);
        tmp7 = ((Str.concat("|", "---")) ?? null);
        tmp8 = ((Str.concat(tmp7, "|--:|")) ?? null);
        tmp9 = ((this.wln(tmp8)) ?? null);
        tmp10 = ((Str.concat("|", "Matchable")) ?? null);
        tmp11 = ((Str.concat(tmp10, "|")) ?? null);
        tmp12 = ((this$Accounting.lines.filter((x) => {
          let selRes;
          selRes = x.isMatchable;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'isMatchable' yielded 'undefined'");
          } else {
            return selRes;
          }
        })) ?? null);
        tmp13 = ((tmp12.map((x) => {
          let selRes;
          selRes = x.balance;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'balance' yielded 'undefined'");
          } else {
            return selRes;
          }
        })) ?? null);
        tmp14 = ((tmp13.reduce((a, b) => {
          return a + b;
        }, 0)) ?? null);
        tmp15 = ((this$Accounting.display(tmp14)) ?? null);
        tmp16 = ((Str.concat(tmp11, tmp15)) ?? null);
        tmp17 = ((Str.concat(tmp16, "|")) ?? null);
        tmp18 = ((this.wln(tmp17)) ?? null);
        tmp19 = ((Str.concat("|", "Non-matchable")) ?? null);
        tmp20 = ((Str.concat(tmp19, "|")) ?? null);
        tmp21 = ((this$Accounting.lines.filter((x) => {
          let selRes, tmp27;
          selRes = x.isMatchable;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'isMatchable' yielded 'undefined'");
          } else {
            tmp27 = selRes;
          }
          return ((Predef.not(tmp27)) ?? null);
        })) ?? null);
        tmp22 = ((tmp21.map((x) => {
          let selRes;
          selRes = x.balance;
          if (selRes === undefined) {
            throw new globalThis.Error("Access to required field 'balance' yielded 'undefined'");
          } else {
            return selRes;
          }
        })) ?? null);
        tmp23 = ((tmp22.reduce((a, b) => {
          return a + b;
        }, 0)) ?? null);
        tmp24 = ((this$Accounting.display(tmp23)) ?? null);
        tmp25 = ((Str.concat(tmp20, tmp24)) ?? null);
        tmp26 = ((Str.concat(tmp25, "|")) ?? null);
        return ((this.wln(tmp26)) ?? null);
      }
      toString() { return "Report(" + this.fileName + ")"; }
    };
  }
  display(amt) {
    let tmp;
    tmp = amt / 1000;
    return ((tmp.toFixed(1)) ?? null);
  } 
  mkLine(nme, proj, starting_balance, matchable) {
    let line, tmp, tmp1;
    tmp = ((this.Line(nme, proj, starting_balance, matchable)) ?? null);
    line = tmp;
    tmp1 = ((this.lines.push(line)) ?? null);
    return line;
  } 
  process(filename, k) {
    let report, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = ((this.Report(filename)) ?? null);
    report = tmp;
    tmp1 = ((report.init()) ?? null);
    tmp2 = ((k(report)) ?? null);
    tmp3 = ((report.wrapUp()) ?? null);
    tmp4 = ((Str.concat("Report written to ", filename)) ?? null);
    return ((Predef.print(tmp4)) ?? null);
  }
  toString() { return "Accounting"; }
}
null
export default Accounting;
