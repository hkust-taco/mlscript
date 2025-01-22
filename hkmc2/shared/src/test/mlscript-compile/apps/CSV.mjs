import Str from "./../Str.mjs";
import Predef from "./../Predef.mjs";
let CSV1;
CSV1 = function CSV(strDelimiter1) { return new CSV.class(strDelimiter1); };
CSV1.class = class CSV {
  constructor(strDelimiter) {
    this.strDelimiter = strDelimiter;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    tmp = this.strDelimiter || ",";
    this.strDelimiter = tmp;
    tmp1 = "(\\" + this.strDelimiter;
    tmp2 = tmp1 + "|\\r?\\n|\\r|^)";
    tmp3 = "([^\"\\" + this.strDelimiter;
    tmp4 = tmp3 + "\\r\\n]*))";
    tmp5 = "(?:\"([^\"]*(?:\"\"[^\"]*)*)\"|" + tmp4;
    tmp6 = tmp2 + tmp5;
    tmp7 = new globalThis.RegExp(tmp6, "gi");
    this.objPattern = tmp7;
  }
  toArrays(strData) {
    let arrData, arrMatches, scrut, strMatchedDelimiter, scrut1, strMatchedValue, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    arrData = [
      []
    ];
    tmp7: while (true) {
      arrMatches = this.objPattern.exec(strData) ?? null;
      scrut = arrMatches !== null;
      if (scrut === true) {
        strMatchedDelimiter = arrMatches[1];
        tmp = strMatchedDelimiter != this.strDelimiter;
        scrut1 = strMatchedDelimiter.length && tmp;
        if (scrut1 === true) {
          tmp1 = arrData.push([]) ?? null;
        } else {
          tmp1 = null;
        }
        scrut2 = arrMatches[2];
        if (scrut2 === true) {
          tmp2 = new globalThis.RegExp("\"\"", "g");
          tmp3 = arrMatches[2].replace(tmp2, "\"");
        } else {
          tmp3 = arrMatches[3];
        }
        strMatchedValue = tmp3;
        tmp4 = arrData.length - 1;
        tmp5 = arrData.at(tmp4) ?? null;
        tmp6 = tmp5.push(strMatchedValue) ?? null;
        continue tmp7;
      } else {
        tmp6 = null;
      }
      break;
    }
    return arrData;
  }
  toString() { return "CSV(" + this.strDelimiter + ")"; }
};
null
let CSV = CSV1; export default CSV;
