const Predef$class = class Predef {
  constructor() {
    
  }
  checkArgs(functionName, expected, got) {
    let scrut, name, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    scrut = got != expected;
    if (scrut) {
      scrut1 = functionName.length > 0;
      if (scrut1) {
        tmp = " '".concat(functionName);
        tmp1 = tmp.concat("'");
      } else {
        tmp1 = "";
      }
      name = tmp1;
      tmp2 = "Function".concat(name);
      tmp3 = tmp2.concat(" expected ");
      tmp4 = tmp3.concat(expected);
      tmp5 = tmp4.concat(" arguments but got ");
      tmp6 = tmp5.concat(got);
      throw new Error.class(tmp6);
    } else {
      return undefined;
    }
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
