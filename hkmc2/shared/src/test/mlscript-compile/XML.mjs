import runtime from "./Runtime.mjs";
import Predef from "./Predef.mjs";
import Iter from "./Iter.mjs";
let StyleAttributeValue1, XML1;
StyleAttributeValue1 = function StyleAttributeValue(rules1) {
  return new StyleAttributeValue.class(rules1);
};
StyleAttributeValue1.class = class StyleAttributeValue {
  #rules;
  constructor(rules) {
    this.#rules = rules;
  }
  toString() { return "StyleAttributeValue(" + "" + ")"; }
};
(class XML {
  static {
    XML1 = XML;
  }
  static serializeValue(value) {
    let param0, rules, tmp, tmp1, tmp2, lambda;
    if (typeof value === 'string') {
      return runtime.safeCall(globalThis.JSON.stringify(value))
    } else if (value instanceof StyleAttributeValue1.class) {
      param0 = value.rules;
      rules = param0;
      lambda = (undefined, function (caseScrut) {
        let first1, first0, name, value1, tmp3;
        if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
          first0 = caseScrut[0];
          first1 = caseScrut[1];
          name = first0;
          value1 = first1;
          tmp3 = name + ": ";
          return tmp3 + value1
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp = lambda;
      tmp1 = Iter.mapping(rules, tmp);
      tmp2 = Iter.joined(tmp1, "; ");
      return runtime.safeCall(globalThis.JSON.stringify(tmp2))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static joinAttributes(attributes) {
    let tmp, tmp1, tmp2, lambda;
    if (globalThis.Array.isArray(attributes) && attributes.length === 0) {
      return ""
    } else {
      lambda = (undefined, function (caseScrut) {
        let first1, first0, name, value1, tmp3, tmp4;
        if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
          first0 = caseScrut[0];
          first1 = caseScrut[1];
          name = first0;
          value1 = first1;
          tmp3 = name + "=";
          tmp4 = XML.serializeValue(value1);
          return tmp3 + tmp4
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp = lambda;
      tmp1 = Iter.mapping(attributes, tmp);
      tmp2 = Iter.joined(tmp1, " ");
      return " " + tmp2
    }
  } 
  static elem(tagName, ...attributes1) {
    return (...elements) => {
      let tmp, tmp1, lambda;
      lambda = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp = runtime.safeCall(Predef.fold(lambda));
      tmp1 = XML.joinAttributes(attributes1);
      return runtime.safeCall(tmp("<", tagName, tmp1, ">", ...elements, "</", tagName, ">"))
    }
  } 
  static tag(tagName1) {
    return (...attributes2) => {
      let tmp, tmp1, lambda;
      lambda = (undefined, function (arg1, arg2) {
        return arg1 + arg2
      });
      tmp = runtime.safeCall(Predef.fold(lambda));
      tmp1 = XML.joinAttributes(attributes2);
      return runtime.safeCall(tmp("<", tagName1, tmp1, " ", "/>"))
    }
  } 
  static style(...rules) {
    let tmp;
    tmp = StyleAttributeValue1(rules);
    return [
      "style",
      tmp
    ]
  } 
  static html(attributes2) {
    return (...elements) => {
      let tmp, tmp1;
      tmp = XML.elem("html", attributes2);
      tmp1 = runtime.safeCall(tmp(...elements));
      return "<!DOCTYPE html>" + tmp1
    }
  }
  static toString() { return "XML"; }
});
let XML = XML1; export default XML;
