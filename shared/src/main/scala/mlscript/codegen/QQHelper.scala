package mlscript.codegen

import mlscript.utils._
import mlscript.utils.shorthands._

object QQHelper {
  val prettyPrinter: Str = """
  |(() => {
  | let indent = "";
  | globalThis.freshName = (n) => `fresh_${n}`;
  | globalThis.Const = (n) => `const_${n}`;
  | globalThis.IntLit = (v) => `IntLit(${v})`;
  | globalThis.DecLit = (v) => `DecLit(${v})`;
  | globalThis.StrLit = (v) => `StrLit(${v})`;
  | globalThis.UnitLit = (v) => `UnitLit(${v})`;
  | globalThis.Lam = (x, e) => `(${x}) => ${e}`;
  | globalThis.Var = (x) => `Var(${x})`;
  | globalThis.App = (f, ...xs) => `${f}(${xs.reduce((x, y) => `${x}${y}, `, "")})`;
  | globalThis.Rcd = (...xs) => `Rcd(${xs.reduce((x, y) => `${x}${y}, `, "")})`;
  | globalThis.Bra = (x) => `(${x})`;
  | globalThis.Sel = (x, y) => `${x}.${y}`;
  | globalThis.Blk = (...s) => `Blk(${s.reduce((x, y) => `${x}${y}; `, "")})`;
  | globalThis.Tup = (...es) => `Tup(${es.reduce((x, y) => `${x}${y}, `, "")})`;
  | globalThis.Fld = (v) => `Fld(${v})`;
  | globalThis.Let = (nme, v, bod) => `let ${nme} = ${v} in ${bod}`;
  | globalThis.Subs = (arr, idx) => `${arr}[${idx}]`;
  | globalThis.With = (lhs, rhs) => `${lsh} with ${rhs}`;
  | globalThis.Quoted = (body) => `Quote(${body})`;
  | globalThis.CaseOf = (trm, cse) => `CaseOf(${trm}, $cse)`;
  | globalThis.Case = (pat, bod, trm) => `Case(${pat}, ${bod}, ${trm})`;
  | globalThis.Wildcard = () => `_`;
  | globalThis.NoCases = () => `NoCases`;
  |})();
  """.stripMargin
}
