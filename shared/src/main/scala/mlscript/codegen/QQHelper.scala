package mlscript.codegen

import mlscript.utils._
import mlscript.utils.shorthands._

// * Pretty printer for quasiquotes.
// * This is a temporary hack due to lack of runtime support and should be removed later.
object QQHelper {
  val prettyPrinter: Str = """
  |(() => {
  | const symbols = new Map();
  | const printList = (lst, sep) => {
  |   if (lst.length === 0) return "";
  |   else {
  |     const r = lst.reduce((x, y) => `${x}${y}${sep}`, "")
  |     return r.substring(0, r.length - sep.length);
  |   }
  | }
  | const indent = (s) => s.split("\n").map(ln => `  ${ln}`).join("\n")
  | globalThis.freshName = (n) => {
  |   if (!symbols.has(n)) { symbols.set(n, 0); }
  |   const i = symbols.get(n);
  |   symbols.set(n, i + 1);
  |   return `${n}_${i}`;
  | }
  | globalThis.Const = (n) => `${n}`;
  | globalThis.IntLit = (v) => `${v}`;
  | globalThis.DecLit = (v) => `${v}`;
  | globalThis.StrLit = (v) => `${v}`;
  | globalThis.UnitLit = (v) => `${v}`;
  | globalThis.Lam = (x, e) => `(${x}) =>\n${indent(e)}`;
  | globalThis.Var = (x) => `${x}`;
  | globalThis.App = (f, ...xs) => {
  | if (f === '+' || f === '-' || f === '*' || f === '/' || f === '==' || f === '<' || f === '>' || f === 'and' || f === 'or' || f === 'is')
  |   return `(${printList(xs, ` ${f} `)})`;
  | else
  |   return `${f}${printList(xs, ", ")}`;
  | }
  | globalThis.Rcd = (...xs) => `{${printList(xs, ", ")}}`;
  | globalThis.Bra = (x) => `(${x})`;
  | globalThis.Sel = (x, y) => `${x}.${y}`;
  | globalThis.Blk = (...s) => `{\n${indent(printList(s, ";\n"))}\n}`;
  | globalThis.Tup = (...es) => `(${printList(es, ", ")})`;
  | globalThis.Fld = (v) => `${v}`;
  | globalThis.Let = (nme, v, bod) => `let ${nme} =\n${indent(v)}\n${indent(`in ${bod}`)}`;
  | globalThis.Subs = (arr, idx) => `${arr}[${idx}]`;
  | globalThis.With = (lhs, rhs) => `${lsh} with ${rhs}`;
  | globalThis.Quoted = (body) => `code"${body}"`;
  | globalThis.CaseOf = (trm, cse) => `match ${trm}:\n  ${cse}`;
  | globalThis.Case = (pat, bod, trm) => `case ${pat} => ${bod}\n  ${trm})`;
  | globalThis.Wildcard = (res) => `_ => ${res}`;
  | globalThis.NoCases = () => `<NoCases>`;
  | globalThis.run = (code) => {console.log("Quoted:\n" + code);}
  |})();
  """.stripMargin
}
