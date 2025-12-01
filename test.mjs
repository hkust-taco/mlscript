// Note: This file will be removed before the PR is merged.

import { MLscript } from "./hkmc2/js/target/scala-3.7.3/hkmc2-fastopt/MLscript.mjs";

const compiler = new MLscript();

const program = `
class Some[A](x: A)
object None
type Option[A] = Some[A] | None
`;

console.log(compiler.compile(program));