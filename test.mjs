// Note: This file will be removed before the PR is merged.

import * as mlscript from "./hkmc2/shared/src/test/mlscript-compile/apps/web-demo/build/MLscript.mjs";

const fs = mlscript.std.defaultFileSystem
const paths = mlscript.std.defaultPaths
const compiler = new mlscript.Compiler(fs, paths);

console.log(Object.getPrototypeOf(fs));

const program = `
class Some[A](x: A)
object None
type Option[A] = Some[A] | None
`;

fs.write("/test.mls", program);

console.log(compiler.compile("/test.mls"));

console.log(fs.list);

console.log(fs.read("/test.mjs"));

