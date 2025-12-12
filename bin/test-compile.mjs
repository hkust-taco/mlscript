import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { inspect } from "node:util";

// Update the relative path here if this file is moved.
const projectPath = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

async function loadStandardLibrary() {
  const compilePath = path.join(projectPath, "hkmc2/shared/src/test/mlscript-compile");
  const files = await Promise.all(
    (await fs.readdir(compilePath))
      .filter((fileName) => {
        const ext = path.extname(fileName);
        return ext === ".mls" || ext === ".mjs";
      })
      .map(async (fileName) => ({
        path: `/std/${fileName}`,
        content: await fs.readFile(path.join(compilePath, fileName), "utf-8"),
      }))
  );
  const preludePath = path.join(projectPath, "hkmc2/shared/src/test/mlscript/decls/Prelude.mls");
  files.push({ path: "/std/Prelude.mls", content: await fs.readFile(preludePath, "utf-8") });
  return files;
}

async function importMLscript() {
  // Check if "./hkmc2/js/target/scala-3.7.3/hkmc2-opt/MLscript.mjs" exists.
  // If not, check "./hkmc2/js/target/scala-3.7.3/hkmc2-fastopt/MLscript.mjs"
  const mlscriptPath = path.join(projectPath, "hkmc2/js/target/scala-3.7.3/hkmc2-opt/MLscript.mjs");
  const mlscriptFastOptPath = path.join(projectPath, "hkmc2/js/target/scala-3.7.3/hkmc2-fastopt/MLscript.mjs");
  try {
    await fs.access(mlscriptPath);
    return await import(mlscriptPath);
  } catch {
    try {
      await fs.access(mlscriptFastOptPath);
      return await import(mlscriptFastOptPath);
    } catch {
      throw new Error(
        `MLscript module not found. Please build the project first.`
      );
    }
  }
}

async function main() {
  const { Compiler, InMemoryFileSystem, Paths } = await importMLscript();
  const fileSystem = InMemoryFileSystem(
    (await loadStandardLibrary()).map(({ path, content }) => [path, content])
  );
  const paths = new Paths(
    "/std/Prelude.mls",
    "/std/Runtime.mjs",
    "/std/Term.mjs"
  );
  const compiler = new Compiler(fileSystem, paths);
  const program = `import "./std/Option.mls"
import "./std/Stack.mls"
import "./std/Predef.mls"

open Stack
open Option
open Predef

fun findFirst(xs, f) = if xs is
  Nil then None
  Cons(x, xs') and
    f(x) then Some(x)
    else findFirst(xs', f)

let nums = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
let result = nums \\findFirst of x => x * 6 is 24
`;
  console.log(bold(red("Source Program:")));
  console.log(program);
  fileSystem.write("/test.mls", program);
  console.log(bold(red("Dianostics:")));
  console.log(inspect(compiler.compile("/test.mls"), { depth: null }));
  console.log(bold(red("Compiled JavaScript:")));
  console.log(fileSystem.read("/test.mjs"));
}

main();

function red(text) {
  return `\x1b[31m${text}\x1b[0m`;
}

function bold(text) {
  return `\x1b[1m${text}\x1b[0m`;
}
