import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../../../../..");
const modulePath = path.join(repoRoot, "hkmc2/js/target/scala-3.8.3/hkmc2-fastopt/MLscript.mjs");
const compilePath = path.join(repoRoot, "hkmc2/shared/src/test/mlscript-compile");
const preludePath = path.join(repoRoot, "hkmc2/shared/src/test/mlscript/decls/Prelude.mls");

const { BrowserCompiler, DummyFileSystem, Paths } = await import(path.toNamespacedPath(modulePath));

const files = new Map();
const writes = [];

for (const fileName of fs.readdirSync(compilePath)) {
  if (fileName.endsWith(".mls") || fileName.endsWith(".mjs")) {
    files.set(`/std/${fileName}`, fs.readFileSync(path.join(compilePath, fileName), "utf8"));
  }
}

files.set("/std/Prelude.mls", fs.readFileSync(preludePath, "utf8"));
files.set(
  "/some-file.mls",
  [
    'import "/std/Stack.mls"',
    "",
    "module OutlineSmoke with",
    "  class Box with",
    "    fun get() = 1",
    "",
    "  object Tools with",
    "    fun identity(x) = x",
    "",
    "  fun top(x) = x",
    "",
  ].join("\n"),
);

const virtualFs = {
  read(filePath) {
    if (!files.has(filePath)) {
      throw new Error(`File not found: ${filePath}`);
    }
    return files.get(filePath);
  },
  write(filePath, content) {
    writes.push(filePath);
    files.set(filePath, content);
  },
  exists(filePath) {
    return files.has(filePath);
  },
  getLastChangedTimestamp(filePath) {
    if (!files.has(filePath)) {
      throw new Error(`File not found: ${filePath}`);
    }
    return 0;
  },
};

const compiler = new BrowserCompiler(
  new DummyFileSystem(virtualFs),
  new Paths("/std/Prelude.mls", "/std/Runtime.mjs", "/std/Term.mjs", "/std"),
);

const result = compiler.analyze("/some-file.mls");

assert.equal(result.schema, "mlscript.symbol-tree");
assert.equal(result.version, 1);
assert.equal(result.rootFile, "/some-file.mls");
assert.ok(result.root);
assert.equal(result.root.kind, "file");
assert.ok(Array.isArray(result.root.children));
assert.ok(Array.isArray(result.diagnostics));

const moduleNode = result.root.children.find((node) => node.name === "OutlineSmoke");
assert.ok(moduleNode, "expected root module node");
assert.equal(moduleNode.kind, "module");

const boxNode = moduleNode.children.find((node) => node.name === "Box");
assert.ok(boxNode, "expected nested class node");
assert.equal(boxNode.kind, "class");
assert.ok(boxNode.children.some((node) => node.name === "get" && node.kind === "function"));

const toolsNode = moduleNode.children.find((node) => node.name === "Tools");
assert.ok(toolsNode, "expected nested object node");
assert.equal(toolsNode.kind, "object");
assert.ok(toolsNode.children.some((node) => node.name === "identity" && node.kind === "function"));
assert.ok(moduleNode.children.some((node) => node.name === "top" && node.kind === "function"));

assert.equal(files.has("/some-file.mjs"), false);
assert.deepEqual(writes.filter((filePath) => filePath.endsWith(".mjs")), []);

console.log("analyze smoke passed");
