# MLscript Packages

Each direct child directory is treated as one package. For example,
`mlscript-packages/web-ide` defines the package named `web-ide`.

The first package-resolution goal is small: packages can import
outside source trees through explicit vendoring, while relative imports inside
a package keep their current behavior.

## Package Manifest File

Each package's directory should contain a manifest file `manifest.json`.
The file will be written in `.mlson` (_MLscript Object Notation_) in the future.

Minimal shape:

```json
{
  "name": "recursive-descent-parsing",
  "main": "RecursiveDescent.mls",
  "moduleName": "RecursiveDescent",
  "vendors": [
    {
      "prefix": "std/",
      "path": "../../mlscript-compile",
      "files": ["Predef.mls", "Stack.mls", "Option.mls"]
    },
    {
      "prefix": "gpp/",
      "path": "../generalized-pratt-parsing",
      "files": ["Token.mls"]
    }
  ]
}
```

Required fields:

- `name`: package name. This should match the package directory name.
- `main`: entry `.mls` file for `import "package-name"`.
- `moduleName`: MLscript symbol expected to be defined by the entry file.

Optional fields:

- `vendors`: external source roots made available to this package.

## Vendoring

`vendors` is the package interdependency mechanism. It is intentionally not an
npm-style dependency graph: a package explicitly chooses which source roots and
which entry files it vendors.

Each vendor entry has:
- `prefix`: import prefix visible to this package.
- `path`: source root, relative to the current package directory.
- `files`: initial `.mls` files or glob patterns under `path`.

For each vendor entry, the package compiler:
1. starts from the `.mls` files matched by `files`;
2. recursively follows their `.mls` imports;
3. compiles the transitive `.mls` closure into `.mjs` files under
  `vendors/<prefix>/` in the current package;
4. copies all `.js`/`.mjs` files under the declared vendor roots as static
  assets, without analyzing their imports;
5. leaves the generated `.mjs` files untracked by version control.

If a JavaScript asset would be copied to the same path as a compiled `.mls`
output, the compiled `.mls` output wins.

The compiler injects `Runtime.mjs` into every
generated JavaScript module.
We place this file at `vendors/std/` of each package.

When vendored code imports another package, package tests read that package's
manifest too. Each package is copied into the current package's
`vendors/` directory at most once, and all generated imports point to that same
copy.

The package's own `.mls` files still compile beside themselves.
