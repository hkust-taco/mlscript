# MLscript Packages

This is the directory for packages.

## Package Manifest File

Each package's directory should contain a manifest file `manifest.json`.
The file will be written in `.mlson` (MLscript Object Notation) in the future.

### Vendor Paths: `vendors: Array[{prefix: Str, path: Str, files: Array[Str]}]`

This option specifies which source code files from outside the package need to be vendored into the current package.
Each element in the array has three properties: `prefix`, `path`, and `files`,
indicating that all files in the `path` directory matching the glob patterns in `files`
can be imported using `prefix` + the file's path relative to `path`.

For example, the following entry allows users to import all `.mls` files
(but not recursively)
in `mlscript-compile` folder by prefixing the filename with `@std/`.

```json
{
  "vendors": [
    {"prefix": "@std/", "path": "../../mlscript-compile", files: ["*.mls"]}
  ]
}
```

The array of vendors is matched in order,
and each import path will be rewritten using the first entry it matches.

Note that when compiling each package,
the compiler will actively compile all matched files.
Therefore, you need to specify the glob patterns in `files` as precisely as possible. Currently, only `*` and `**` glob patterns are supported.
