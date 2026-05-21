# MLscript Web IDE

This is an online integrated development environment
(hereinafter referred to as the Web IDE)
developed for MLscript.
It supports syntax highlighting,
multi-file compilation,
module JavaScript code generation,
and sandbox execution in local browser.

## Getting Started

- Run `sbt hkmc2JVM/test` first.
  This generates the standard library `.mjs` files used by the demo.
- Run `sbt hkmc2JS/fullOptJS`.
  This compiles the MLscript compiler to JavaScript
  and embeds the standard library sources for the browser.
- Copy `hkmc2/js/target/scala-3.8.3/hkmc2-opt/`
  into this package's ignored `build/` folder.
- Serve this folder with a static web server.
