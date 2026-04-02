# Using the MLscript code base


## Workflow

It is best to leave the SBT shell open (by just typing the `sbt` command line)
and issue commands directly in that shell, as SBT startup is very slow.

Before running individual tests, make sure to first run `hkmc2JVM/test`,
so that the compilation-tests (in `hkmc2/shared/src/test/mlscript-compile/`) are run
and produce the JS files that are needed at runtime for the other tests (in `hkmc2/shared/src/test/mlscript/`).

Before finishing your work, run `hkmc2AllTests/test` to make sure the codebase compiles and all tests succeed.

After you are done fixing all the problems and all the tests pass,
*you need to commit the resulting golden test output changes*.
Any commit that does not include the latest changes to test outputs will fail the CI.


## Coding Style

Never use `asInstanceOf` unless absolutely necessary. If you find yourself using `asInstanceOf`, it's a sign that your code may need to be refactored to be more type-safe.

Never use default arguments in core business logic. Default arguments should be reserved for user-facing APIs.

Do not remove existing `end` markers.

