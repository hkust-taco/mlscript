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

Please also read the files in `.github/skills/hkmc2-difftests`.


## Coding Style

Never use `asInstanceOf` unless absolutely necessary. If you find yourself using `asInstanceOf`, it's a sign that your code may need to be refactored to be more type-safe.

Never use default arguments in core business logic.
Default arguments should be reserved for user-facing APIs.

Keep it DRY: if you find yourself copying and pasting code,
consider refactoring it into a reusable function or class.
The goal of minimizing code duplication is to improve maintainability:
the logic for handling cases that ought to be similar should be centralized.

**Document your code**:
Use comments to explain the intent behind complex logic,
especially if it is not immediately clear from the code itself.
When appropriate, explain the history of what led to the current implementation,
especially if it involves non-obvious decisions/trade-offs
or if alternative approaches were considered and rejected.


## Editing Style

Do not remove existing `end` markers.

Never strip indentation whitespace.

Empty lines in this project are usually significant.
They help to visually identify blocks and groups of blocks of code
(multiple empty lines separates groups of blocks hierarchically).
You should _never_ remove pre-existing empty lines as part of your changes;
this includes empty lines at the very end of files,
which are left for easier future editing by programmers.

**Important:** When working on a PR, make sure to check the diff of the whole PR (including all commits)
to ensure that no needless empty-line changes are included in the PR. If you find any, please remove them.

