# Extensible Example 02: Workflow Steps

Status: Done

## Goal

Demonstrate a recursive extension category that parses a compact workflow
declaration:

```ocaml
workflow deploy step "build" next step "test" next done
```

and lowers the workflow body to a nested `Cons ... Nil` tree.

## Added Test Source

```ocaml
#keyword "workflow" None None
#keyword "step" None None
#keyword "next" None None
#keyword "done" None None
#extend ["steps", [ keyword("step"), ["string-literal", "name"], keyword("next"), ["steps", "tail"] ], [Cons name tail]]
#extend ["steps", [ keyword("done") ], [Nil]]
#extend ["decl", [ keyword("workflow"), ["ident", "name"], ["steps", "steps"] ], [Workflow name steps]]
workflow deploy step "build" next step "test" next done
```

## Notes

- `steps` is a recursive extension-only category.
- The final `decl` extension captures a workflow name and a recursive step list.
- The output tree demonstrates recursive parsing and substitution through the
  extension mechanism.

## Parser Fixes

- None.
