# Extensible Example 01: Route Declarations

Status: Done

## Goal

Demonstrate a compact declaration-level DSL built with `#keyword` and
`#extend`. The example adds route declarations of the form:

```ocaml
route GET "/users" list_users
```

and lowers them to ordinary syntax trees headed by `Route`.

## Added Test Source

```ocaml
#keyword "route" None None
#keyword "GET" None None
#keyword "POST" None None
#extend ["http-method", [ keyword("GET") ], [Get]]
#extend ["http-method", [ keyword("POST") ], [Post]]
#extend ["decl", [ keyword("route"), ["http-method", "method"], ["string-literal", "path"], ["term", "handler"] ], [Route method path handler]]
route GET "/users" list_users;;
route POST "/users" create_user
```

## Notes

- `http-method` is a new extension-only category.
- `decl` is extended so the new syntax can appear as a module item.
- The output tree proves that `method`, `path`, and `handler` are captured and
  substituted into the replacement tree.

## Parser Fixes

- None.
