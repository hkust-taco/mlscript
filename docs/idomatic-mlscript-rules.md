# Idomatic MLscript Rules

## List of Rules and Progress Tracker

- [x] Use object literals instead of manual field assignments
  - [x] Empty mutable objects
  - [x] Mutable objects with fields
- [x] Utilize the Ultimate Conditional Syntax
  - [x] Equality tests
  - [x] Get rid of nested `if` using `and`
  - [x] Saves a level of indentation
  - [x] Combine the techniques together
- [x] Get rid of parenthesis of function calls using `of` keywords
- [x] Organize consecutive `let` bindings using splits
- [x] Prefer `not` over `is false`
- [ ] Use `do` instead of `then ... else ()`
- [ ] Prefer quoted identifiers for symbol-like fields and values
- [ ] Drop braces from multiline object literals
- [ ] Do not overuse `of`

## Rules

### Use object literals instead of manual field assignments

#### Case 1: Empty mutable objects

`new mut Object` can be rewritten as `mut {}`.

#### Case 2: Mutable objects with fields.

Before:

```mlscript
  fun bubbleEventOptions(detail) =
    let options = new mut Object
    set
      options.bubbles = true
      options.detail = detail
    options
```

After:

```mlscript
  fun bubbleEventOptions(detail) =
    mut { bubbles: true, :detail }
```

### Utilize the Ultimate Conditional Syntax

#### Case 1: Equality Tests

Before:

```
  fun shouldHandleFsEvent(kind) =
    if
      kind === "write" then true
      kind === "delete" then true
      kind === "rename" then true
      kind === "readonly" then true
      kind === "attr" then true
      else false
```

Step 1: Use `is` when the RHS can be written as a pattern.

```
  fun shouldHandleFsEvent(kind) =
    if
      kind is "write" then true
      kind is "delete" then true
      kind is "rename" then true
      kind is "readonly" then true
      kind is "attr" then true
      else false
```

Step 2: Use disjunctive patterns.

```
  fun shouldHandleFsEvent(kind) =
    if
      kind is "write" | "delete" | "rename" | "readonly" | "attr" then true
      else false
```

Step 3: Use shorthand UCS expression when it is only a test.

```
  fun shouldHandleFsEvent(kind) =
    kind is "write" | "delete" | "rename" | "readonly" | "attr"
```

#### Get rid of nested `if` using `and`

Before:

```mlscript
      if existingTabId is Absent do
        if entry.at(1).path === filePath do
          set existingTabId = entry.at(0)
```

Step 1: Remove nested `if` using `and`.

```mlscript
      if existingTabId is Absent and
        entry.at(1).path === filePath do
          set existingTabId = entry.at(0)
```

Step 2: Put conditions on the same line to save space.

```mlscript
      if existingTabId is Absent and entry.at(1).path === filePath do
        set existingTabId = entry.at(0)
```

#### Case 3: Saves a level of indentation

Before: The body of the function is a Ultimate Conditional Syntax expression.

```mlscript
  fun showArrow(arrow) =
    if arrow.classList.contains("visible") is false do
      set arrow.style.display = "flex"
      arrow.offsetHeight
      arrow.classList.add("visible")
```

After: We can begin `if` at the same line of the function.

```mlscript
  fun showArrow(arrow) = if arrow.classList.contains("visible") is false do
    set arrow.style.display = "flex"
    arrow.offsetHeight
    arrow.classList.add("visible")
```

#### Case 4: Combine the techniques together

Before:

```mlscript
  fun handleFsEventForTab(tabId, tab, event) =
    if tab.path === event.path do
      let kind = event.("type")
      if
        kind === "delete" then this.closeTab(tabId)
        kind === "rename" then
          set
            tab.name = event.node.name
            tab.path = event.newPath
          this.updateDisplay()
        kind === "readonly" then
          set tab.readonly = event.readonly
          this.updateDisplay()
        kind === "attr" then
          set tab.attrs = nodeAttrs(event)
          this.updateDisplay()
        kind === "write" then updateTabContent(tab, event.path)
        else ()
```

Step 1: Use `is` when possible

```mlscript
  fun handleFsEventForTab(tabId, tab, event) =
    if tab.path === event.path do
      let kind = event.("type")
      if
        kind is "delete" then this.closeTab(tabId)
        kind is "rename" then
          set
            tab.name = event.node.name
            tab.path = event.newPath
          this.updateDisplay()
        kind is "readonly" then
          set tab.readonly = event.readonly
          this.updateDisplay()
        kind is "attr" then
          set tab.attrs = nodeAttrs(event)
          this.updateDisplay()
        kind is "write" then updateTabContent(tab, event.path)
        else ()
```

Step 2: Split after `is` when the prefix is the same.

```mlscript
  fun handleFsEventForTab(tabId, tab, event) =
    if tab.path === event.path do
      let kind = event.("type")
      if kind is
        "delete" then this.closeTab(tabId)
        "rename" then
          set
            tab.name = event.node.name
            tab.path = event.newPath
          this.updateDisplay()
        "readonly" then
          set tab.readonly = event.readonly
          this.updateDisplay()
        "attr" then
          set tab.attrs = nodeAttrs(event)
          this.updateDisplay()
        "write" then updateTabContent(tab, event.path)
        else ()
```

Step 3: Merge nested `if` using `and`.

```mlscript
  fun handleFsEventForTab(tabId, tab, event) =
    if tab.path === event.path and
      let kind = event.("type")
      kind is
        "delete" then this.closeTab(tabId)
        "rename" then
          set
            tab.name = event.node.name
            tab.path = event.newPath
          this.updateDisplay()
        "readonly" then
          set tab.readonly = event.readonly
          this.updateDisplay()
        "attr" then
          set tab.attrs = nodeAttrs(event)
          this.updateDisplay()
        "write" then updateTabContent(tab, event.path)
        else ()
```

Step 4: The scrutinee can be an expression.

```mlscript
  fun handleFsEventForTab(tabId, tab, event) =
    if tab.path === event.path and event.("type") is
      "delete" then this.closeTab(tabId)
      "rename" then
        set
          tab.name = event.node.name
          tab.path = event.newPath
        this.updateDisplay()
      "readonly" then
        set tab.readonly = event.readonly
        this.updateDisplay()
      "attr" then
        set tab.attrs = nodeAttrs(event)
        this.updateDisplay()
      "write" then updateTabContent(tab, event.path)
      else ()
```

### Get rid of parenthesis of function calls using `of` keywords

Before: There is a single `)` on the newline in the middle.

```mlscript
  fun setupEventListeners() =
    let panel = this
    window.addEventListener("file-open", event =>
      panel.openFile(event.detail.path, event.detail.fileName)
    )
    document.addEventListener("keydown", event => panel.handleShortcut(event))
```

After: Use `of`, which behaves like Haskell's `$`, but supports multiple arguments.

```mlscript
  fun setupEventListeners() =
    let panel = this
    window.addEventListener of "file-open", event =>
      panel.openFile(event.detail.path, event.detail.fileName)
    document.addEventListener of "keydown", event => panel.handleShortcut(event)
```

### Organize consecutive `let` bindings using splits

Before:

```mlscript
    let tabBar = this.querySelector(".tab-bar")
    let leftArrow = this.querySelector(".tab-scroll-left")
    let rightArrow = this.querySelector(".tab-scroll-right")
    let scrollInterval = null
    let scrollSpeed = 3
```

After:

```mlscript
    let
      tabBar = this.querySelector(".tab-bar")
      leftArrow = this.querySelector(".tab-scroll-left")
      rightArrow = this.querySelector(".tab-scroll-right")
      scrollInterval = null
      scrollSpeed = 3
```

### Additional rewrite patterns from PR review

#### Prefer `not` over `is false`

Use `not X` for boolean negation.

Before:

```mlscript
  if arrow.classList.contains("visible") is false do
    set arrow.style.display = "flex"
```

After:

```mlscript
  if not arrow.classList.contains("visible") do
    set arrow.style.display = "flex"
```

#### Use `do` instead of `then ... else ()`

When the conditional only performs an action and the `else` branch is `()`,
make it a `do` conditional.

Before:

```mlscript
  if shouldUpdate then
    this.updateDisplay()
  else ()
```

After:

```mlscript
  if shouldUpdate do
    this.updateDisplay()
```

#### Prefer quoted identifiers for symbol-like fields and values

When both an object field name and its value are symbol-like strings, use quoted
identifiers instead of string literals.

Before:

```mlscript
  mut { "type": "module" }
```

After:

```mlscript
  mut { 'type: 'module }
```

#### Drop braces from multiline object literals

When an object literal spans multiple lines, indentation can delimit the fields.

Before:

```mlscript
  mut {
    'type: 'compile-success
    id: id
    changes: changes
  }
```

After:

```mlscript
  mut
    'type: 'compile-success
    id: id
    changes: changes
```

#### Do not overuse `of`

Use `of` when it removes noisy parentheses in a multiline or nested call. For
simple flat calls, ordinary parentheses are clearer.

Before:

```mlscript
  window.setTimeout of hideLater, 200
```

After:

```mlscript
  window.setTimeout(hideLater, 200)
```
