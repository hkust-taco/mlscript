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
- [ ] Get rid of parenthesis of function calls using `of` keywords
- [ ] Organize consecutive `let` bindings using splits

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
