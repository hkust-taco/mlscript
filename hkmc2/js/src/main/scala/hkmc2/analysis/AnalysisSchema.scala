package hkmc2.analysis

import hkmc2.{Diagnostic, Loc}
import mlscript.utils.*, shorthands.*

enum SymbolKind(val wireName: Str):
  case File extends SymbolKind("file")
  case Module extends SymbolKind("module")
  case Object extends SymbolKind("object")
  case Class extends SymbolKind("class")
  case Trait extends SymbolKind("trait")
  case Mixin extends SymbolKind("mixin")
  case Type extends SymbolKind("type")
  case Pattern extends SymbolKind("pattern")
  case Constructor extends SymbolKind("constructor")
  case Function extends SymbolKind("function")
  case Value extends SymbolKind("value")
  case MutableValue extends SymbolKind("mutable-value")
  case Parameter extends SymbolKind("parameter")
  case Field extends SymbolKind("field")
  case Unknown extends SymbolKind("unknown")

enum SymbolOrigin(val wireName: Str):
  case Source extends SymbolOrigin("source")
  case Import extends SymbolOrigin("import")
  case Synthetic extends SymbolOrigin("synthetic")
  case Error extends SymbolOrigin("error")

final case class SourceRange(
    file: Str,
    start: Int,
    end: Int,
    startLine: Int,
    startColumn: Int,
    endLine: Int,
    endColumn: Int,
)
object SourceRange:
  def fromLoc(loc: Loc): SourceRange =
    val (startLine, _, startColumn) = loc.origin.fph.getLineColAt(loc.spanStart)
    val (endLine, _, endColumn) = loc.origin.fph.getLineColAt(loc.spanEnd)
    SourceRange(
      loc.origin.fileName.toString,
      loc.spanStart,
      loc.spanEnd,
      loc.origin.startLineNum + startLine,
      startColumn,
      loc.origin.startLineNum + endLine,
      endColumn,
    )

final case class DependencyInfo(
    file: Str,
    kind: Str,
    importedName: Opt[Str],
    range: Opt[SourceRange],
)

final case class SymbolFlags(
    exported: Bool,
    overloaded: Bool,
    mutable: Bool,
    hasBody: Bool,
)

final case class SourceInfo(
    treeKind: Str,
    description: Str,
)

final case class SymbolNode(
    id: Str,
    stableId: Str,
    name: Str,
    displayName: Str,
    kind: SymbolKind,
    origin: SymbolOrigin,
    range: Opt[SourceRange],
    selectionRange: Opt[SourceRange],
    signature: Opt[Str],
    detail: Opt[Str],
    flags: SymbolFlags,
    children: Ls[SymbolNode],
    source: Opt[SourceInfo],
)

final case class FileDiagnostics(
    path: Str,
    diagnostics: Ls[Diagnostic],
)

final case class AnalysisDocument(
    schema: Str,
    version: Int,
    revision: Opt[Int],
    rootFile: Str,
    root: Opt[SymbolNode],
    diagnostics: Ls[FileDiagnostics],
    dependencies: Ls[DependencyInfo],
)
