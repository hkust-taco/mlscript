package hkmc2.analysis

import scala.scalajs.js
import js.JSConverters.*

import hkmc2.{Diagnostic, Message, ShowCtx}
import mlscript.utils.*, shorthands.*

object AnalysisJsCodec:

  def document(document: AnalysisDocument): js.Dynamic =
    val result = js.Dynamic.literal(
      schema = document.schema,
      version = document.version,
      rootFile = document.rootFile,
      root = document.root.map(symbolNode).orNull,
      diagnostics = document.diagnostics.map(fileDiagnostics).toJSArray,
      dependencies = document.dependencies.map(dependencyInfo).toJSArray,
    )
    document.revision.foreach: revision =>
      result.updateDynamic("revision")(revision)
    result

  private def symbolNode(node: SymbolNode): js.Dynamic =
    val result = js.Dynamic.literal(
      id = node.id,
      stableId = node.stableId,
      name = node.name,
      displayName = node.displayName,
      kind = node.kind.wireName,
      origin = node.origin.wireName,
      range = node.range.map(sourceRange).orNull,
      selectionRange = node.selectionRange.map(sourceRange).orNull,
      flags = symbolFlags(node.flags),
      children = node.children.map(symbolNode).toJSArray,
    )
    node.signature.foreach: signature =>
      result.updateDynamic("signature")(signature)
    node.detail.foreach: detail =>
      result.updateDynamic("detail")(detail)
    node.source.foreach: source =>
      result.updateDynamic("source")(sourceInfo(source))
    result

  private def sourceRange(range: SourceRange): js.Dynamic =
    js.Dynamic.literal(
      file = range.file,
      start = range.start,
      end = range.end,
      startLine = range.startLine,
      startColumn = range.startColumn,
      endLine = range.endLine,
      endColumn = range.endColumn,
    )

  private def symbolFlags(flags: SymbolFlags): js.Dynamic =
    js.Dynamic.literal(
      exported = flags.exported,
      overloaded = flags.overloaded,
      mutable = flags.mutable,
      hasBody = flags.hasBody,
    )

  private def sourceInfo(source: SourceInfo): js.Dynamic =
    js.Dynamic.literal(
      treeKind = source.treeKind,
      description = source.description,
    )

  private def dependencyInfo(info: DependencyInfo): js.Dynamic =
    val result = js.Dynamic.literal(
      file = info.file,
      kind = info.kind,
      range = info.range.map(sourceRange).orNull,
    )
    info.importedName.foreach: importedName =>
      result.updateDynamic("importedName")(importedName)
    result

  private def fileDiagnostics(file: FileDiagnostics): js.Dynamic =
    js.Dynamic.literal(
      path = file.path,
      diagnostics = file.diagnostics.map(diagnostic).toJSArray,
    )

  private def diagnostic(diagnostic: Diagnostic): js.Dynamic =
    js.Dynamic.literal(
      kind = diagnostic.kind.toString().toLowerCase(),
      source = diagnostic.source.toString().toLowerCase(),
      mainMessage = diagnostic.theMsg,
      allMessages = diagnostic.allMsgs.map:
        case (message, loc) =>
          lazy val ctx = ShowCtx.mk:
            message.bits.collect:
              case Message.Code(t) => t
          js.Dynamic.literal(
            messageBits = message.bits.map:
              case Message.Text(text) => js.Dynamic.literal(text = text)
              case Message.Code(ty) => ty.showIn(0)(using ctx)
            .toJSArray,
            location = loc match
              case S(loc) => js.Dynamic.literal(
                start = loc.spanStart,
                end = loc.spanEnd,
              )
              case N => null
          )
      .toJSArray,
    )

end AnalysisJsCodec
