package hkmc2.analysis

import hkmc2.{Loc, Origin}
import hkmc2.io
import hkmc2.semantics.*
import hkmc2.syntax
import hkmc2.syntax.Tree
import mlscript.utils.*, shorthands.*

class SymbolTreeBuilder(
    rootFile: io.Path,
    origin: Origin,
    parsed: Tree.Block,
    elaborated: Term.Blk,
):
  private var nextId: Int = 0
  private val rootFileName = rootFile.toString

  def buildRoot(): SymbolNode =
    val stableId = s"file:$rootFileName"
    SymbolNode(
      allocateId(stableId),
      stableId,
      rootFile.last,
      rootFile.toString,
      SymbolKind.File,
      SymbolOrigin.Source,
      S(fileRange()),
      S(fileRange()),
      N,
      N,
      SymbolFlags(exported = true, overloaded = false, mutable = false, hasBody = true),
      definitionNodes(elaborated.stats, stableId),
      S(SourceInfo("Block", "file")),
    )

  def dependencies(): Ls[DependencyInfo] =
    elaborated.stats.collect:
      case imp: Import =>
        DependencyInfo(
          imp.file.toString,
          importKindName(imp.kind),
          importedName(imp),
          imp.toLoc.map(SourceRange.fromLoc),
        )

  private def allocateId(stableId: Str): Str =
    nextId += 1
    s"$stableId#$nextId"

  private def fileRange(): SourceRange =
    SourceRange.fromLoc(Loc(0, origin.fph.blockStr.length, origin))

  private def definitionNodes(stats: Ls[Statement], ownerStableId: Str): Ls[SymbolNode] =
    stats.zipWithIndex.flatMap:
      case (statement, index) =>
        definitionNode(statement, ownerStableId, index)

  private def definitionNode(statement: Statement, ownerStableId: Str, index: Int): Opt[SymbolNode] =
    statement match
      case definition: TermDefinition =>
        S(termDefinitionNode(definition, ownerStableId, index))
      case definition: ClassLikeDef =>
        S(classLikeNode(definition, ownerStableId, index))
      case definition: hkmc2.semantics.TypeDef =>
        S(typeDefinitionNode(definition, ownerStableId, index))
      case _ =>
        N

  private def termDefinitionNode(definition: TermDefinition, ownerStableId: Str, index: Int): SymbolNode =
    val stableId = memberStableId(ownerStableId, definition.sym.nme, kindForTerm(definition), definition.toLoc, index)
    val parameterChildren = parameterNodes(definition.params, stableId)
    val nestedChildren = definition.body.toList.flatMap(nestedDefinitionNodes(_, stableId))
    SymbolNode(
      allocateId(stableId),
      stableId,
      definition.sym.nme,
      definition.sym.nme,
      kindForTerm(definition),
      originFor(definition.sym.nameIsMeaningful, definition.toLoc),
      definition.toLoc.map(SourceRange.fromLoc),
      definition.tsym.toLoc.map(SourceRange.fromLoc).orElse(definition.toLoc.map(SourceRange.fromLoc)),
      N,
      S(termDetail(definition)),
      SymbolFlags(
        exported = isExported(definition.annotations),
        overloaded = definition.sym.trees.distinct.length > 1,
        mutable = definition.k is syntax.MutVal,
        hasBody = definition.body.isDefined,
      ),
      parameterChildren ::: nestedChildren,
      sourceInfo(definition.sym),
    )

  private def classLikeNode(definition: ClassLikeDef, ownerStableId: Str, index: Int): SymbolNode =
    val stableId = memberStableId(ownerStableId, definition.bsym.nme, kindForClassLike(definition), definition.toLoc, index)
    val parameterChildren = definition.paramsOpt.toList.flatMap(parametersInList(_, stableId, SymbolKind.Parameter))
    val memberChildren = definitionNodes(definition.body.blk.stats, stableId)
    SymbolNode(
      allocateId(stableId),
      stableId,
      definition.bsym.nme,
      definition.bsym.nme,
      kindForClassLike(definition),
      originFor(definition.bsym.nameIsMeaningful, definition.toLoc),
      definition.toLoc.map(SourceRange.fromLoc),
      definition.sym.toLoc.map(SourceRange.fromLoc).orElse(definition.toLoc.map(SourceRange.fromLoc)),
      N,
      S(definition.kind.str),
      SymbolFlags(
        exported = isExported(definition.annotations),
        overloaded = definition.bsym.trees.distinct.length > 1,
        mutable = false,
        hasBody = definition.body.blk.stats.nonEmpty,
      ),
      parameterChildren ::: memberChildren,
      sourceInfo(definition.bsym),
    )

  private def typeDefinitionNode(definition: hkmc2.semantics.TypeDef, ownerStableId: Str, index: Int): SymbolNode =
    val stableId = memberStableId(ownerStableId, definition.bsym.nme, SymbolKind.Type, definition.toLoc, index)
    SymbolNode(
      allocateId(stableId),
      stableId,
      definition.bsym.nme,
      definition.bsym.nme,
      SymbolKind.Type,
      originFor(definition.bsym.nameIsMeaningful, definition.toLoc),
      definition.toLoc.map(SourceRange.fromLoc),
      definition.sym.toLoc.map(SourceRange.fromLoc).orElse(definition.toLoc.map(SourceRange.fromLoc)),
      N,
      S("type"),
      SymbolFlags(
        exported = isExported(definition.annotations),
        overloaded = definition.bsym.trees.distinct.length > 1,
        mutable = false,
        hasBody = definition.rhs.isDefined,
      ),
      Nil,
      sourceInfo(definition.bsym),
    )

  private def nestedDefinitionNodes(term: Term, ownerStableId: Str): Ls[SymbolNode] =
    term match
      case Term.Blk(stats, res) =>
        definitionNodes(stats, ownerStableId) ::: nestedDefinitionNodes(res, ownerStableId)
      case _ =>
        term.subTerms.toList.flatMap(nestedDefinitionNodes(_, ownerStableId))

  private def parameterNodes(params: Ls[ParamList], ownerStableId: Str): Ls[SymbolNode] =
    params.zipWithIndex.flatMap:
      case (paramList, listIndex) =>
        parametersInList(paramList, s"$ownerStableId/params:$listIndex", SymbolKind.Parameter)

  private def parametersInList(paramList: ParamList, ownerStableId: Str, kind: SymbolKind): Ls[SymbolNode] =
    paramList.allParams.zipWithIndex.map:
      case (param, index) =>
        val stableId = memberStableId(ownerStableId, param.sym.nme, kind, param.toLoc, index)
        SymbolNode(
          allocateId(stableId),
          stableId,
          param.sym.nme,
          param.sym.nme,
          kind,
          originFor(param.sym.name.nonEmpty, param.toLoc),
          param.toLoc.map(SourceRange.fromLoc),
          param.sym.toLoc.map(SourceRange.fromLoc).orElse(param.toLoc.map(SourceRange.fromLoc)),
          N,
          N,
          SymbolFlags(exported = false, overloaded = false, mutable = param.flags.mut, hasBody = false),
          Nil,
          N,
        )

  private def memberStableId(
      ownerStableId: Str,
      name: Str,
      kind: SymbolKind,
      loc: Opt[Loc],
      index: Int,
  ): Str =
    val locationPart = loc.fold(s"index:$index")(loc => s"${loc.origin.fileName}:${loc.spanStart}:${loc.spanEnd}")
    s"$ownerStableId/${kind.wireName}:$name@$locationPart"

  private def kindForTerm(definition: TermDefinition): SymbolKind =
    definition.k match
      case syntax.Fun => SymbolKind.Function
      case syntax.MutVal => SymbolKind.MutableValue
      case _: syntax.ValLike => SymbolKind.Value
      case _ => SymbolKind.Unknown

  private def kindForClassLike(definition: ClassLikeDef): SymbolKind =
    definition.kind match
      case syntax.Mod => SymbolKind.Module
      case syntax.Obj => SymbolKind.Object
      case syntax.Cls => SymbolKind.Class
      case syntax.Pat => SymbolKind.Pattern

  private def originFor(nameIsMeaningful: Bool, loc: Opt[Loc]): SymbolOrigin =
    if !nameIsMeaningful then SymbolOrigin.Synthetic
    else
      loc match
        case S(loc) if loc.origin.fileName.toString =/= rootFileName => SymbolOrigin.Import
        case _ => SymbolOrigin.Source

  private def isExported(annotations: Ls[Annot]): Bool =
    !annotations.exists:
      case Annot.Modifier(syntax.Keyword.`private`) => true
      case _ => false

  private def termDetail(definition: TermDefinition): Str =
    definition.k match
      case syntax.Fun => "function"
      case syntax.MutVal => "mutable value"
      case syntax.ImmutVal => "value"
      case syntax.Ins => "implicit instance"
      case syntax.LetBind => "let binding"
      case syntax.HandlerBind => "handler binding"

  private def sourceInfo(symbol: BlockMemberSymbol): Opt[SourceInfo] =
    symbol.trees.headOption.map: tree =>
      val treeKind = tree match
        case _: Tree.TypeDef => "TypeDef"
        case _: Tree.TermDef => "TermDef"
      SourceInfo(treeKind, tree.describe)

  private def importKindName(kind: ImportKind): Str =
    kind match
      case ImportKind.Default => "default"
      case ImportKind.Namespace => "namespace"
      case ImportKind.Named(_) => "named"

  private def importedName(imp: Import): Opt[Str] =
    imp.kind match
      case ImportKind.Named(importedName) => S(importedName)
      case _ => S(imp.sym.nme)

end SymbolTreeBuilder
