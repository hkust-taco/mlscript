package hkmc2

import collection.mutable.{Map as MutMap, Set as MutSet}

import hkmc2.utils.*, shorthands.*
import hkmc2.io
import utils.TraceLogger

import semantics.*
import Elaborator.*


import CompilerCache.*


class CompilerCtx(
    val importing: Opt[(io.Path, CompilerCtx)],
    val beingCompiled: Set[io.Path],
    val fs: io.FileSystem,
    cache: CompilerCache,
    /** Build-local sink for artifacts requested while elaborating the caller, if any. */
    private val dependencyRecorder: Opt[CompilerCtx.DependencyRecorder],
    /** Where the prelude and runtime of this compilation session live. Fixed alongside
      * `rootConfig`, and for the same reason: they take part in lowering — the lowered program
      * imports the runtime by path — so a unit lowered against different ones is a different
      * artifact, and the units cached here are shared. */
    val paths: MLsCompiler.Paths,
    /** The configuration of the whole compilation session, under which every compilation unit
      * reached through this context is elaborated. It is fixed when the context is created:
      * the units cached here are shared, so their elaboration — and hence the identity of the
      * symbols they define — must not depend on which of them is compiled or imported first. */
    val rootConfig: Config,
):
  
  def allFilesBeingImported: Ls[io.Path] =
    importing match
    case S((path, parent)) => path :: parent.allFilesBeingImported
    case N => Nil

  /** Run a nested artifact request while publishing its dependency on the artifact currently
    * being built. The cache owns this shared state because several root compilations may use
    * distinct `CompilerCtx` chains while contending for the same artifact path locks. */
  private[hkmc2] def withActiveDependency[A]
        (file: io.Path)
        (onCycle: Ls[io.Path] => A)
        (request: => A)
        : A =
    importing match
    case S((requester, _)) => cache.withActiveDependency(requester, file)(onCycle)(request)
    case N => request
  
  private def derive(newFile: io.Path, recorder: CompilerCtx.DependencyRecorder): CompilerCtx =
    CompilerCtx(S(newFile, this), beingCompiled + newFile, fs, cache, S(recorder), paths, rootConfig)
  
  /** Elaborate (and, when compiler paths are set, lower) a compilation unit, caching the result.
    *
    * Note that the importer's configuration is deliberately not a parameter: a compilation unit's
    * elaboration must depend only on the unit itself, or importers would keep invalidating each
    * other's cached artifact — and a single worksheet could then observe symbols from two different
    * elaborations of the same file (say, `State.tupleSymbol` from one and the symbols reached
    * through an `import` statement from another), which is silently inconsistent. */
  def getElaboratedBlock
        (file: io.Path, prelude: Ctx)
        (using TL, Raise)
        : Artifact =
    
    val lastMod = fs.getLastChangedTimestamp(file)
    
    def mk =
      val dependencies = new CompilerCtx.DependencyRecorder
      val modulePath = (file.up / io.RelPath(file.baseName + ".mjs")).toString
      val state = new Elaborator.State
      given Elaborator.State = state

      given Config = rootConfig

      given SymbolPrinter = new SymbolPrinter(
        Scope.empty(Scope.Cfg.default.copy(
          escapeChars = false,
          useSuperscripts = true,
          includeZero = true,
        ))
      )
      val backendTL = new TraceLogger:
        override def doTrace: Bool = false

      val parse =
        given CompilerCtx = this
        ParserSetup(file)
      given Elaborator.Ctx = prelude
      val artifactCtx = derive(parse.origin.fileName, dependencies)
      val elab =
        given CompilerCtx = artifactCtx
        Elaborator(tl, file.up, prelude)

      val parsed = parse.resultBlk
      val nme = file.baseName
      val exportedSymbol = parsed.definedSymbols.find(_._1 === nme).map(_._2)
      def collectCompilationUnitSymbols(program: codegen.Program): Set[codegen.BoundSymbol] =
        program.main match
        case codegen.Scoped(syms, _) =>
          syms.iterator.collect:
            case sym: BlockMemberSymbol => sym
          .toSet
        case _ => Set.empty
      val (blk0, _) = elab.importFrom(parsed)
      if file.toString === paths.runtimeSourceFile.toString then
        state.initRuntimeSymbolsFromBlock(blk0)
      else
        state.initRuntimeSymbolsFromFile(paths.runtimeSourceFile, prelude)(
          using tl, summon[Raise], artifactCtx)

      val artifactConfig = Config.extractConfigFromStats(blk0)
      artifactConfig.givenIn:
        given Elaborator.State = state
        val resolver = Resolver(backendTL)
        resolver.traverseBlock(blk0)(using Resolver.ICtx.empty)
      def findQuote(t: semantics.Statement): Bool = t match
        case Term.Quoted(_) | Term.Unquoted(_) => true
        case Term.Ref(sym) => sym === State.termSymbol
        case _ => t.subTerms.exists(findQuote)
      val hasQuote = findQuote(blk0)
      val blk = new Term.Blk(
        Import(State.runtimeSymbol, paths.runtimeFile.toString, paths.runtimeFile) ::
          // Only import `Term.mls` when necessary.
          (if hasQuote then
            Import(State.termSymbol, paths.termFile.toString, paths.termFile) :: blk0.stats
          else
            blk0.stats),
        blk0.res
      )
      val importedModulePaths = CompilerCtx.collectImportedModulePaths(blk)(using state)
      val compilationUnit = CompilationUnit(
        modulePath,
        exportedSymbol,
        artifactConfig,
        importedModulePaths,
      )
      state.publishCompilationUnit(compilationUnit)

      // Runs the compilation pipeline on a freshly lowered compilation unit.
      // The unit's own top-level symbols are preserved as a private ABI, because other
      // compilation units may inline bodies of this one that still refer to them.
      // Note that this must run the *whole* pipeline (and not just the lowering proper),
      // as the `irDefn` fields the inliner reads are owned by the latest rewrite of each definition,
      // and only fully-transformed definitions are valid to splice into another unit.
      def optimize(lowered: codegen.Program): codegen.Program =
        given Config = artifactConfig
        val printer = (p: codegen.Program) => p.showAsTree // TODO: proper printing like in diff-tests
        val pipeline = new codegen.CompilationPipeline:
          override def extraSymbolsToPreserveFrom(prog: codegen.Program): Set[codegen.BoundSymbol] =
            collectCompilationUnitSymbols(prog)
        backendTL.givenIn:
          pipeline.run(lowered, printer, exportedSymbol.toSet, backendTL)

      // Every compilation unit is lowered, so that its symbols carry the IR definitions an
      // importer's inliner may splice in — and so that the importer never has to lower it itself,
      // which it could only do by elaborating it afresh, under symbols nobody else would share.
      val ir =
        artifactConfig.givenIn:
          given Elaborator.State = state
          val low = backendTL.givenIn:
            new codegen.Lowering()(using artifactConfig, backendTL, summon[Raise], state, prelude, summon[SymbolPrinter])
          optimize(low.program(blk, Set.empty))

      state.publishCompilationUnitAbi:
        CompilationUnitAbi:
          CompilerCtx.allocateModulePrivateExportNames(ir)(using state, summon[Raise])
      Artifact(parsed, blk0, ir, artifactConfig, prelude, state, compilationUnit, rootConfig, dependencies.result, lastMod)
    
    val artifact = cache.upsert(file)(
      isCurrent = (cachedFile, art) =>
        // * The root configuration is fixed for a whole compilation session — nothing mutates it —
        // * so a cached artifact was necessarily built with the one we are asking for now.
        // * A mismatch means two contexts with different root configurations share a cache, which
        // * would give the same source file two elaborations and hence two sets of symbols.
        // * We keep the cached artifact rather than re-elaborating: reusing one identity is the
        // * lesser evil, and the diagnostic makes the misuse visible instead of silent.
        softAssert(art.rootConfig === rootConfig,
          s"Cached artifact for $cachedFile was elaborated under a different root configuration")
        def sourceIsCurrent(path: io.Path, timestamp: Long): Bool =
          try timestamp >= fs.getLastChangedTimestamp(path)
          catch case _: io.FileSystem.FileNotFoundException => false
        (art.ctx is prelude)
          && sourceIsCurrent(cachedFile, art.lastChangedTimestamp)
          && art.dependencies.forall(dep => sourceIsCurrent(dep.path, dep.lastChangedTimestamp)),
      create = mk,
    )
    dependencyRecorder.foreach(_.note(file, artifact))
    artifact

  def getPrelude
        (file: io.Path)
        (using tl: TL, raise: Raise)
        : PreludeArtifact =
    // The prelude context is shared so every compilation unit sees the same prelude
    // symbols. Callers still elaborate their own files with a fresh State; the frozen
    // State remains the owner captured by the prelude symbols themselves.
    // The prelude is elaborated once per context, under its root configuration: were it
    // elaborated per requester, cached compilation units would keep referring to whichever
    // elaboration came first, and a body inlined across units would then carry prelude symbols
    // that the importing file does not recognize.
    val lastMod = fs.getLastChangedTimestamp(file)
    cache.upsertPrelude(file)(
      isCurrent = art =>
        // * See the corresponding assertion in `getElaboratedBlock` above.
        softAssert(art.config === rootConfig,
          s"Cached prelude for $file was elaborated under a different root configuration")
        art.lastChangedTimestamp >= lastMod,
      create =
        val state = new Elaborator.State
        given Elaborator.State = state
        given Config = rootConfig
        given CompilerCtx = this
        val parse = ParserSetup(file)
        val elab = Elaborator(tl, file.up, Ctx.empty)
        val initCtx = State.init.nestLocal("prelude")
        val (blk, ctx) = elab.importFrom(parse.resultBlk)(using initCtx)
        PreludeArtifact(parse.resultBlk, blk, ctx, state, rootConfig, lastMod),
    )
  
  
object CompilerCtx:
  
  inline def get(using cctx: CompilerCtx) = cctx


  /** Collect import provenance after elaboration has assembled all user and synthetic imports.
    *
    * Only locally-owned symbols belong in the table. An unaliased `.mls` import retains the
    * imported compilation unit's symbol, whose defining-unit provenance must remain authoritative.
    */
  private def collectImportedModulePaths(blk: Term.Blk)(using state: State): Map[ImportSymbol, Str] =
    var paths = Map.empty[ImportSymbol, Str]
    def collect(statement: semantics.Statement): Unit =
      statement match
      case Import(sym, path, _) if sym.getState is state =>
        paths.get(sym) match
        case S(previous) => assert(previous === path, (sym, previous, path))
        case N => paths = paths.updated(sym, path)
      case _ =>
      statement.subStatements.foreach(collect)
    collect(blk)
    paths

  def fresh(fs: io.FileSystem, paths: MLsCompiler.Paths, rootConfig: Config): CompilerCtx =
    CompilerCtx(N, Set.empty, fs, new PlatformCompilerCache, N, paths, rootConfig)

  private[hkmc2] final class DependencyRecorder:
    // Keep the timestamp in the set element rather than mapping paths to timestamps. If a source
    // changes while one artifact is being built and two branches observe different versions, both
    // versions remain in the snapshot; the older one then makes the artifact immediately stale.
    private val dependencies = MutSet.empty[SourceDependency]

    def note(path: io.Path, artifact: Artifact): Unit =
      dependencies += SourceDependency(path, artifact.lastChangedTimestamp)
      dependencies ++= artifact.dependencies

    def result: Set[SourceDependency] = dependencies.toSet
  
  
  private val modulePrivatePrefix = "_$_modulePrivate_$_"
  
  import codegen.*
  
  /** Allocate the defining unit's private export namespace once so all importers reuse it.
    *
    * Ordinary top-level names are reserved first, then the private aliases are allocated with a
    * distinctive prefix. `Scope` handles escaping and collision suffixes exactly as it does for
    * other generated JavaScript names; symbol UIDs influence traversal order only and never become
    * part of the external name. */
  def allocateModulePrivateExportNames(p: Program)(using State, Raise): Map[BlockMemberSymbol, Str] =
    p.main match
    case Scoped(syms, _) =>
      val orderedSymbols = syms.toList.sortBy(_.uid)
      val privateNameScope = Scope.empty(Scope.Cfg.default)
      orderedSymbols.foreach(privateNameScope.allocateName(_))
      orderedSymbols.collect:
        case sym: BlockMemberSymbol =>
          sym -> privateNameScope.allocateName(sym, prefix = modulePrivatePrefix, shadow = true)
      .toMap
    case _ => Map.empty
  
end CompilerCtx



object CompilerCache:
  
  class Artifact(
    val tree: syntax.Tree.Block,
    val term: semantics.Term.Blk,
    val ir: codegen.Program,
    val config: Config,
    val ctx: Elaborator.Ctx,
    val state: Elaborator.State,
    val compilationUnit: Elaborator.CompilationUnit,
    val rootConfig: Config,
    val dependencies: Set[SourceDependency],
    val lastChangedTimestamp: Long,
  )

  /** The version of one transitive source dependency observed while building an artifact. */
  final case class SourceDependency(path: io.Path, lastChangedTimestamp: Long)

  class PreludeArtifact(
    val tree: syntax.Tree.Block,
    val term: semantics.Term.Blk,
    val ctx: Elaborator.Ctx,
    val state: Elaborator.State,
    val config: Config,
    val lastChangedTimestamp: Long,
  )

  /** The dependencies between artifact builds that are active right now.
    *
    * Registering an edge and checking whether it closes a cycle are one short synchronized
    * operation. The expensive artifact request runs outside this monitor, while its edge remains
    * visible to other requesters. Edge counts make overlapping equal requests safe, and the
    * scoped API guarantees cleanup when a request fails. */
  private[hkmc2] final class ActiveDependencyGraph:
    private val edges = MutMap.empty[io.Path, MutMap[io.Path, Int]]

    private def pathBetween(from: io.Path, to: io.Path): Opt[Ls[io.Path]] =
      def loop(current: io.Path, visited: Set[io.Path]): Opt[Ls[io.Path]] =
        if current === to then S(current :: Nil)
        else if visited.contains(current) then N
        else
          edges.get(current).iterator
            .flatMap(_.keys)
            .toArray
            .sortBy(_.toString)
            .iterator
            .map(next => loop(next, visited + current).map(current :: _))
            .collectFirst:
              case S(path) => path
      loop(from, Set.empty)

    private def register(from: io.Path, to: io.Path): Either[Ls[io.Path], Unit] = synchronized:
      pathBetween(to, from) match
      case S(path) => Left(from :: path)
      case N =>
        val outgoing = edges.getOrElseUpdate(from, MutMap.empty)
        outgoing(to) = outgoing.getOrElse(to, 0) + 1
        Right(())

    private def unregister(from: io.Path, to: io.Path): Unit = synchronized:
      edges.get(from) match
      case S(outgoing) =>
        outgoing.get(to) match
        case S(1) =>
          outgoing.remove(to)
          if outgoing.isEmpty then edges.remove(from)
        case S(count) => outgoing(to) = count - 1
        case N => assert(false, s"Inactive compiler dependency $from -> $to was released")
      case N => assert(false, s"Inactive compiler dependency $from -> $to was released")

    def withDependency[A]
          (from: io.Path, to: io.Path)
          (onCycle: Ls[io.Path] => A)
          (request: => A)
          : A =
      register(from, to) match
      case Left(cycle) => onCycle(cycle)
      case Right(()) =>
        try request
        finally unregister(from, to)

  /** A cache whose expensive computations are serialized per path rather than globally.
    *
    * The supplied maps provide the platform's concurrency semantics: JVM uses `TrieMap`, while
    * JavaScript uses ordinary mutable maps on its single execution thread. Keeping a stable lock
    * per path makes every successful requester observe the same published artifact — and therefore
    * the same symbol identities — without a cache-wide monitor. */
  private[hkmc2] final class ArtifactCache[A <: AnyRef](
      entries: MutMap[io.Path, A],
      pathLocks: MutMap[io.Path, AnyRef],
  ):
    private def pathLock(path: io.Path): AnyRef =
      pathLocks.getOrElseUpdate(path, new Object)

    def getOrCreate(path: io.Path)(isCurrent: A => Bool, create: => A): A =
      pathLock(path).synchronized:
        entries.get(path) match
        case S(entry) if isCurrent(entry) => entry
        case _ =>
          val entry = create
          entries(path) = entry
          entry
  
end CompilerCache


trait CompilerCache:
  // TODO also use hash comparison to avoid needless re-parses?

  protected def elabCache: CompilerCache.ArtifactCache[Artifact]
  protected def preludeCache: CompilerCache.ArtifactCache[PreludeArtifact]

  // This mutable graph belongs to one cache, just like the path locks it protects requesters
  // from deadlocking on. It must not be moved to symbols or other globally shared compiler state.
  private val activeDependencies = new ActiveDependencyGraph

  private[hkmc2] def withActiveDependency[A]
        (from: io.Path, to: io.Path)
        (onCycle: Ls[io.Path] => A)
        (request: => A)
        : A =
    activeDependencies.withDependency(from, to)(onCycle)(request)
  
  /** Return the current artifact at `path`, or atomically rebuild that artifact.
    *
    * The artifact records all of its transitive source dependencies, so `isCurrent` can decide
    * whether this particular artifact must be rebuilt without scanning or clearing unrelated
    * cache entries. `create` runs under a lock dedicated to `path`: concurrent requesters reuse
    * one symbol identity for the same file, while unrelated files remain free to elaborate in
    * parallel. Imports recursively acquire their own path locks rather than holding a cache-wide
    * monitor through the entire rebuilding chain. */
  def upsert(path: io.Path)(isCurrent: (io.Path, Artifact) => Bool, create: => Artifact): Artifact =
    elabCache.getOrCreate(path)(isCurrent(path, _), create)

  /** Diff-test and compile-test runners request the Prelude in parallel.
    *
    * Only the first requester for this path elaborates it; concurrent requesters block on that
    * path alone and reuse the same frozen artifact once it is available. */
  def upsertPrelude(path: io.Path)(isCurrent: PreludeArtifact => Bool, create: => PreludeArtifact): PreludeArtifact =
    preludeCache.getOrCreate(path)(isCurrent, create)
  
end CompilerCache
