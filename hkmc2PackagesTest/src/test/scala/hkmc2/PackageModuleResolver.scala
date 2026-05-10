package hkmc2

import scala.collection.immutable.ListMap
import scala.collection.mutable.{LinkedHashMap as MutLinkedHashMap, Map as MutMap, Queue as MutQueue, Set as MutSet}

import mlscript.utils.*, shorthands.*
import io.PlatformPath.given

import hkmc2.io.FileSystem

/** A source artifact and the package-local file generated or copied from it. */
case class VendoredFile(source: os.Path, target: os.Path)

/** A manifest vendor entry after resolving source and target roots. */
case class VendorRoot(prefix: Str, root: os.Path, targetRoot: os.Path, patterns: Ls[Str])

// We may use a different module resolver for URL modules in browsers. For
// example, `import "https://esm.sh/nanoid"` should be accepted.

class PackageModuleResolver(
    packageDir: os.Path,
    manifest: PackageManifest,
    nodeModulesPath: Opt[io.Path],
    standardLibraryRoot: os.Path,
)(using fs: io.FileSystem) extends LocalModuleResolver(Nil, nodeModulesPath):
  import PackageModuleResolver.*
  
  private case class PackageScope(root: os.Path, vendors: Ls[VendorRoot])
  
  private val packageScopes = buildPackageScopes()
  private val rootScope = packageScopes(identityPath(packageDir))
  private val allVendorRoots = packageScopes.valuesIterator.flatMap(_.vendors).toList
  private val uniqueVendorRoots = allVendorRoots.distinctBy(vendor => identityPath(vendor.root))
  private val vendorRootsByDepthDesc = uniqueVendorRoots.sortBy(vendor => -vendor.root.segmentCount)
  private val packageScopesByDepthDesc = packageScopes.valuesIterator.toList.sortBy(scope => -scope.root.segmentCount)
  
  private val closure = collectVendorClosure()
  
  val vendoredSources: Ls[VendoredFile] = closure.mlsTargets.toList.map:
    case (source, target) => VendoredFile(source, target)
  val copiedVendorFiles: Ls[VendoredFile] = closure.jsTargets.toList.map:
    case (source, target) => VendoredFile(source, target)
  
  /** Tell the compiler where a vendored source should emit its .mjs output. */
  override def targetPathForSource(sourcePath: io.Path): Opt[io.Path] =
    val source: os.Path = sourcePath
    closure.targetForSource.get(source) match
      case Some(target) => S(target)
      case None => N
  
  /** Resolve package vendor prefixes before falling back to local/node resolution. */
  override def tryResolveModulePath(path: Str): Opt[ModuleResolver.ResolvedModule] =
    tryResolveModulePath(path, packageDir)
  
  /** Resolve package vendor prefixes using the manifest of the importing file. */
  override def tryResolveModulePath(path: Str, from: io.Path): Opt[ModuleResolver.ResolvedModule] =
    tryVendorFile(path, scopeForDirectory(from)) orElse super.tryResolveModulePath(path)
  
  /** Resolve a prefixed import to its source file and generated target path. */
  private def tryVendorFile(rawPath: Str, scope: PackageScope): Opt[ModuleResolver.ResolvedModule] =
    scope.vendors.iterator.collectFirst:
      case vendor if rawPath.startsWith(vendor.prefix) =>
        val relativePath = os.RelPath(rawPath.drop(vendor.prefix.length))
        val source = vendor.root / relativePath
        closure.targetForSource.get(source) match
          case Some(target) => S(ModuleResolver.ResolvedModule.File(source, target, source.baseName))
          case None => N
    .flatten
  
  /** Collected vendored files, preserving manifest/discovery order. */
  private case class VendorClosure(
    mlsTargets:ListMap[os.Path, os.Path],
    jsTargets:ListMap[os.Path, os.Path],
    targetForSource: Map[os.Path, os.Path],
  )
  
  /** Build the vendored MLscript closure and static JavaScript asset set. */
  private def collectVendorClosure(): VendorClosure =
    val mlsTargets = MutLinkedHashMap.empty[os.Path, os.Path]
    val jsTargets = MutLinkedHashMap.empty[os.Path, os.Path]
    val copiedTargetPaths = MutSet.empty[os.Path]
    val targetForSource = MutMap.empty[os.Path, os.Path]
    val pendingMls = MutQueue.empty[os.Path]
    
    // Add one discovered MLscript vendor file and enqueue it for import scanning.
    def include(path: os.Path): Unit =
      ownerFor(path) match
        case S(vendor) =>
          if !os.exists(path) then
            throw new Exception(s"Vendored import does not exist: $path")
          path.ext match
            case "mls" =>
              val target = targetFor(vendor, path)
              if !mlsTargets.contains(path) then
                mlsTargets += path -> target
                targetForSource += path -> target
                pendingMls.enqueue(path)
            case "mjs" =>
              val sourceMls = path / os.up / s"${path.baseName}.mls"
              if os.exists(sourceMls) then
                include(sourceMls)
                targetForSource += path -> targetFor(vendor, sourceMls)
              else
                includeStatic(vendor, path)
            case "js" =>
              includeStatic(vendor, path)
            case _ => ()
        case N => ()
    
    def includeStatic(vendor: VendorRoot, path: os.Path): Unit =
      val target = targetFor(vendor, path)
      if !jsTargets.contains(path) && !copiedTargetPaths(target) then
        jsTargets += path -> target
        copiedTargetPaths += target
      targetForSource += path -> target
    
    rootScope.vendors.foreach: vendor =>
      matchedVendorFiles(vendor).foreach(include)
    
    while pendingMls.nonEmpty do
      val source = pendingMls.dequeue()
      importLiterals(source).foreach: rawImport =>
        resolveSourceImport(source, rawImport).foreach(include)
    
    uniqueVendorRoots.foreach: vendor =>
      staticJavaScriptFiles(vendor).foreach: source =>
        includeStatic(vendor, source)
    
    val compiledTargets = mlsTargets.values.toSet
    val copiedJsTargets = jsTargets.filterNot:
      case (_, target) => compiledTargets.contains(target)
    
    VendorClosure(
      collection.immutable.ListMap.from(mlsTargets),
      collection.immutable.ListMap.from(copiedJsTargets),
      targetForSource.toMap,
    )
  
  /** Expand manifest file patterns under a vendor root. */
  private def matchedVendorFiles(vendor: VendorRoot): Ls[os.Path] =
    val (literalPatterns, globPatterns) = vendor.patterns.partition(pattern => !hasGlobMeta(pattern))
    val literalFiles = literalPatterns.map(pattern => vendor.root / os.RelPath(pattern)).filter(os.isFile)
    if globPatterns.isEmpty then literalFiles
    else
      import java.nio.file.FileSystems
      val fileSystem = FileSystems.getDefault
      val matchers = globPatterns.map(pattern => fileSystem.getPathMatcher(s"glob:$pattern"))
      val globFiles = os.walk(vendor.root).iterator.filter: file =>
        if os.isFile(file) then
          val relativePath = vendor.root.toNIO.relativize(file.toNIO)
          matchers.exists(_.matches(relativePath))
        else false
      .toList
      literalFiles ::: globFiles
  
  private def hasGlobMeta(pattern: Str): Boolean =
    pattern.exists: ch =>
      ch == '*' || ch == '?' || ch == '[' || ch == ']' || ch == '{' || ch == '}'
  
  /** Collect all JavaScript assets under a vendor root without scanning them. */
  private def staticJavaScriptFiles(vendor: VendorRoot): Ls[os.Path] =
    os.walk(vendor.root).iterator.filter: file =>
      os.isFile(file) &&
        !file.startsWith(vendor.root / "vendors") &&
        (file.ext === "js" || file.ext === "mjs") &&
        !os.exists(file / os.up / s"${file.baseName}.mls")
    .toList
  
  /** Extract MLscript import string literals for rudimentary closure tracking. */
  private def importLiterals(file: os.Path): Ls[Str] =
    // TODO: This regex is deliberately rudimentary. Reuse the parsed/elaborated
    // trees cached by CompilerCtx instead, so vendoring follows real imports.
    val ImportLiteral = "(?m)^\\s*import\\s+\"([^\"]+)\"".r
    ImportLiteral.findAllMatchIn(os.read(file)).map(_.group(1)).toList
  
  /** Resolve an import seen while scanning a vendored source file. */
  private def resolveSourceImport(currentFile: os.Path, rawPath: Str): Opt[os.Path] =
    if rawPath.startsWith("./") || rawPath.startsWith("../") then
      S(currentFile / os.up / os.RelPath(rawPath))
    else if rawPath.startsWith("/") then
      S(os.Path(rawPath))
    else
      scopeForDirectory(currentFile / os.up).vendors.find(vendor => rawPath.startsWith(vendor.prefix)) match
        case Some(vendor) => S(vendor.root / os.RelPath(rawPath.drop(vendor.prefix.length)))
        case None => N
  
  /** Find which declared vendor root owns a filesystem path. */
  private def ownerFor(path: os.Path): Opt[VendorRoot] =
    vendorRootsByDepthDesc.find(vendor => path.startsWith(vendor.root)) match
      case Some(vendor) => S(vendor)
      case None => N
  
  /** Compute the package-local generated/copied path for a vendor file. */
  private def targetFor(vendor: VendorRoot, source: os.Path): os.Path =
    val relativePath = source.relativeTo(vendor.root)
    val target = vendor.targetRoot / relativePath
    if source.ext === "mls" then target / os.up / s"${target.baseName}.mjs"
    else target
  
  private def scopeForDirectory(from: io.Path): PackageScope =
    val dir: os.Path = from
    packageScopesByDepthDesc
      .find(scope => dir.startsWith(scope.root))
      .getOrElse(rootScope)
  
  private def buildPackageScopes(): ListMap[Str, PackageScope] =
    val scopes = MutLinkedHashMap.empty[Str, PackageScope]
    val queued = MutSet.empty[Str]
    val checkedManifests = MutSet.empty[Str]
    val pending = MutQueue.empty[(os.Path, PackageManifest)]
    val canonicalTargets = MutLinkedHashMap.empty[Str, os.Path]
    
    def canonicalTarget(sourceRoot: os.Path, suggestedTarget: os.Path): os.Path =
      canonicalTargets.getOrElseUpdate(identityPath(sourceRoot), suggestedTarget)
    
    def mkVendorRoot(ownerRoot: os.Path, vendor: VendorManifest): VendorRoot =
      val sourceRoot = resolvePackagePath(ownerRoot, vendor.path)
      VendorRoot(
        vendor.prefix,
        sourceRoot,
        canonicalTarget(sourceRoot, vendorTargetRoot(packageDir, vendor.prefix)),
        vendor.files,
      )
    
    def withCompilerSupport(roots: Ls[VendorRoot]): Ls[VendorRoot] =
      val supportFiles = Ls(RuntimeSourceFile, TermSourceFile)
      roots.find(_.prefix === StandardLibraryPrefix) match
        case S(_) =>
          roots.map:
            case root if root.prefix === StandardLibraryPrefix =>
              root.copy(patterns = (supportFiles ::: root.patterns).distinct)
            case root => root
        case N =>
          roots :+ VendorRoot(
            StandardLibraryPrefix,
            standardLibraryRoot,
            canonicalTarget(standardLibraryRoot, vendorTargetRoot(packageDir, StandardLibraryPrefix)),
            supportFiles,
          )
    
    def enqueue(root: os.Path): Unit =
      val key = identityPath(root)
      if !queued(key) && !scopes.contains(key) && !checkedManifests(key) then
        checkedManifests += key
        manifestAt(root).foreach: manifest =>
          queued += key
          pending.enqueue(root -> manifest)
    
    checkedManifests += identityPath(packageDir)
    queued += identityPath(packageDir)
    pending.enqueue(packageDir -> manifest)
    
    while pending.nonEmpty do
      val (root, packageManifest) = pending.dequeue()
      val key = identityPath(root)
      if !scopes.contains(key) then
        val vendors = withCompilerSupport(packageManifest.vendors.map(mkVendorRoot(root, _)))
        scopes += key -> PackageScope(root, vendors)
        vendors.foreach(vendor => enqueue(vendor.root))
    
    collection.immutable.ListMap.from(scopes)
  
  private def manifestAt(root: os.Path): Opt[PackageManifest] =
    if os.exists(root / "manifest.json") then S(PackageManifest.read(root))
    else N
  
  private def identityPath(path: os.Path): Str =
    path.toNIO.normalize.toString

object PackageModuleResolver:
  val StandardLibraryPrefix: Str = "std/"
  private val RuntimeSourceFile: Str = "Runtime.mls"
  private val TermSourceFile: Str = "Term.mls"
  
  def runtimeTarget(packageDir: os.Path): os.Path =
    vendorTargetRoot(packageDir, StandardLibraryPrefix) / "Runtime.mjs"
  
  def termTarget(packageDir: os.Path): os.Path =
    vendorTargetRoot(packageDir, StandardLibraryPrefix) / "Term.mjs"
  
  /** Resolve a manifest path relative to the package directory. */
  private def resolvePackagePath(packageDir: os.Path, path: Str): os.Path =
    if path.startsWith("/") then os.Path(path)
    else packageDir / os.RelPath(path)
  
  /** Compute the generated vendors/ root for a vendor prefix. */
  private def vendorTargetRoot(packageDir: os.Path, prefix: Str): os.Path =
    val normalizedPrefix = prefix.stripSuffix("/")
    if normalizedPrefix.isEmpty then packageDir / "vendors"
    else packageDir / "vendors" / os.RelPath(normalizedPrefix)
