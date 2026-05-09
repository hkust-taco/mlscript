package hkmc2

import scala.collection.immutable.ListMap
import scala.collection.mutable.{LinkedHashMap as MutLinkedHashMap, ListMap as MutListMap, Map as MutMap, Queue as MutQueue}

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
)(using fs: io.FileSystem) extends LocalModuleResolver(Nil, nodeModulesPath):
  import PackageModuleResolver.*
  
  private val vendorRoots: Ls[VendorRoot] =
    manifest.vendors.map: vendor =>
      VendorRoot(
        vendor.prefix,
        resolvePackagePath(packageDir, vendor.path),
        vendorTargetRoot(packageDir, vendor.prefix),
        vendor.files,
      )
  
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
    tryVendorFile(path) orElse super.tryResolveModulePath(path)
  
  /** Resolve a prefixed import to its source file and generated target path. */
  private def tryVendorFile(rawPath: Str): Opt[ModuleResolver.ResolvedModule] =
    vendorRoots.iterator.collectFirst:
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
    val targetForSource = MutMap.empty[os.Path, os.Path]
    val pendingMls = MutQueue.empty[os.Path]
    
    // Add one discovered MLscript vendor file and enqueue it for import scanning.
    def include(path: os.Path): Unit =
      if !os.exists(path) then
        throw new Exception(s"Vendored import does not exist: $path")
      ownerFor(path) match
        case S(vendor) if path.ext === "mls" =>
          val target = targetFor(vendor, path)
          if !mlsTargets.contains(path) then
            mlsTargets += path -> target
            targetForSource += path -> target
            pendingMls.enqueue(path)
        case S(_) => ()
        case N =>
          throw new Exception(s"Vendored import is outside declared vendor roots: $path")
    
    vendorRoots.foreach: vendor =>
      matchedVendorFiles(vendor).foreach(include)
    
    while pendingMls.nonEmpty do
      val source = pendingMls.dequeue()
      importLiterals(source).foreach: rawImport =>
        resolveSourceImport(source, rawImport).foreach(include)
    
    val compiledTargets = mlsTargets.values.toSet
    vendorRoots.foreach: vendor =>
      staticJavaScriptFiles(vendor).foreach: source =>
        val target = targetFor(vendor, source)
        if compiledTargets.contains(target) then
          targetForSource += source -> target
        else if !jsTargets.contains(source) && !jsTargets.values.exists(_ == target) then
          jsTargets += source -> target
          targetForSource += source -> target
    
    VendorClosure(
      collection.immutable.ListMap.from(mlsTargets),
      collection.immutable.ListMap.from(jsTargets),
      targetForSource.toMap,
    )
  
  /** Expand manifest file patterns under a vendor root. */
  private def matchedVendorFiles(vendor: VendorRoot): Ls[os.Path] =
    import java.nio.file.FileSystems
    vendor.patterns.iterator.flatMap: pattern =>
      val matcher = FileSystems.getDefault.getPathMatcher(s"glob:$pattern")
      os.walk(vendor.root).iterator.filter: file =>
        os.isFile(file) && matcher.matches(vendor.root.toNIO.relativize(file.toNIO))
    .toList
  
  /** Collect all JavaScript assets under a vendor root without scanning them. */
  private def staticJavaScriptFiles(vendor: VendorRoot): Ls[os.Path] =
    os.walk(vendor.root).iterator.filter: file =>
      os.isFile(file) && (file.ext === "js" || file.ext === "mjs")
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
      vendorRoots.find(vendor => rawPath.startsWith(vendor.prefix)) match
        case Some(vendor) => S(vendor.root / os.RelPath(rawPath.drop(vendor.prefix.length)))
        case None => N
  
  /** Find which declared vendor root owns a filesystem path. */
  private def ownerFor(path: os.Path): Opt[VendorRoot] =
    vendorRoots.find(vendor => path.startsWith(vendor.root)) match
      case Some(vendor) => S(vendor)
      case None => N
  
  /** Compute the package-local generated/copied path for a vendor file. */
  private def targetFor(vendor: VendorRoot, source: os.Path): os.Path =
    val relativePath = source.relativeTo(vendor.root)
    val target = vendor.targetRoot / relativePath
    if source.ext === "mls" then target / os.up / s"${target.baseName}.mjs"
    else target

object PackageModuleResolver:
  /** Resolve a manifest path relative to the package directory. */
  private def resolvePackagePath(packageDir: os.Path, path: Str): os.Path =
    if path.startsWith("/") then os.Path(path)
    else packageDir / os.RelPath(path)
  
  /** Compute the generated vendors/ root for a vendor prefix. */
  private def vendorTargetRoot(packageDir: os.Path, prefix: Str): os.Path =
    val normalizedPrefix = prefix.stripSuffix("/")
    if normalizedPrefix.isEmpty then packageDir / "vendors"
    else packageDir / "vendors" / os.RelPath(normalizedPrefix)
