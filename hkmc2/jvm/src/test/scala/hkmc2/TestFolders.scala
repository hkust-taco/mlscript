package hkmc2

import mlscript.utils._, shorthands._


/** Centralized definitions of which test directories belong to which SBT project.
  * Each project specifies the `mlscript/` subdirectories (for diff tests) and the
  * `mlscript-compile/` subdirectories (for compile tests) that it owns. */
object TestFolders:
  
  /** Helper to check whether `file` is inside (i.e. a descendant of) `dir`. */
  def isInDir(file: os.Path, dir: os.Path): Bool =
    file.startsWith(dir)
  
  /** The base test directory: `hkmc2/shared/src/test`. */
  def mainTestDir(wd: os.Path): os.Path =
    wd/"hkmc2"/"shared"/"src"/"test"
  
  /** The diff test directory: `hkmc2/shared/src/test/mlscript`. */
  def diffTestDir(wd: os.Path): os.Path =
    mainTestDir(wd)/"mlscript"
  
  /** The compile test directory: `hkmc2/shared/src/test/mlscript-compile`. */
  def compileTestDir(wd: os.Path): os.Path =
    mainTestDir(wd)/"mlscript-compile"
  
  // ——— Diff test subdirectories excluded from the main DiffTestRunner ———
  
  /** Diff test subdirectories that belong to the hkmc2NofibTests project. */
  def nofibDiffDir(wd: os.Path): os.Path =
    diffTestDir(wd)/"nofib"
  
  /** Diff test subdirectories that belong to the hkmc2AppsTests project. */
  def appsDiffDir(wd: os.Path): os.Path =
    diffTestDir(wd)/"apps"
  
  /** Diff test subdirectories that belong to the hkmc2WasmTests project. */
  def wasmDiffDir(wd: os.Path): os.Path =
    diffTestDir(wd)/"wasm"
  
  /** Diff test directories that are always excluded (staging, mlscript-compile). */
  def alwaysExcludedDiffDirs(wd: os.Path): Ls[os.Path] =
    (diffTestDir(wd)/"ucs"/"staging") :: compileTestDir(wd) :: Nil
  
  /** All diff test directories excluded from the main DiffTestRunner. */
  def mainExcludedDiffDirs(wd: os.Path): Ls[os.Path] =
    nofibDiffDir(wd) ::
    appsDiffDir(wd) ::
    wasmDiffDir(wd) ::
    alwaysExcludedDiffDirs(wd)
  
  /** Check whether a file should be excluded from the given list of excluded
    * directories and/or individual files. */
  def isExcluded(file: os.Path, excludedDirs: Ls[os.Path]): Bool =
    excludedDirs.exists(dir => isInDir(file, dir))
  
  // ——— Compile test directories ———
  
  /** Compile test directories for the main hkmc2JVM project.
    * We walk from `mainTestDir` so test names include the `mlscript-compile/` prefix. */
  def mainCompileDirs(wd: os.Path): Ls[os.Path] =
    mainTestDir(wd) :: Nil
  
  /** Directories whose compile files are excluded from the main CompileTestRunner. */
  def mainExcludedCompileDirs(wd: os.Path): Ls[os.Path] =
    nofibCompileDirs(wd) ::: appsCompileDirs(wd) ::: wasmCompileDirs(wd)
  
  /** Compile test directories for the hkmc2NofibTests project.
    * We walk from `bench/` so test names include the `mlscript-compile/` prefix. */
  def nofibCompileDirs(wd: os.Path): Ls[os.Path] =
    compileTestDir(wd)/"nofib" :: Nil
  
  /** Compile test directories for the hkmc2AppsTests project.
    * We walk from `mlscript-compile/apps/` directly. */
  def appsCompileDirs(wd: os.Path): Ls[os.Path] =
    compileTestDir(wd)/"apps" :: Nil
  
  /** Compile test directories for the hkmc2WasmTests project.
    * We walk from `mainTestDir` so test names include the `mlscript-compile/` prefix.. */
  def wasmCompileDirs(wd: os.Path): Ls[os.Path] =
    compileTestDir(wd)/"wasm" :: Nil
  
end TestFolders

