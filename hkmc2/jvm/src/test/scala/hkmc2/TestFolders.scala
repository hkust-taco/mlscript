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
  def mainTestDir(workingDir: os.Path): os.Path =
    workingDir/"hkmc2"/"shared"/"src"/"test"
  
  /** The diff test directory: `hkmc2/shared/src/test/mlscript`. */
  def diffTestDir(workingDir: os.Path): os.Path =
    mainTestDir(workingDir)/"mlscript"
  
  /** The compile test directory: `hkmc2/shared/src/test/mlscript-compile`. */
  def compileTestDir(workingDir: os.Path): os.Path =
    mainTestDir(workingDir)/"mlscript-compile"
  
  // ——— Diff test subdirectories excluded from the main DiffTestRunner ———
  
  /** Diff test subdirectories that belong to the hkmc2NofibTests project. */
  def nofibDiffDirs(workingDir: os.Path): Ls[os.Path] =
    diffTestDir(workingDir)/"nofib" :: Nil
  
  /** Diff test subdirectories that belong to the hkmc2AppsTests project. */
  def appsDiffDirs(workingDir: os.Path): Ls[os.Path] =
    diffTestDir(workingDir)/"apps" :: Nil
  
  /** Diff test directories that are always excluded (staging, mlscript-compile). */
  def alwaysExcludedDiffDirs(workingDir: os.Path): Ls[os.Path] =
    (diffTestDir(workingDir)/"ucs"/"staging") ::
    compileTestDir(workingDir) ::
    Nil
  
  /** All diff test directories excluded from the main DiffTestRunner. */
  def mainExcludedDiffDirs(workingDir: os.Path): Ls[os.Path] =
    alwaysExcludedDiffDirs(workingDir) ++ nofibDiffDirs(workingDir) ++ appsDiffDirs(workingDir)
  
  /** Check whether a file should be excluded from the given list of excluded directories. */
  def isExcluded(file: os.Path, excludedDirs: Ls[os.Path]): Bool =
    excludedDirs.exists(dir => isInDir(file, dir))
  
  // ——— Compile test directories ———
  
  /** Compile test directories for the main hkmc2JVM project.
    * We walk from `mainTestDir` so test names include the `mlscript-compile/` prefix. */
  def mainCompileDirs(workingDir: os.Path): Ls[os.Path] =
    mainTestDir(workingDir) :: Nil
  
  /** Directories whose compile files are excluded from the main CompileTestRunner. */
  def mainExcludedCompileDirs(workingDir: os.Path): Ls[os.Path] =
    compileTestDir(workingDir)/"apps" :: Nil
  
  /** Compile test directories for the hkmc2NofibTests project.
    * We walk from `bench/` so test names include the `mlscript-compile/` prefix. */
  def nofibCompileDirs(workingDir: os.Path): Ls[os.Path] =
    (workingDir/"hkmc2Benchmarks"/"src"/"test"/"bench") :: Nil

  /** Compile test directories for the hkmc2AppsTests project.
    * We walk from `mlscript-compile/apps/` directly. */
  def appsCompileDirs(workingDir: os.Path): Ls[os.Path] =
    compileTestDir(workingDir)/"apps" :: Nil

end TestFolders
