// import Wart._

import org.scalajs.linker.interface.OutputPatterns

enablePlugins(ScalaJSPlugin)

val scala3Version = "3.8.4"
val directoryWatcherVersion = "0.18.0"
val scalaTestVersion = "3.2.20"

ThisBuild / scalaVersion     := "2.13.18"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "hkust-taco.github.io"
ThisBuild / organizationName := "HKUST-TACO"
ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-unchecked",
  "-language:higherKinds",
  "-language:implicitConversions",
  if (insideCI.value) "-Wconf:any:error"
  else                "-Wconf:any:warning",
)

// CI runners have few physical cores. Compile tests have a wall-clock time limit
// (see TimeOutTests), which measures contention as much as compilation time when
// other test tasks run at the same time: the dependencies of `hkmc2AllTests/test`
// are unordered relative to each other, so sbt would run the JS tests, the
// subproject runners, and the JVM suites together. Run one test task at a time
// on CI; ScalaTest still runs the tests of a `ParallelTestExecution` suite in parallel.
Global / concurrentRestrictions ++= {
  if (insideCI.value) Seq(Tags.limit(Tags.Test, 1))
  else Nil
}

// ThisBuild / wartremoverWarnings ++= Warts.unsafe

lazy val root = project.in(file("."))
  .aggregate(hkmc2JS, hkmc2JVM, hkmc2AllTests, coreJS, coreJVM)
  .settings(
    publish := {},
    publishLocal := {},
  )

lazy val hkmc2 = crossProject(JSPlatform, JVMPlatform).in(file("hkmc2"))
  .settings(
    scalaVersion := scala3Version,
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"diff", "*.mls", NothingFilter),
    
    // scalacOptions ++= Seq("-indent", "-rewrite"),
    scalacOptions ++= Seq("-new-syntax", "-rewrite"),
    // scalacOptions ++= Seq("-language:experimental.modularity"), // https://docs.scala-lang.org/scala3/reference/experimental/modularity.html
    
    libraryDependencies += "io.methvin" % "directory-watcher" % directoryWatcherVersion,
    libraryDependencies += "io.methvin" %% "directory-watcher-better-files" % directoryWatcherVersion,
    libraryDependencies += "com.lihaoyi" %%% "fansi" % "0.5.0", // Scala.js or Scala-Native
    libraryDependencies += "com.lihaoyi" %%% "sourcecode" % "0.4.2", // Scala.js / Scala Native
    libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.9.3",
    
    libraryDependencies += "org.scalactic" %%% "scalactic" % scalaTestVersion,
    libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
    
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"mlscript", "*.mls", NothingFilter),
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"mlscript-compile", "*.mls", NothingFilter),
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"mlscript", "*.cmd", NothingFilter),
  )
  .jvmSettings(
  )
  .jsSettings(
    scalaJSLinkerConfig ~= {
      _.withModuleKind(ModuleKind.ESModule)
        .withOutputPatterns(OutputPatterns.fromJSFile("MLscript.mjs"))
    },
    libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "2.2.0",
  )
  .dependsOn(core)

lazy val hkmc2JVM = hkmc2.jvm
lazy val hkmc2JS = hkmc2.js

lazy val hkmc2DiffTests = project.in(file("hkmc2DiffTests"))
  .dependsOn(hkmc2JVM % "compile->compile;test->test")
  .settings(
    scalaVersion := scala3Version,
    
    libraryDependencies += "org.scalactic" %%% "scalactic" % scalaTestVersion,
    libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
    
    Test/run/fork := true, // so that CTRL+C actually terminates the watcher
  )

val compileTestFixtures = taskKey[Unit]("Compile the MLscript fixtures needed by diff tests")

/** Helper to create test subprojects that compile `.mls` files then run diff tests.
  * Each subproject depends on `hkmc2JVM` and `hkmc2DiffTests` for shared test infrastructure.
  * A named prerequisite lets suites share fixture compilation in aggregate runs.
  * Diff tests wait for it before loading the generated modules. */
def hkmc2TestSubproject(dirName: String, compileRunner: Option[String], diffRunner: String): Project = {
  val compileTask = compileRunner match {
    case Some(runner) =>
      (Test / testOnly).toTask(s" hkmc2.$runner")
    case None =>
      Def.task { () }
  }

  Project(dirName, file(dirName))
    .dependsOn(hkmc2JVM % "compile->compile;test->test")
    .dependsOn(hkmc2DiffTests % "compile->compile;test->test")
    .settings(
      scalaVersion := scala3Version,
      
      libraryDependencies += "org.scalactic" %%% "scalactic" % scalaTestVersion,
      libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
      
      Test / compileTestFixtures := compileTask.value,
      Test / test := (Test / testOnly).toTask(s" hkmc2.$diffRunner")
        .dependsOn(Test / compileTestFixtures).value,
      
      Test/run/fork := true, // so that CTRL+C actually terminates the watcher
    )
}

lazy val hkmc2NofibTests = hkmc2TestSubproject("hkmc2NofibTests", Some("NofibCompileTestRunner"), "NofibDiffTestRunner")
lazy val hkmc2AppsTests = hkmc2TestSubproject("hkmc2AppsTests", Some("AppsCompileTestRunner"), "AppsDiffTestRunner")
lazy val hkmc2WasmTests = hkmc2TestSubproject("hkmc2WasmTests", Some("WasmCompileTestRunner"), "WasmDiffTestRunner")
lazy val hkmc2SlopTests = hkmc2TestSubproject("hkmc2SlopTests", None, "SlopDiffTestRunner")
  .settings(
    // These worksheets load main-suite fixtures such as Iter.mjs and the Wasm.mjs
    // runtime helper. Both must be generated before the slop tests start, even
    // when an aggregate schedules the Wasm and slop suites as sibling tasks.
    Test / test := (Test / test).dependsOn(
      hkmc2JVM / Test / test,
      hkmc2WasmTests / Test / compileTestFixtures,
    ).value,
  )

lazy val hkmc2MainTests = project.in(file("hkmc2MainTests"))
  .settings(
    Test / test := (
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2JVM / Test / test)
        .dependsOn(hkmc2SlopTests / Test / test)
    ).value
  )

lazy val hkmc2MostTests = project.in(file("hkmc2MostTests"))
  .settings(
    Test / test := (
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2NofibTests / Test / test)
        .dependsOn(hkmc2AppsTests / Test / test)
        .dependsOn(hkmc2WasmTests / Test / test)
        .dependsOn(hkmc2SlopTests / Test / test)
        .dependsOn(hkmc2JVM / Test / test)
    ).value
  )

lazy val hkmc2AllTests = project.in(file("hkmc2AllTests"))
  .settings(
    Test / test := (
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2NofibTests / Test / test)
        .dependsOn(hkmc2AppsTests / Test / test)
        .dependsOn(hkmc2WasmTests / Test / test)
        .dependsOn(hkmc2SlopTests / Test / test)
        .dependsOn(hkmc2JVM / Test / test)
        .dependsOn(hkmc2JS / Test / test)
        .dependsOn(hkmc2Benchmarks / Test / compile)
    ).value
  )


// Watcher
addCommandAlias("watch", "~hkmc2DiffTests/Test/run")
// Diff-tests
addCommandAlias("dtest", "hkmc2DiffTests/testOnly hkmc2.DiffTestRunner -- -z")
addCommandAlias("ndtest", "hkmc2NofibTests/testOnly hkmc2.NofibDiffTestRunner -- -z")
addCommandAlias("adtest", "hkmc2AppsTests/testOnly hkmc2.AppsDiffTestRunner -- -z")
addCommandAlias("wdtest", "hkmc2WasmTests/testOnly hkmc2.WasmDiffTestRunner -- -z")
addCommandAlias("sdtest", "hkmc2SlopTests/testOnly hkmc2.SlopDiffTestRunner -- -z")
// Compilation tests
addCommandAlias("ctest", "hkmc2JVM/testOnly hkmc2.CompileTestRunner -- -z")
addCommandAlias("cntest", "hkmc2NofibTests/testOnly hkmc2.NofibCompileTestRunner -- -z")
addCommandAlias("catest", "hkmc2AppsTests/testOnly hkmc2.AppsCompileTestRunner -- -z")
addCommandAlias("cwtest", "hkmc2WasmTests/testOnly hkmc2.WasmCompileTestRunner -- -z")
// Aggregate tests (for validation)
addCommandAlias("qtest", "hkmc2MainTests/test") // a quick check running only the main compilation and diff- tests
addCommandAlias("mtest", "hkmc2MostTests/test") //  ignores JS compilation + diff- tests; usually sufficient
addCommandAlias("atest", "hkmc2AllTests/test")  // includes JS compilation + diff- tests; checked by CI


lazy val core = crossProject(JSPlatform, JVMPlatform).in(file("core"))
  .settings(
    sourceDirectory := baseDirectory.value.getParentFile()/"shared",
  )

lazy val coreJVM = core.jvm
lazy val coreJS = core.js


lazy val hkmc2Benchmarks = project.in(file("hkmc2Benchmarks"))
  .settings(
    name := "benchmark",
    scalaVersion := scala3Version,
    sourceDirectory := baseDirectory.value/"src",
    libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
    watchSources += WatchSource(
      baseDirectory.value/"src"/"test"/"bench", "*.mls", NothingFilter),

    Test/run/fork := true, // so that CTRL+C actually terminates the watcher
  )
  .dependsOn(hkmc2JVM)
  .dependsOn(hkmc2DiffTests % "compile->compile;test->test")

