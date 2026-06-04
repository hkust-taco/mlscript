import Wart._
import org.scalajs.linker.interface.OutputPatterns

enablePlugins(ScalaJSPlugin)

val scala3Version = "3.8.3"
val directoryWatcherVersion = "0.18.0"
val scalaTestVersion = "3.2.19"

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

lazy val root = project.in(file("."))
  .aggregate(mlscriptJS, mlscriptJVM, ts2mlsTest, compilerJVM, hkmc2AllTests, coreJS, coreJVM)
  .settings(
    publish := {},
    publishLocal := {},
  )

lazy val hkmc2 = crossProject(JSPlatform, JVMPlatform).in(file("hkmc2"))
  .settings(
    scalaVersion := scala3Version,
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"diff", "*.mls", NothingFilter),
    
    // TODO remove when codebase becomes production-ready
    scalacOptions -= "-Wconf:any:error",
    
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

/** Helper to create test subprojects that compile `.mls` files then run diff tests.
  * Each subproject depends on `hkmc2JVM` and `hkmc2DiffTests` for shared test infrastructure.
  * When a compile runner is provided, `Def.sequential` guarantees it completes before diff tests start. */
def hkmc2TestSubproject(dirName: String, compileRunner: Option[String], diffRunner: String): Project = {
  val testTask = compileRunner match {
    case Some(runner) =>
      Def.sequential(
        (Test / testOnly).toTask(s" hkmc2.$runner"),
        (Test / testOnly).toTask(s" hkmc2.$diffRunner"),
      )
    case None =>
      (Test / testOnly).toTask(s" hkmc2.$diffRunner")
  }

  Project(dirName, file(dirName))
    .dependsOn(hkmc2JVM % "compile->compile;test->test")
    .dependsOn(hkmc2DiffTests % "compile->compile;test->test")
    .settings(
      scalaVersion := scala3Version,
      
      libraryDependencies += "org.scalactic" %%% "scalactic" % scalaTestVersion,
      libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
      
      Test / test := testTask.value,
      
      Test/run/fork := true, // so that CTRL+C actually terminates the watcher
    )
}

lazy val hkmc2NofibTests = hkmc2TestSubproject("hkmc2NofibTests", Some("NofibCompileTestRunner"), "NofibDiffTestRunner")
lazy val hkmc2AppsTests = hkmc2TestSubproject("hkmc2AppsTests", Some("AppsCompileTestRunner"), "AppsDiffTestRunner")
lazy val hkmc2WasmTests = hkmc2TestSubproject("hkmc2WasmTests", Some("WasmCompileTestRunner"), "WasmDiffTestRunner")

lazy val hkmc2MainTests = project.in(file("hkmc2MainTests"))
  .settings(
    Test / test := (
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2JVM / Test / test)
    ).value
  )

lazy val hkmc2MostTests = project.in(file("hkmc2MostTests"))
  .settings(
    Test / test := (
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2NofibTests / Test / test)
        .dependsOn(hkmc2AppsTests / Test / test)
        .dependsOn(hkmc2WasmTests / Test / test)
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

lazy val mlscript = crossProject(JSPlatform, JVMPlatform).in(file("."))
  .settings(
    name := "mlscript",
    scalacOptions ++= Seq(
      "-Ywarn-value-discard",
      "-Ypatmat-exhaust-depth:160",
    ),
    wartremoverWarnings ++= Warts.allBut(
      Recursion, Throw, Nothing, Return, While, IsInstanceOf,
      Var, MutableDataStructures, NonUnitStatements,
      DefaultArguments, ImplicitParameter, ImplicitConversion,
      StringPlusAny, Any, ToString,
      JavaSerializable, Serializable, Product, ToString,
      LeakingSealed, Overloading,
      Option2Iterable, IterableOps, ListAppend, SeqApply,
      TripleQuestionMark, PartialFunctionApply,
    ),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % Test,
    libraryDependencies += "com.lihaoyi" %%% "sourcecode" % "0.3.1",
    libraryDependencies += "com.lihaoyi" %%% "fastparse" % "2.3.3",
    libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.8.0",
    // 
    watchSources += WatchSource(
      sourceDirectory.value.getParentFile().getParentFile()/"shared/src/test/diff", "*.fun", NothingFilter),
    watchSources += WatchSource(
      sourceDirectory.value.getParentFile().getParentFile()/"shared/src/test/diff", "*.mls", NothingFilter),
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oC"),
  )
  .jsSettings(
    scalaJSUseMainModuleInitializer := true,
    libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "2.2.0",
  )
  .dependsOn(core)

lazy val mlscriptJVM = mlscript.jvm
lazy val mlscriptJS = mlscript.js

lazy val ts2mls = crossProject(JSPlatform, JVMPlatform).in(file("ts2mls"))
  .settings(
    name := "ts2mls",
  )
  .jvmSettings()
  .jsSettings(
    libraryDependencies += "org.scalatest" %%% "scalatest" % "3.2.12" % "test"
  )
  .dependsOn(mlscript % "compile->compile;test->test")

lazy val ts2mlsJS = ts2mls.js
lazy val ts2mlsJVM = ts2mls.jvm

lazy val ts2mlsTest = project.in(file("ts2mls"))
  .settings(
    Test / test := ((ts2mlsJVM / Test / test) dependsOn (ts2mlsJS / Test / test)).value
  )

lazy val compiler = crossProject(JSPlatform, JVMPlatform).in(file("compiler"))
  .settings(
    name := "mlscript-compiler",
    scalaVersion := scala3Version,
    sourceDirectory := baseDirectory.value.getParentFile()/"shared",
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"test"/"diff", "*.mls", NothingFilter),
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"test"/"diff-ir", "*.mls", NothingFilter),
  )
  .dependsOn(mlscript % "compile->compile;test->test")

lazy val compilerJVM = compiler.jvm
lazy val compilerJS = compiler.js

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
