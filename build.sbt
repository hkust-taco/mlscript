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
    Compile / sourceGenerators += Def.task {
      val rootDir = (ThisBuild / baseDirectory).value
      val stdDir = rootDir / "hkmc2" / "shared" / "src" / "test" / "mlscript-compile"
      val declsDir = rootDir / "hkmc2" / "shared" / "src" / "test" / "mlscript" / "decls"
      val out = (Compile / sourceManaged).value / "hkmc2" / "WebIDEStd.scala"
      val preludeFile = declsDir / "Prelude.mls"
      val stdFiles = ((stdDir * "*.mls") +++ (stdDir * "*.mjs") +++ (stdDir / "quotes" * "*.mls") +++ (stdDir / "quotes" * "*.mjs")).get
        .filterNot(_.getName == "Prelude.mls")
        .sortBy(file => stdDir.toPath.relativize(file.toPath).toString)

      def scalaString(value: String): String =
        "\"" + value.flatMap {
          case '\\' => "\\\\"
          case '"' => "\\\""
          case '\n' => "\\n"
          case '\r' => "\\r"
          case '\t' => "\\t"
          case c if c.isControl => f"\\u${c.toInt}%04x"
          case c => c.toString
        } + "\""

      val entries = stdFiles.map { file =>
        val relativePath = stdDir.toPath.relativize(file.toPath).toString.replace(java.io.File.separatorChar, '/')
        s"""js.Array(${scalaString("/std/" + relativePath)}, ${scalaString(IO.read(file))})"""
      }
      val source =
        s"""|package hkmc2
            |
            |import scala.scalajs.js
            |import scala.scalajs.js.annotation.JSExportTopLevel
            |
            |object WebIDEStd:
            |  @JSExportTopLevel("std")
            |  val std: js.Dynamic = js.Dynamic.literal(
            |    prelude = ${scalaString(IO.read(preludeFile))},
            |    files = js.Array(
            |      ${entries.mkString(",\n      ")}
            |    )
            |  )
            |""".stripMargin
      IO.write(out, source)
      Seq(out)
    }.taskValue,
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

lazy val hkmc2PackagesTest = project.in(file("hkmc2PackagesTest"))
  .dependsOn(hkmc2JVM % "compile->compile;test->test")
  .settings(
    scalaVersion := scala3Version,

    libraryDependencies += "org.scalactic" %%% "scalactic" % scalaTestVersion,
    libraryDependencies += "org.scalatest" %%% "scalatest" % scalaTestVersion % "test",
    libraryDependencies += "com.lihaoyi" %% "ujson" % "4.4.3",

    Test / test := (Test / testOnly).toTask(" hkmc2.PackageTestRunner").value,

    Test/run/fork := true, // so that CTRL+C actually terminates the watcher
  )

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
        .dependsOn(hkmc2PackagesTest / Test / test)
        .dependsOn(hkmc2WasmTests / Test / test)
        .dependsOn(hkmc2JVM / Test / test)
    ).value
  )

lazy val hkmc2AllTests = project.in(file("hkmc2AllTests"))
  .settings(
    Test / test := Def.sequential(
      hkmc2JVM / Test / test, // prepares compile-test `.mjs` outputs used by JS tests
      (hkmc2DiffTests / Test / test)
        .dependsOn(hkmc2NofibTests / Test / test)
        .dependsOn(hkmc2AppsTests / Test / test)
        .dependsOn(hkmc2PackagesTest / Test / test)
        .dependsOn(hkmc2WasmTests / Test / test)
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

