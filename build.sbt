import Wart._

enablePlugins(ScalaJSPlugin)

val scala3Version = "3.6.1"
val directoryWatcherVersion = "0.18.0"

ThisBuild / scalaVersion     := "2.13.14"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "hkust-taco.github.io"
ThisBuild / organizationName := "HKUST-TACO"
ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-unchecked",
  "-language:higherKinds",
  if (insideCI.value) "-Wconf:any:error"
  else                "-Wconf:any:warning",
)

lazy val root = project.in(file("."))
  .aggregate(mlscriptJS, mlscriptJVM, ts2mlsTest, compilerJVM, hkmc2JS, hkmc2JVM, coreJS, coreJVM)
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
    
    libraryDependencies += "io.methvin" % "directory-watcher" % directoryWatcherVersion,
    libraryDependencies += "io.methvin" %% "directory-watcher-better-files" % directoryWatcherVersion,
    libraryDependencies += "com.lihaoyi" %%% "fansi" % "0.4.0",
    libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.9.3",
    
    libraryDependencies += "org.scalactic" %%% "scalactic" % "3.2.18",
    libraryDependencies += "org.scalatest" %%% "scalatest" % "3.2.18" % "test",
    
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"mlscript", "*.mls", NothingFilter),
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"src"/"test"/"mlscript", "*.cmd", NothingFilter),
    
    Test/run/fork := true, // so that CTRL+C actually terminates the watcher
  )
  .jvmSettings(
  )
  .dependsOn(core)

lazy val hkmc2JVM = hkmc2.jvm
lazy val hkmc2JS = hkmc2.js

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
      TripleQuestionMark,
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

