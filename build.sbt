import Wart._

enablePlugins(ScalaJSPlugin)

ThisBuild / scalaVersion     := "2.13.14"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "io.lptk"
ThisBuild / organizationName := "LPTK"
ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-unchecked",
  "-language:higherKinds",
  if (insideCI.value) "-Wconf:any:error"
  else                "-Wconf:any:warning",
)

lazy val root = project.in(file("."))
  .aggregate(mlscriptJS, mlscriptJVM, ts2mlsTest, compilerJVM)
  .settings(
    publish := {},
    publishLocal := {},
  )

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
    libraryDependencies += "com.lihaoyi" %%% "sourcecode" % "0.3.0",
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
    scalaVersion := "3.3.3",
    sourceDirectory := baseDirectory.value.getParentFile()/"shared",
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"test"/"diff", "*.mls", NothingFilter),
    watchSources += WatchSource(
      baseDirectory.value.getParentFile()/"shared"/"test"/"diff-ir", "*.mls", NothingFilter),
  )
  .dependsOn(mlscript % "compile->compile;test->test")

lazy val compilerJVM = compiler.jvm
lazy val compilerJS = compiler.js

