import Wart._

enablePlugins(ScalaJSPlugin)

ThisBuild / scalaVersion     := "2.13.8"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "io.lptk"
ThisBuild / organizationName := "LPTK"

lazy val root = project.in(file("."))
  .aggregate(mlscriptJS, mlscriptJVM)
  .settings(
    publish := {},
    publishLocal := {},
  )

lazy val mlscript = crossProject(JSPlatform, JVMPlatform).in(file("."))
  .settings(
    name := "mlscript",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-language:higherKinds",
      "-Ywarn-value-discard",
    ),
    scalacOptions ++= {
      if (insideCI.value) Seq("-Wconf:any:error")
      else                Seq("-Wconf:any:warning")
    },
    wartremoverWarnings ++= Warts.allBut(
      Recursion, Throw, Nothing, Return, While, IsInstanceOf,
      Var, MutableDataStructures, NonUnitStatements,
      DefaultArguments, ImplicitParameter, ImplicitConversion,
      StringPlusAny, Any,
      JavaSerializable, Serializable, Product,
      LeakingSealed, Overloading,
      Option2Iterable, TraversableOps, ListAppend
    ),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % Test,
    libraryDependencies += "com.lihaoyi" %%% "sourcecode" % "0.2.8",
    libraryDependencies += "com.lihaoyi" %%% "fastparse" % "2.3.3",
    libraryDependencies += "com.lihaoyi" %% "fansi" % "0.2.14",
    // libraryDependencies += "com.lihaoyi" %%% "fansi" % "0.2.7", // FIXME does not resolve — why?
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
    libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "2.1.0",
  )

lazy val mlscriptJVM = mlscript.jvm
lazy val mlscriptJS = mlscript.js

lazy val ts2mls = crossProject(JSPlatform, JVMPlatform).in(file("ts2mls"))
  .settings(
    name := "ts2mls",
    scalaVersion := "2.13.8",
    scalacOptions ++= Seq(
      "-deprecation"
    )
  )
  .jvmSettings()
  .jsSettings(
    scalaJSUseMainModuleInitializer := true,
    libraryDependencies += "org.scalatest" %%% "scalatest" % "3.2.12" % "test"
  )
  .dependsOn(mlscript % "compile->compile;test->test")

lazy val ts2mlsJS = ts2mls.js
lazy val ts2mlsJVM = ts2mls.jvm

val tsTypeDiffTests = taskKey[Unit]("")

tsTypeDiffTests := (Def.task{
  (ts2mlsJVM / Test / test).value
} triggeredBy (ts2mlsJS / Test / test)).value