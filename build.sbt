import Wart._

enablePlugins(ScalaJSPlugin)

ThisBuild / scalaVersion     := "2.13.6"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "io.lptk"
ThisBuild / organizationName := "LPTK"

lazy val root = project.in(file("."))
  .aggregate(funtypesJS, funtypesJVM)
  .settings(
    publish := {},
    publishLocal := {},
  )

lazy val funtypes = crossProject(JSPlatform, JVMPlatform).in(file("."))
  .settings(
    name := "funtypes",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-language:higherKinds",
      "-Ywarn-value-discard",
    ),
    wartremoverWarnings ++= Warts.allBut(
      Recursion, Throw, Nothing, Return, While, IsInstanceOf,
      Var, MutableDataStructures, NonUnitStatements,
      DefaultArguments, ImplicitParameter, ImplicitConversion,
      StringPlusAny, Any,
      JavaSerializable, Serializable, Product,
      LeakingSealed, Overloading,
      Option2Iterable, TraversableOps, ListAppend
    ),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "com.lihaoyi" %%% "sourcecode" % "0.2.3",
    libraryDependencies += "com.lihaoyi" %%% "fastparse" % "2.3.2",
    libraryDependencies += "com.lihaoyi" %% "fansi" % "0.2.14",
    // libraryDependencies += "com.lihaoyi" %%% "fansi" % "0.2.7", // FIXME does not resolve — why?
    libraryDependencies += "com.lihaoyi" %% "ammonite-ops" % "2.4.0",
    // 
    watchSources += WatchSource(
      sourceDirectory.value.getParentFile().getParentFile()/"shared/src/test/diff", "*.fun", NothingFilter)
  )
  .jsSettings(
    scalaJSUseMainModuleInitializer := true,
    libraryDependencies += "org.scala-js" %%% "scalajs-dom" % "1.1.0",
    libraryDependencies += "be.doeraene" %%% "scalajs-jquery" % "1.0.0",
  )

lazy val funtypesJVM = funtypes.jvm
lazy val funtypesJS = funtypes.js
