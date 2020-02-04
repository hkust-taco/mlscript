import Dependencies._
import Wart._

ThisBuild / scalaVersion     := "2.13.1"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "io.lptk"
ThisBuild / organizationName := "LPTK"

lazy val root = (project in file("."))
  .settings(
    name := "simple-algebraic-subtyping",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-language:higherKinds",
      "-Ywarn-value-discard",
    ),
    wartremoverWarnings ++= Warts.allBut(
      Recursion, Throw, Nothing,
      Var, MutableDataStructures, NonUnitStatements,
      DefaultArguments, ImplicitParameter, StringPlusAny,
      JavaSerializable, Serializable, Product,
      LeakingSealed,
    ),
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2",
  )
