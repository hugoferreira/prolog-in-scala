scalaVersion := "3.2.2"

name := "hello-world"
organization := "eu.hugosereno"
version := "1.0"

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.2.9" % Test,
  "org.scalacheck" %% "scalacheck" % "1.15.4"
)
