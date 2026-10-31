package hkmc2

import org.scalatest.funsuite.AnyFunSuite

import hkmc2.utils.*, shorthands.*
import hkmc2.Message.MessageContext


// Diff tests check diagnostic text, but cannot check whether the compilation-test
// runner notices a diagnostic that has no source line to include in its summary.
class ReportFormatterTest extends AnyFunSuite:
  private val basePath = io.Path("/tests")

  for diagnostic <- List(
    ErrorReport(msg"Error without a source location" -> N :: Nil),
    WarningReport(msg"Warning without a source location" -> N :: Nil),
    InternalError(msg"Internal error without a source location" -> N :: Nil),
  ) do
    test(s"records ${diagnostic.kind} diagnostics without source locations"):
      val report = ReportFormatter(_ => (), basePath, colorize = false)
      report.mkRaise(basePath / io.RelPath("Test.mls"))(diagnostic)
      assert(report.hasDiagnostics)
      assert(report.badLines.isEmpty)
      report(0, Nil, showRelativeLineNums = false)
      assert(report.hasDiagnostics)

  test("an empty diagnostic batch does not report a failure"):
    val report = ReportFormatter(_ => (), basePath, colorize = false)
    assert(!report.hasDiagnostics)
    report(0, Nil, showRelativeLineNums = false)
    assert(!report.hasDiagnostics)
