import scala.util.Try
import scala.scalajs.js.annotation.JSExportTopLevel
import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.raw.{Event, TextEvent, UIEvent, HTMLTextAreaElement}
import mlscript.utils._
import mlscript._
import mlscript.utils.shorthands._
import scala.util.matching.Regex
import scala.scalajs.js
import scala.collection.immutable

object Main {
  def main(args: Array[String]): Unit = {
    val source = document.querySelector("#mlscript-input")
    update(source.textContent)
    source.addEventListener("input", typecheck)
  }
  @JSExportTopLevel("typecheck")
  def typecheck(e: dom.UIEvent): Unit = {
    e.target match {
      case elt: dom.HTMLTextAreaElement =>
        update(elt.value)
    }
  }
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  def update(str: String): Unit = {
    // println(s"Input: $str")
    val target = document.querySelector("#mlscript-output")
    val tryRes = Try[Str] {
      import fastparse._
      import fastparse.Parsed.{Success, Failure}
      import mlscript.{MLParser, ErrorReport, Origin}
      val lines = str.splitSane('\n').toIndexedSeq
      val processedBlock = MLParser.addTopLevelSeparators(lines).mkString
      val fph = new mlscript.FastParseHelpers(str, lines)
      val parser = new MLParser(Origin("<input>", 1, fph))
      parse(processedBlock, parser.pgrm(_), verboseFailures = false) match {
        case f: Failure =>
          val Failure(err, index, extra) = f
          val (lineNum, lineStr, _) = fph.getLineColAt(index)
          "Parse error: " + extra.trace().msg +
            s" at line $lineNum:<BLOCKQUOTE>$lineStr</BLOCKQUOTE>"
        case Success(pgrm, index) =>
          println(s"Parsed: $pgrm")
          val (diags, (typeDefs, stmts)) = pgrm.desugared
          // report(diags) // TODO... currently the MLParser does not report any in desugaring so this is fine
          val (typeCheckResult, errorResult) = checkProgramType(pgrm)
          errorResult match {
            case Some(typeCheckResult) => typeCheckResult
            case None => {
              val htmlBuilder = new StringBuilder
              var results = generateRuntimeCode(pgrm) match {
                case R(code) =>
                  executeCode(code) match {
                    case L(errorHtml) =>
                      htmlBuilder ++= errorHtml
                      Nil
                    case R(results) => results
                  }
                case L(errorHtml) =>
                  htmlBuilder ++= errorHtml
                  Nil
              }
              htmlBuilder ++= """<table>
                  |  <thead>
                  |    <tr>
                  |       <td>Name</td>
                  |       <td>Type</td>
                  |       <td>Value</td>
                  |    </tr>
                  |  </thead>
                  |""".stripMargin
              // Assemble something like: `val <name>: <type> = <value>`.
              // If error occurred, leave `<no value>`.
              typeCheckResult.zip(pgrm.desugared._2._2) foreach { case ((name, ty), origin) =>
                val value = origin match {
                  // Do not extract from results if its a type declaration.
                  case Def(_, _, R(_), _) => N
                  // Otherwise, `origin` is either a term or a definition.
                  case _ => results match {
                    case head :: next =>
                      results = next
                      S(head)
                    case Nil => N
                  }
                }
                val valueHtml = value match {
                  case S(text) => s"<td>$text</td>"
                  case N => "<td class=\"no-value\">no value</td>"
                }
                htmlBuilder ++= s"""<tr>
                  |  <td class="name">${name getOrElse "res"}</td>
                  |  <td class="type">$ty</td>
                  |  $valueHtml
                  |</tr>
                  |""".stripMargin
              }
              htmlBuilder ++= "</table>"
              htmlBuilder.toString
            }
          }
      }
    }
    
    target.innerHTML = tryRes.fold[Str](
      err =>
        s"""
      <font color="Red">
      Unexpected error: ${err}${
          err.printStackTrace
          // err.getStackTrace().map(s"$htmlLineBreak$htmlWhiteSpace$htmlWhiteSpace at " + _).mkString
          ""
        }</font>""",
      identity
    )
  }
  
  // Returns `Right[Str]` if successful, `Left[Str]` if not.
  private def generateRuntimeCode(pgrm: Pgrm): Either[Str, Str] = {
    try {
      val backend = new JSWebBackend()
      val lines = backend(pgrm)
      val code = lines.mkString("\n")
      println("Running code: " + code)
      R(code)
    } catch {
      case e: Throwable =>
        val sb = new StringBuilder()
        sb ++= "<font color=\"red\">Code generation crashed:</font>"
        sb ++= htmlLineBreak + e.getMessage
        // sb ++= htmlLineBreak + ((e.getStackTrace) mkString htmlLineBreak)
        sb ++= htmlLineBreak
        sb ++= htmlLineBreak
        L(sb.toString)
    }
  }
  
  // Execute the generated code.
  // We extract this function because there is some boilerplate code.
  // It returns a tuple of three items:
  // 1. results of definitions;
  // 2. results of expressions;
  // 3. error message (if has).
  @SuppressWarnings(Array("org.wartremover.warts.AsInstanceOf"))
  private def executeCode(code: Str): Either[Str, Ls[Str]] = {
    try {
      R(js.eval(code).asInstanceOf[js.Array[Str]].toList)
    } catch {
      case e: Throwable =>
        val errorBuilder = new StringBuilder()
        errorBuilder ++= "<font color=\"red\">Runtime error occurred:</font>"
        errorBuilder ++= htmlLineBreak + e.getMessage
        errorBuilder ++= htmlLineBreak
        errorBuilder ++= htmlLineBreak
        L(errorBuilder.toString)
    }
  }
  
  private val htmlLineBreak = "<br />"
  private val htmlWhiteSpace = "&nbsp;"
  private val splitLeadingSpaces: Regex = "^( +)(.+)$".r
  
  def checkProgramType(pgrm: Pgrm): Ls[Option[Str] -> Str] -> Option[Str] = {
    val (diags, (typeDefs, stmts)) = pgrm.desugared
    
    val typer = new mlscript.Typer(
      dbg = false,
      verbose = false,
      explainErrors = false
    )
    
    import typer._
    
    val res = new collection.mutable.StringBuilder
    val results = new collection.mutable.ArrayBuffer[Option[Str] -> Str]
    val stopAtFirstError = true
    var errorOccurred = false

    def formatError(culprit: Str, err: ErrorReport): Str = {
      s"""<b><font color="Red">
                Error in <font color="LightGreen">${culprit}</font>: ${err.mainMsg}
                <!--${
                  // The rest of the message may not make sense if we don't also print the provs
                  // For example we'd get things like "Declared at\nDeclared at" for dup type params...
                  err.allMsgs.tail
                    .map(_._1.show + "<br/>")
                    .mkString("&nbsp;&nbsp;&nbsp;&nbsp;")}-->
                </font></b><br/>"""
    }
    
    implicit val raise: Raise = throw _
    implicit var ctx: Ctx =
      try processTypeDefs(typeDefs)(Ctx.init, raise)
      catch {
        case err: ErrorReport =>
          res ++= formatError("class definitions", err)
          Ctx.init
      }
    
    val curBlockTypeDefs = typeDefs.flatMap(td => ctx.tyDefs.get(td.nme.name))
    typer.computeVariances(curBlockTypeDefs, ctx)
    
    def getType(ty: typer.TypeScheme): Type = {
      val wty = ty.uninstantiatedBody
      object SimplifyPipeline extends typer.SimplifyPipeline {
        def debugOutput(msg: => Str): Unit = println(msg)
      }
      val sim = SimplifyPipeline(wty)(ctx)
      val exp = typer.expandType(sim)
      exp
    }
    def formatBinding(nme: Str, ty: TypeScheme): Str = {
      val exp = getType(ty)
      s"""<b>
              <font color="#93a1a1">val </font>
              <font color="LightGreen">${nme}</font>: 
              <font color="LightBlue">${exp.show}</font>
              </b><br/>"""
    }
    
    def underline(fragment: Str): Str =
      s"<u style=\"text-decoration: #E74C3C dashed underline\">$fragment</u>"
    
    var totalTypeErrors = 0
    var totalWarnings = 0
    var outputMarker = ""
    val blockLineNum = 0
    val showRelativeLineNums = false
    
    def report(diag: Diagnostic): Str = {
      var sb = new collection.mutable.StringBuilder
      def output(s: Str): Unit = {
        sb ++= outputMarker
        sb ++= s
        sb ++= htmlLineBreak
        ()
      }
      val sctx = Message.mkCtx(diag.allMsgs.iterator.map(_._1), "?")
      val headStr = diag match {
        case ErrorReport(msg, loco, src) =>
          totalTypeErrors += 1
          s"╔══ <strong style=\"color: #E74C3C\">[ERROR]</strong> "
        case WarningReport(msg, loco, src) =>
          totalWarnings += 1
          s"╔══ <strong style=\"color: #F39C12\">[WARNING]</strong> "
      }
      val lastMsgNum = diag.allMsgs.size - 1
      var globalLineNum =
        blockLineNum // solely used for reporting useful test failure messages
      diag.allMsgs.zipWithIndex.foreach { case ((msg, loco), msgNum) =>
        val isLast = msgNum =:= lastMsgNum
        val msgStr = msg.showIn(sctx)
        if (msgNum =:= 0)
          output(headStr + msgStr)
        else
          output(s"${if (isLast && loco.isEmpty) "╙──" else "╟──"} ${msgStr}")
        if (loco.isEmpty && diag.allMsgs.size =:= 1) output("╙──")
        loco.foreach { loc =>
          val (startLineNum, startLineStr, startLineCol) =
            loc.origin.fph.getLineColAt(loc.spanStart)
          if (globalLineNum =:= 0) globalLineNum += startLineNum - 1
          val (endLineNum, endLineStr, endLineCol) =
            loc.origin.fph.getLineColAt(loc.spanEnd)
          var l = startLineNum
          var c = startLineCol // c starts from 1
          while (l <= endLineNum) {
            val globalLineNum = loc.origin.startLineNum + l - 1
            val relativeLineNum = globalLineNum - blockLineNum + 1
            val shownLineNum =
              if (showRelativeLineNums && relativeLineNum > 0)
                s"l.+$relativeLineNum"
              else "l." + globalLineNum
            val prepre = "║  "
            val pre = s"$shownLineNum: " // Looks like l.\d+
            val curLine = loc.origin.fph.lines(l - 1)
            val lastCol =
              if (l =:= endLineNum) endLineCol else curLine.length + 1
            val front = curLine.slice(0, c - 1)
            val middle = underline(curLine.slice(c - 1, lastCol - 1))
            val back = curLine.slice(lastCol - 1, curLine.size)
            output(s"$prepre$pre\t$front$middle$back")
            c = 1
            l += 1
            if (isLast) output("╙──")
          }
        }
      }
      if (diag.allMsgs.isEmpty) output("╙──")
      sb.toString
    }
    
    var declared: Map[Var, typer.PolymorphicType] = Map.empty
    
    def htmlize(str: Str): Str =
      str.replace("\n", "<br/>").replace("  ", "&emsp;")
    
    var decls = stmts
    while (decls.nonEmpty) {
      val d = decls.head
      decls = decls.tail
      try d match {
        case d @ Def(isrec, nme, L(rhs), _) =>
          val ty_sch = typeLetRhs(isrec, nme.name, rhs)(ctx, raise)
          val inst = ty_sch.instantiate(0)
          println(s"Typed `$nme` as: $inst")
          println(s" where: ${inst.showBounds}")
          val exp = getType(ty_sch)
          declared.get(nme) match {
            case S(sign) =>
              subsume(ty_sch, sign)(ctx, raise, TypeProvenance(d.toLoc, "def definition"))
              // Note: keeping the less precise declared type signature here (no ctx update)
            case N =>
              ctx += nme.name -> VarSymbol(ty_sch, nme)
          }
          res ++= formatBinding(d.nme.name, ty_sch)
          results append S(d.nme.name) -> htmlize(getType(ty_sch).show)
        case d @ Def(isrec, nme, R(PolyType(tps, rhs)), _) =>
          declared.get(nme) match {
            case S(sign) =>
              import Message.MessageContext
              typer.err(msg"illegal redeclaration of ${nme.name}" -> d.toLoc
                :: msg"already defined here:" ->
                  declared.keysIterator.find(_.name === nme.name).flatMap(_.toLoc)
                :: Nil)
            case N => ()
          }
          val ty_sch = PolymorphicType(0, typeType(rhs)(ctx.nextLevel, raise,
            vars = tps.map(tp => tp.name -> freshVar(noProv/*FIXME*/)(1)).toMap))
          ctx += nme.name -> VarSymbol(ty_sch, nme)
          declared += nme -> ty_sch
          results append S(d.nme.name) -> htmlize(getType(ty_sch).show)
        case s: DesugaredStatement =>
          typer.typeStatement(s, allowPure = true) match {
            case R(binds) =>
              binds.foreach { case (nme, pty) =>
                ctx += nme -> VarSymbol(pty, Var(nme))
                res ++= formatBinding(nme, pty)
                results append S(nme) -> htmlize(getType(pty).show)
              }
            case L(pty) =>
              val exp = getType(pty)
              if (exp =/= TypeName("unit")) {
                val nme = "res"
                ctx += nme -> VarSymbol(pty, Var(nme))
                res ++= formatBinding(nme, pty)
                results append N -> htmlize(getType(pty).show)
              }
          }
      } catch {
        case err: ErrorReport =>
          if (stopAtFirstError) decls = Nil
          val culprit = d match {
            case Def(isrec, nme, rhs, isByname)  => "def " + nme
            case _: DesugaredStatement => "statement"
          }
          res ++= report(err)
          errorOccurred = true
      }
    }
    
    results.toList -> (if (errorOccurred) S(res.toString) else N)
  }
  
  private def underline(fragment: Str): Str =
    s"<u style=\"text-decoration: #E74C3C dashed underline\">$fragment</u>"
}
