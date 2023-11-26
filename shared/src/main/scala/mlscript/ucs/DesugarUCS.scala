package mlscript.ucs

import collection.mutable.{Map => MutMap}
import mlscript.ucs.stages._
import mlscript.pretyper.{PreTyper, Scope, ScrutineeSymbol, Symbol, ValueSymbol}
import mlscript._, utils._, shorthands._
import mlscript.codegen.Helpers.inspect
import mlscript.Message, Message.MessageContext

// TODO: Rename to `Desugarer` once the old desugarer is removed.
trait DesugarUCS extends Transformation
                    with Desugaring
                    with Normalization
                    with PostProcessing 
                    with CoverageChecking { self: PreTyper =>
  

  protected def visitIf(`if`: If)(implicit scope: Scope): Unit =
    trace("visitIf") {
      // Stage 0: Transformation
      val transformed = transform(`if`, true)
      println("Transformed UCS term:")
      println(transformed.toString, 2)
      println(ucs.syntax.printTermSplit(transformed))
      // Stage 1: Desugaring
      // This stage will generate new names based on the position of the scrutinee.
      // Therefore, we need to call `visitSplit` to associate these newly generated
      // names with symbols.
      val desugared = desugar(transformed)
      println(desugared.toString, 2)
      println("Desugared UCS term:")
      println(ucs.core.printSplit(desugared))
      visitSplit(desugared)
      // Stage 2: Normalization
      val normalized = normalize(desugared)
      println(normalized.toString, 2)
      println("Normalized UCS term:")
      printNormalizedTerm(normalized)
      // Stage 3: Post-processing
      val postProcessed = postProcess(normalized)
      println("Post-processed UCS term:")
      printNormalizedTerm(postProcessed)
      // Stage 4: Coverage checking
      val diagnostics = checkCoverage(postProcessed)
      println(s"Coverage checking result: ${diagnostics.size} errors")
      raise(diagnostics)
      // Epilogue
      `if`.desugaredTerm = S(normalized)
    }(_ => "visitIf ==> ()")
  
  private def visitSplit(split: core.Split)(implicit scope: Scope): Unit =
    trace(s"visitSplit <== [${scope.showLocalSymbols}]") {
      import core._
      split match {
        case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => 
          println(s"found branch: $scrutinee is $pattern")
          visitTerm(scrutinee)
          val patternSymbols = visitPattern(scrutinee, pattern)
          visitSplit(continuation)(scope.withEntries(patternSymbols))
          visitSplit(tail)
        case Split.Let(_, name, _, tail) =>
          println(s"found let binding: \"$name\"")
          visitSplit(tail)(scope + new ValueSymbol(name, false))
        case Split.Else(default) => visitTerm(default)
        case Split.Nil => println("the end")
      }
    }()

  private def visitPattern(scrutinee: Var, pattern: core.Pattern): List[Var -> Symbol] =
    trace(s"visitPattern <== $pattern") {
      lazy val scrutineeSymbol = scrutinee.symbol match {
        case symbol: ScrutineeSymbol => symbol
        case other: Symbol =>
          throw new DesugaringException(msg"Scrutinee is not a scrutinee symbol" -> scrutinee.toLoc :: Nil)
      }
      pattern match {
        case core.Pattern.Literal(literal) => Nil
        case core.Pattern.Name(nme) =>
          nme.symbol = scrutineeSymbol
          nme -> scrutineeSymbol :: Nil
        case core.Pattern.Class(nme, N) =>
          scrutineeSymbol.matchedClasses += nme
          Nil
        case core.Pattern.Class(nme, S(parameters)) =>
          scrutineeSymbol.matchedClasses += nme
          parameters.iterator.zipWithIndex.flatMap { 
            case (N, _) => N
            case (S(parameter), index) =>
              val symbol = scrutineeSymbol.addSubScrutinee(nme, index, parameter)
              parameter.symbol = symbol; S(parameter -> symbol)
          }.toList
        case core.Pattern.Tuple(elements) => elements.flatMap {
          case N => Nil
          case S(pattern) => elements.iterator.zipWithIndex.flatMap {
            case (N, _) => N
            case (S(element), index) =>
              val symbol = scrutineeSymbol.addSubScrutinee(index)
              element.symbol = symbol; S(element -> symbol)
          }.toList
        }
        case core.Pattern.Record(entries) =>
          entries.iterator.zipWithIndex.map { case ((fieldName, bindingName), _) =>
            val symbol = scrutineeSymbol.addSubScrutinee(fieldName)
            bindingName.symbol = symbol; bindingName -> symbol
          }.toList
      }
    }(_.iterator.map(_._1.name).mkString("visitPattern ==> [", ", ", "]"))
}
