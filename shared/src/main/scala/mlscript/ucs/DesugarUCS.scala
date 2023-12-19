package mlscript.ucs

import collection.mutable.{Map => MutMap}
import mlscript.ucs.stages._
import mlscript.pretyper.{PreTyper, Scope, ScrutineeSymbol, Symbol, ValueSymbol}
import mlscript._, utils._, shorthands._
import mlscript.Message, Message.MessageContext

// TODO: Rename to `Desugarer` once the old desugarer is removed.
trait DesugarUCS extends Transformation
                    with Desugaring
                    with Normalization
                    with PostProcessing 
                    with CoverageChecking { self: PreTyper =>
  

  protected def traverseIf(`if`: If)(implicit scope: Scope): Unit =
    trace("traverseIf") {
      // Stage 0: Transformation
      println("STEP 0")
      val transformed = transform(`if`, true)
      println("Transformed UCS term:")
      println(transformed.toString, 2)
      println(ucs.syntax.printTermSplit(transformed))
      // Stage 1: Desugaring
      // This stage will generate new names based on the position of the scrutinee.
      // Therefore, we need to call `traverseSplit` to associate these newly generated
      // names with symbols.
      println("STEP 1")
      val desugared = desugar(transformed)
      println(desugared.toString, 2)
      println("Desugared UCS term:")
      println(ucs.core.printSplit(desugared))
      traverseSplit(desugared)
      // Stage 2: Normalization
      println("STEP 2")
      val normalized = normalize(desugared)
      println(normalized.toString, 2)
      println("Normalized UCS term:")
      printNormalizedTerm(normalized)
      // Stage 3: Post-processing
      println("STEP 3")
      val postProcessed = postProcess(normalized)
      println("Post-processed UCS term:")
      printNormalizedTerm(postProcessed)
      // Stage 4: Coverage checking
      println("STEP 4")
      val diagnostics = checkCoverage(postProcessed)
      println(s"Coverage checking result: ${diagnostics.size} errors")
      raise(diagnostics)
      // Epilogue
      `if`.desugaredTerm = S(normalized)
    }(_ => "traverseIf ==> ()")
  
  private def traverseSplit(split: core.Split)(implicit scope: Scope): Unit =
    trace(s"traverseSplit <== [${scope.showLocalSymbols}]") {
      import core._
      split match {
        case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => 
          println(s"found branch: $scrutinee is $pattern")
          traverseTerm(scrutinee)
          val patternSymbols = traversePattern(scrutinee, pattern)
          traverseSplit(continuation)(scope.withEntries(patternSymbols))
          traverseSplit(tail)
        case Split.Let(_, name, _, tail) =>
          println(s"found let binding: \"$name\"")
          traverseSplit(tail)(scope + new ValueSymbol(name, false))
        case Split.Else(default) => traverseTerm(default)
        case Split.Nil => println("the end")
      }
    }()

  private def traversePattern(scrutinee: Var, pattern: core.Pattern): List[Var -> Symbol] =
    trace(s"traversePattern <== $pattern") {
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
    }(_.iterator.map(_._1.name).mkString("traversePattern ==> [", ", ", "]"))
}
