package mlscript.ucs

import collection.mutable.{Map => MutMap}
import mlscript.ucs.stages._
import mlscript.pretyper.{PreTyper, Scope}
import mlscript.pretyper.symbol._
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
      val transformed = traceWithTopic("transform") {
        println("STEP 0")
        val transformed = transform(`if`, true)
        println("Transformed UCS term:")
        println(ucs.syntax.printTermSplit(transformed))
        transformed
      }
      // Stage 1: Desugaring
      val desugared = traceWithTopic("desugar") {
        println("STEP 1")
        val desugared = desugar(transformed)
        println("Desugared UCS term:")
        println(ucs.core.printSplit(desugared))
        desugared
      }
      traceWithTopic("traverse") {
        println("STEP 1.5")
        traverseSplit(desugared)
      }
      // Stage 2: Normalization
      val normalized = traceWithTopic("normalize") {
        println("STEP 2")
        val normalized = normalize(desugared)
        println("Normalized UCS term:")
        printNormalizedTerm(normalized)
        normalized
      }
      // Stage 3: Post-processing
      val postProcessed = traceWithTopic("postprocess") {
        println("STEP 3")
        val postProcessed = postProcess(normalized)
        println("Post-processed UCS term:")
        printNormalizedTerm(postProcessed)
        postProcessed
      }
      // Stage 4: Coverage checking
      traceWithTopic("coverage") {
        val checked = println("STEP 4")
        val diagnostics = checkCoverage(postProcessed)
        println(s"Coverage checking result: ${diagnostics.size} errors")
        raise(diagnostics)
      }
      // Epilogue
      `if`.desugaredTerm = S(postProcessed)
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
          traverseSplit(tail)(scope + name.symbol)
        case Split.Else(default) => traverseTerm(default)
        case Split.Nil => println("the end")
      }
    }()

  private def traversePattern(scrutinee: Var, pattern: core.Pattern)(implicit scope: Scope): List[Var -> Symbol] =
    trace(s"traversePattern <== $pattern") {
      lazy val scrutineeSymbol = scrutinee.symbol match {
        case symbol: ScrutineeSymbol => symbol
        case other: Symbol =>
          throw new DesugaringException(msg"Scrutinee is not a scrutinee symbol" -> scrutinee.toLoc :: Nil)
      }
      pattern match {
        case core.Pattern.Literal(literal) => Nil
        case core.Pattern.Name(nme) => nme -> nme.symbol :: Nil
        // For now, there should only be parameter-less class patterns.
        case core.Pattern.Class(nme) => Nil
        case core.Pattern.Tuple(_) => ???
        case core.Pattern.Record(_) => ???
      }
    }(_.iterator.map(_._1.name).mkString("traversePattern ==> [", ", ", "]"))
}
