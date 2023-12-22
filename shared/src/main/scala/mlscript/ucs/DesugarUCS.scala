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
          traverseSplit(tail)(scope + new ValueSymbol(name, false))
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
        case core.Pattern.Name(nme) =>
          nme.symbol = scrutineeSymbol
          nme -> scrutineeSymbol :: Nil
        // case core.Pattern.Class(nme @ Var("true"), N) =>
        //   println(s"found true pattern")
        //   nme -> scrutineeSymbol :: Nil
        case core.Pattern.Class(nme, maybeParameters) =>
          println(s"`$nme` has location: ${nme.toLoc.isDefined}")
          // Resolve `nme`. It can either be a class, a trait, or a module.
          val symbol = scope.getTypeSymbol(nme.name) match {
            case S(symbol: TraitSymbol) => println(s"${nme.name} is a trait"); symbol
            case S(symbol: ClassSymbol) => println(s"${nme.name} is a class"); symbol
            case S(symbol: ModuleSymbol) => println(s"${nme.name} is a module"); symbol
            case S(symbol: MixinSymbol) =>
              throw new DesugaringException(msg"Mixins are not allowed in pattern" -> nme.toLoc :: Nil)
            case S(symbol: TypeAliasSymbol) =>
              throw new DesugaringException(msg"Type alias is not allowed in pattern" -> nme.toLoc :: Nil)
            // case S(symbol: TermSymbol) =>
            //   throw new DesugaringException(msg"Only classes, modules, and traits can be matched against." -> nme.toLoc :: Nil)
            case N =>
              throw new DesugaringException(msg"Undefined symbol found in patterns." -> nme.toLoc :: Nil)
          }
          nme.symbol = symbol
          // Add the class to the list of matched classes.
          scrutineeSymbol.addMatchedClass(symbol, nme.toLoc)
          maybeParameters match {
            case N => Nil
            case S(parameters) =>
              parameters.iterator.zipWithIndex.flatMap { 
                case (N, _) => N
                case (S(parameter), index) =>
                  val symbol = scrutineeSymbol.addSubScrutinee(nme, index, parameter, parameter.toLoc)
                  parameter.symbol = symbol; S(parameter -> symbol)
              }.toList
          }
        case core.Pattern.Tuple(elements) => elements.flatMap {
          case N => Nil
          case S(pattern) => elements.iterator.zipWithIndex.flatMap {
            case (N, _) => N
            case (S(element), index) =>
              val symbol = scrutineeSymbol.addSubScrutinee(index, element.toLoc)
              element.symbol = symbol; S(element -> symbol)
          }.toList
        }
        case core.Pattern.Record(entries) =>
          entries.iterator.zipWithIndex.map { case ((fieldName, bindingName), _) =>
            val symbol = scrutineeSymbol.addSubScrutinee(fieldName, bindingName.toLoc)
            bindingName.symbol = symbol; bindingName -> symbol
          }.toList
      }
    }(_.iterator.map(_._1.name).mkString("traversePattern ==> [", ", ", "]"))
}
