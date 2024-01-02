package mlscript.ucs

import collection.mutable.{Map => MutMap}
import mlscript.ucs.stages._
import mlscript.ucs.context.{Context, ScrutineeData}
import mlscript.ucs.display.{showNormalizedTerm, showSplit}
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

  protected def freshSymbol(nme: Var): LocalTermSymbol = new LocalTermSymbol(nme)

  /** Common operations of `Var` which can be shared within all stages. */
  protected implicit class VarOps(nme: Var) {
    /** Associate the given `Var` with a fresh `ValueSymbol`. */
    def withFreshSymbol: Var = nme.withSymbol(freshSymbol(nme))

    /**
      * If the given `Var` represents a class name, get its associated `ClassSymbol`.
      *
      * @param className the class name variable
      */
    def getClassLikeSymbol: TypeSymbol =
      trace(s"getClassLikeSymbol <== ${inspect.shallow(nme)}") {
        nme.symbolOption match {
          case S(symbol: ClassSymbol) => symbol
          case S(symbol: TraitSymbol) => symbol
          case S(symbol: ModuleSymbol) => symbol
          case S(symbol: Symbol) => throw new DesugaringException(
            msg"variable ${nme.name} is not associated with a class symbol" -> N :: Nil)
          case N => throw new DesugaringException(
            msg"variable ${nme.name} is not associated with any symbols" -> N :: Nil)
        }
      }(symbol => s"getClassLikeSymbol ==> ${symbol.name}")

    /**
      * A short hand for `nme.symbol.getScrutinee` but add a diagnostic message
      * to a local diagnostic archive (TODO) if there's any error.
      */
    def getOrCreateScrutinee(implicit context: Context): ScrutineeData = nme.symbolOption match {
      case S(symbol: TermSymbol) => symbol.getOrCreateScrutinee
      case S(otherSymbol) => throw new DesugaringException(
        msg"Expected scrutinee symbol, found ${nme.symbol.name}" -> nme.toLoc :: Nil
      )
      case N => throw new DesugaringException(
        msg"Scrutinee symbol not found" -> nme.toLoc :: Nil
      )
    }

    def withScrutinee(scrutinee: ScrutineeData)(implicit context: Context): Var = nme.symbolOption match {
      case S(symbol: TermSymbol) =>
        symbol.addScrutinee(scrutinee)
        nme
      case S(otherSymbol) => throw new DesugaringException(
        msg"Expected scrutinee symbol, found ${nme.symbol.name}" -> nme.toLoc :: Nil
      )
      case N => throw new DesugaringException(
        msg"Scrutinee symbol not found" -> nme.toLoc :: Nil
      )
    }

    def withResolvedTypeSymbol(implicit scope: Scope): Var = {
      nme.symbol = nme.resolveTypeSymbol
      nme
    }

    def resolveTypeSymbol(implicit scope: Scope): TypeSymbol = scope.getTypeSymbol(nme.name) match {
      case S(symbol: TraitSymbol) =>
        println(s"resolveTypeSymbol ${nme} ==> trait")
        nme.symbol = symbol
        symbol
      case S(symbol: ClassSymbol) =>
        println(s"resolveTypeSymbol ${nme} ==> class")
        nme.symbol = symbol
        symbol
      case S(symbol: ModuleSymbol) =>
        println(s"resolveTypeSymbol ${nme} ==> module")
        nme.symbol = symbol
        symbol
      case S(symbol: MixinSymbol) =>
        throw new DesugaringException(msg"Mixins are not allowed in pattern" -> nme.toLoc :: Nil)
      case S(symbol: TypeAliasSymbol) =>
        throw new DesugaringException(msg"Type alias is not allowed in pattern" -> nme.toLoc :: Nil)
      case N =>
        throw new DesugaringException(msg"Undefined symbol found in patterns." -> nme.toLoc :: Nil)
    }
  }

  protected def traverseIf(`if`: If)(implicit scope: Scope): Unit = {
    implicit val context: Context = new Context(`if`)
    trace("traverseIf") {
      // Stage 0: Transformation
      val transformed = traceWithTopic("transform") {
        println("STEP 0")
        val transformed = transform(`if`)
        println("Transformed UCS term:")
        println(showSplit(transformed))
        transformed
      }
      // Stage 1: Desugaring
      val desugared = traceWithTopic("desugar") {
        println("STEP 1")
        val desugared = desugar(transformed)
        println("Desugared UCS term:")
        println(showSplit(desugared))
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
        println(showNormalizedTerm(normalized))
        normalized
      }
      // Stage 3: Post-processing
      val postProcessed = traceWithTopic("postprocess") {
        println("STEP 3")
        val postProcessed = postProcess(normalized)
        println("Post-processed UCS term:")
        println(showNormalizedTerm(postProcessed))
        postProcessed
      }
      // Stage 4: Coverage checking
      traceWithTopic("coverage") {
        val checked = println("STEP 4")
        val diagnostics = checkCoverage(postProcessed)
        println(s"Coverage checking result: ${diagnostics.size} errors")
        raiseMany(diagnostics)
      }
      // Epilogue
      `if`.desugaredTerm = S(postProcessed)
    }(_ => "traverseIf ==> ()")
  }
  
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
        case Split.Let(_, name, rhs, tail) =>
          println(s"found let binding: \"$name\"")
          println(s"traverse rhs: $rhs")
          traverseTerm(rhs)
          traverseSplit(tail)(scope + name.symbol)
        case Split.Else(default) => traverseTerm(default)
        case Split.Nil => println("the end")
      }
    }()

  private def traversePattern(scrutinee: Var, pattern: core.Pattern)(implicit scope: Scope): List[Var -> Symbol] =
    trace(s"traversePattern <== $pattern") {
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
