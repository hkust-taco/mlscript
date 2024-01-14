package mlscript.ucs

import collection.mutable.{Map => MutMap}
import syntax.{source => s, core => c}, stages._, context.{Context, ScrutineeData}
import mlscript.ucs.display.{showNormalizedTerm, showSplit}
import mlscript.pretyper.{PreTyper, Scope}
import mlscript.pretyper.symbol._
import mlscript.{If, Loc, Message, Var}, Message.MessageContext, mlscript.Diagnostic.PreTyping
import mlscript.utils._, shorthands._
import syntax.core.{Branch, Split}

// TODO: Rename to `Desugarer` once the old desugarer is removed.
trait DesugarUCS extends Transformation
                    with Desugaring
                    with Normalization
                    with PostProcessing 
                    with CoverageChecking { self: PreTyper =>

  /** A shorthand function to raise errors without specifying the source. */
  protected def raiseError(messages: (Message -> Opt[Loc])*): Unit =
    raiseError(PreTyping, messages: _*)

  /** A shorthand function to raise warnings without specifying the source. */
  protected def raiseWarning(messages: (Message -> Opt[Loc])*): Unit =
    raiseWarning(PreTyping, messages: _*)

  /** Create a fresh local symbol for the given `Var`. */
  protected def freshSymbol(nme: Var): LocalTermSymbol = new LocalTermSymbol(nme)

  /** Common operations of `Var` which can be shared within all stages. */
  protected implicit class VarOps(nme: Var) {
    /** Associate the given `Var` with a fresh `ValueSymbol`. */
    def withFreshSymbol: Var = nme.withSymbol(freshSymbol(nme))

    /**
      * Expect the given `symbol` to be a class-like symbol. If it is not, we
      * get or create a dummy class symbol for it. The desugaring can continue
      * and `Typer` will throw an error for this miuse.
      */
    private def requireClassLikeSymbol(symbol: TypeSymbol)(implicit context: Context): TypeSymbol = symbol match {
      case symbol @ (_: TraitSymbol | _: ClassSymbol | _: ModuleSymbol | _: DummyClassSymbol) => symbol
      case symbol: MixinSymbol =>
        raiseError(msg"Mixins are not allowed in pattern" -> nme.toLoc)
        context.getOrCreateDummyClassSymbol(nme)
      case symbol: TypeAliasSymbol =>
        raiseError(msg"Type alias is not allowed in pattern" -> nme.toLoc)
        context.getOrCreateDummyClassSymbol(nme)
    }

    /**
      * If the given `Var` represents a class name, get its associated `ClassSymbol`.
      *
      * @param className the class name variable
      */
    def getClassLikeSymbol(implicit context: Context): TypeSymbol = {
      val symbol = nme.symbolOption match {
        case S(symbol: TypeSymbol) => requireClassLikeSymbol(symbol)
        case S(symbol: TermSymbol) =>
          raiseError(msg"variable ${nme.name} is not associated with a class symbol" -> nme.toLoc)
          context.getOrCreateDummyClassSymbol(nme)
        case N =>
          raiseError(msg"variable ${nme.name} is not associated with any symbols" -> nme.toLoc)
          context.getOrCreateDummyClassSymbol(nme)
      }
      println(s"getClassLikeSymbol: ${nme.name} ==> ${symbol.showDbg}")
      symbol
    }

    /**
      * A short hand for `nme.symbol.getScrutinee` but add a diagnostic message
      * to a local diagnostic archive (TODO) if there's any error.
      */
    def getOrCreateScrutinee(implicit context: Context): ScrutineeData = nme.symbolOption match {
      case S(symbol: TermSymbol) => symbol.getOrCreateScrutinee
      case S(otherSymbol) => throw new DesugaringException(
        msg"Expected scrutinee symbol, found ${nme.symbol.name}" -> nme.toLoc :: Nil
      )
      case N => throw new DesugaringException(msg"Scrutinee symbol not found" -> nme.toLoc :: Nil)
    }

    /** Associate the `Var` with a scrutinee and returns the same `Var`. */
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

    /**
      * If the `Var` is associated with a term symbol, returns it. Otherwise,
      * resolve the term symbol and associate the `Var` with the term symbol.
      */
    def getOrResolveTermSymbol(implicit scope: Scope): TermSymbol = {
      nme.symbolOption match {
        case N => resolveTermSymbol
        case S(symbol: TermSymbol) => symbol
        case S(otherSymbol) =>
          raiseError(msg"identifier `${nme.name}` should be a term" -> nme.toLoc)
          freshSymbol(nme) // TODO: Maybe we should maintain a "lost" symbol map.
      }
    }

    /** Associate the `Var` with a term symbol and returns the term symbol. */
    def resolveTermSymbol(implicit scope: Scope): TermSymbol = {
      val symbol = scope.getTermSymbol(nme.name).getOrElse {
        raiseError(msg"identifier `${nme.name}` not found" -> nme.toLoc)
        freshSymbol(nme) // TODO: Maybe we should maintain a "lost" symbol map.
      }
      nme.symbol = symbol
      symbol
    }

    /** Associate the `Var` with a term symbol and returns the same `Var`. */
    def withResolvedTermSymbol(implicit scope: Scope): Var = { nme.resolveTermSymbol; nme }

    /** Associate the `Var` with a class like symbol and returns the class like symbol. */
    def resolveClassLikeSymbol(implicit scope: Scope, context: Context): TypeSymbol = {
      val symbol = scope.getTypeSymbol(nme.name) match {
        case S(symbol) => requireClassLikeSymbol(symbol)
        case N =>
          raiseError(msg"type identifier `${nme.name}` not found" -> nme.toLoc)
          context.getOrCreateDummyClassSymbol(nme)
      }
      nme.symbol = symbol
      symbol
    }

    /**
      * Associate the `Var` with a class like symbol and returns the same `Var`.
      * We might be able to remove this function. Currently, it is only used for
      * resolving `Var("true")` and `Var("false")` in `Desugaring`. */
    def withResolvedClassLikeSymbol(implicit scope: Scope, context: Context): Var =
      { nme.resolveClassLikeSymbol; nme }
  }

  protected implicit class SourceSplitOps[+B <: s.Branch](these: s.Split[B]) {
    def ++[BB >: B <: s.Branch](those: s.Split[BB]): s.Split[BB] =
      if (those === s.Split.Nil) these else (these match {
        case s.Split.Cons(head, tail) => s.Split.Cons(head, tail ++ those)
        case s.Split.Let(rec, nme, rhs, tail) => s.Split.Let(rec, nme, rhs, tail ++ those)
        case s.Split.Else(_) =>
          raiseWarning(
            msg"unreachable case" -> those.toLoc,
            msg"because this branch covers the case" -> these.toLoc
          )
          these
        case s.Split.Nil => those
      })
  }

  protected implicit class CoreSplitOps(these: c.Split) {
    /**
      * Concatenates two splits. Beware that `that` may be discarded if `this`
      * has an else branch. Make sure to make diagnostics for discarded `that`.
      */
    def ++(those: c.Split): c.Split =
      if (those === c.Split.Nil) these else (these match {
        case me: c.Split.Cons => me.copy(tail = me.tail ++ those)
        case me: c.Split.Let => me.copy(tail = me.tail ++ those)
        case _: c.Split.Else =>
          raiseWarning(
            msg"the case is unreachable" -> those.toLoc,
            msg"because this branch covers the case" -> these.toLoc
          )
          these
        case c.Split.Nil => those
      })
  }

  protected def traverseIf(`if`: If)(implicit scope: Scope): Unit = {
    implicit val context: Context = new Context(`if`)
    try trace("traverseIf") {
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
        desugar(transformed)
      }
      traceWithTopic("desugar.result") {
        println("Desugared UCS term:")
        println(showSplit(desugared))
      }
      traceWithTopic("traverse") {
        println("STEP 1.5")
        traverseSplit(desugared)
      }
      // Stage 2: Normalization
      val normalized = traceWithTopic("normalize") {
        println("STEP 2")
        normalize(desugared)
      }
      traceWithTopic("normalize.result") {
        println("Normalized UCS term:")
        println(showNormalizedTerm(normalized))
      }
      // Stage 3: Post-processing
      val postProcessed = traceWithTopic("postprocess") {
        println("STEP 3")
        postProcess(normalized)
      }
      traceWithTopic("postprocess.result") {
        println("Post-processed UCS term:")
        println(showNormalizedTerm(postProcessed))
      }
      // Stage 4: Coverage checking
      traceWithTopic("coverage") {
        val checked = println("STEP 4")
        val diagnostics = checkCoverage(postProcessed)
        println(s"Coverage checking result: ${diagnostics.size} errors")
        raiseMany(diagnostics)
      }
      traceWithTopic("desugared") {
        println(s"Desugared term: ${postProcessed.showDbg}")
      }
      // Epilogue
      `if`.desugaredTerm = S(postProcessed)
    }(_ => "traverseIf ==> ()") catch {
      case e: DesugaringException => raiseError(e.messages: _*)
    }
  }
  
  private def traverseSplit(split: syntax.core.Split)(implicit scope: Scope): Unit =
    trace(s"traverseSplit <== [${scope.showLocalSymbols}]") {
      
      split match {
        case Split.Cons(Branch(scrutinee, pattern, continuation), tail) => 
          traverseTerm(scrutinee)
          val patternSymbols = pattern.declaredVars.map(nme => nme -> nme.symbol)
          traverseSplit(continuation)(scope.withEntries(patternSymbols))
          traverseSplit(tail)
        case Split.Let(isRec, name, rhs, tail) =>
          val recScope = scope + name.symbol
          traverseTerm(rhs)(if (isRec) recScope else scope)
          traverseSplit(tail)(recScope)
        case Split.Else(default) => traverseTerm(default)
        case Split.Nil => ()
      }
    }()
}
