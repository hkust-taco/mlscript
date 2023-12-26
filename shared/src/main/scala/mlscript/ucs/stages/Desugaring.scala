package mlscript.ucs.stages

import mlscript.{App, Asc, Fld, FldFlags, Lit, Sel, Term, Tup, TypeName, Var}
import mlscript.ucs.{syntax => s, core => c, PartialTerm}
import mlscript.ucs.helpers.mkBinOp
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol._
import mlscript.pretyper.{PreTyper, Scope}
import mlscript.ucs.DesugaringException
import mlscript.Message, Message.MessageContext

/**
  * The desugaring stage of UCS. In this stage, we transform the source abstract
  * syntax into core abstract syntax, which is more concise. We will make
  * following changes during this stage:
  * 
  * 1. Flatten nested patterns and generated bindings for nameless scrutinees
  *    and parameters of class-like patterns.
  * 2. Desugar variable patterns to plain let bindings.
  * 3. Desugar literal patterns to equivalent boolean expressions.
  * 4. Reassemble partial terms that are broken by "conditional splits".
  * 5. Associate each scrutinee with a unique "scrutinee symbol".
  *    TODO: `ScrutineeSymbol` will be removed in the future.
  * 
  * Desugared UCS terms (core abstract syntax) are in the form of `Split`, which
  * is a list of branches. Each branch consists of a scrutinee, a pattern, and a
  * continuation.
  */
trait Desugaring { self: PreTyper =>
  @inline def desugar(term: s.TermSplit)(implicit scope: Scope): c.Split =
    desugarTermSplit(term)(PartialTerm.Empty, scope)

  import Desugaring._

  // Call these objects to generate fresh variables for different purposes.
  // I plan to mix the unique identifiers of UCS expressions into the prefixes.
  // So that the generated variables will definitely not conflict with others.
  private val freshCache = new VariableGenerator(cachePrefix)
  private val freshScrutinee = new VariableGenerator(scrutineePrefix)
  private val freshTest = new VariableGenerator(testPrefix)

  /**
    * Coin a fresh name for a destructed parameter. The name consists of three
    * parts: the name of the parent scrutinee, the name of matched class, and
    * the index of the parameter. For example, if variable `x` is matched as
    * `Cons(hd, tl)`, then the name of `hd` will be `x$Cons_0` and the name of
    * `tl` will be `x$Cons_1`.
    */
  private def freshScrutinee(parentScrutinee: Var, parentClassName: Str, index: Int): Var =
    Var(s"${parentScrutinee}$$${parentClassName}_${index.toString}")

  /**
    * Coin a fresh name for the result of `unapply` method. The name begins with
    * `args_`, followed by the name of the scrutinee, and finally ends with the
    * name of the matched class. For example, if variable `x` is matched as
    * `Cons(hd, tl)`, then the name of `Cons.unapply(x)` will be `args_x$Cons`.
    * Parameters `hd` and `tl` are obtained by selecting `.1` and `.2` from
    * `args_x$Cons`.
    */
  private def makeUnappliedVar(scrutinee: Var, className: Var): Var =
    Var(s"$unappliedPrefix${scrutinee.name}$$${className.name}")

  // I plan to integrate scrutinee symbols into a field of `ValueSymbol`.
  // Because each `ValueSymbol` can be matched in multiple UCS expressions.
  private implicit class VarOps(nme: Var) {
    def withFreshSymbol: Var = nme.withSymbol(freshSymbol(nme))

    def getScrutineeSymbol: ScrutineeSymbol = nme.symbolOption match {
      case S(symbol: ScrutineeSymbol) => symbol
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

  /**
    * A shorthand for making a true pattern, which is useful in desugaring
    * Boolean conditions.
    */
  private def truePattern(implicit scope: Scope) = c.Pattern.Class(Var("true").withResolvedTypeSymbol)

  private def freshSymbol(nme: Var): ValueSymbol = new ValueSymbol(nme, false)

  private def desugarTermSplit(split: s.TermSplit)(implicit termPart: PartialTerm, scope: Scope): c.Split =
    split match {
      case s.Split.Cons(head, tail) => desugarTermBranch(head) ++ desugarTermSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) =>
        c.Split.Let(rec, nme, rhs, desugarTermSplit(tail)(termPart, scope + nme.withFreshSymbol.symbol)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default); 
      case s.Split.Nil => c.Split.Nil
    }

  // This function does not need to can `withCachedTermPart` because all branches assume that
  // `termPart` is either empty or waiting for an RHS.
  private def desugarTermBranch(branch: s.TermBranch)(implicit termPart: PartialTerm, scope: Scope): c.Split =
    trace(s"desugarTermBranch <== $termPart") {
      branch match {
        case s.TermBranch.Boolean(testPart, continuation) =>
          val test = freshTest().withFreshSymbol
          c.Split.Let(
            rec = false,
            name = test,
            term = Asc(termPart.addTerm(testPart, true).get, TypeName("Bool")),
            tail = c.Branch(test, truePattern, desugarTermSplit(continuation)(PartialTerm.Empty, scope + test.symbol)) :: c.Split.Nil
          )
        case s.TermBranch.Match(scrutinee, split) =>
          desugarPatternSplit(split)(termPart.addTerm(scrutinee, true).get, scope)
        case s.TermBranch.Left(left, continuation) =>
          desugarOperatorSplit(continuation)(termPart.addTerm(left, true), scope)
      }
    }()

  private def withCachedTermPart[B <: s.Branch](desugar: (PartialTerm, Scope) => c.Split)(implicit termPart: PartialTerm, scope: Scope): c.Split =
    termPart.get match {
      case v: Var => desugar(termPart, scope) // No need to cache variables.
      case rhs =>
        val cache = freshCache().withFreshSymbol
        c.Split.Let(false, cache, rhs, desugar(PartialTerm.Total(cache, Nil), scope + cache.symbol))
    }

  private def desugarOperatorSplit(split: s.OperatorSplit)(implicit termPart: PartialTerm, scope: Scope): c.Split =
    withCachedTermPart { (termPart, scope) => split match {
      case s.Split.Cons(head, tail) => desugarOperatorBranch(head)(termPart, scope) ++ desugarOperatorSplit(tail)(termPart, scope)
      case s.Split.Let(rec, nme, rhs, tail) =>
        c.Split.Let(rec, nme, rhs, desugarOperatorSplit(tail)(termPart, scope + nme.withFreshSymbol.symbol)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }}

  private def desugarOperatorBranch(branch: s.OperatorBranch)(implicit termPart: PartialTerm, scope: Scope): c.Split =
    trace(s"desugarOperatorBranch <== $termPart") {
      branch match {
        case s.OperatorBranch.Binary(op, split) => desugarTermSplit(split)(termPart.addOp(op), scope)
        case s.OperatorBranch.Match(_, split) => desugarPatternSplit(split)(termPart.get, scope)
      }
    }()

  /** Make a term like `ClassName.unapply(scrutinee)`. */
  private def makeUnapplyCall(scrutinee: Var, className: Var) = 
    App(Sel(className, Var("unapply")), Tup(N -> Fld(FldFlags.empty, scrutinee) :: Nil))

  private def makeLiteralTest(test: Var, scrutinee: Var, literal: Lit)(implicit scope: Scope): c.Split => c.Split =
    next => c.Split.Let(
      rec = false,
      name = scrutinee,
      term = mkBinOp(scrutinee, Var("=="), literal, true),
      tail = c.Branch(scrutinee, truePattern, next) :: c.Split.Nil
    )

  private def flattenClassParameters(parentScrutinee: Var, parentClassLikeSymbol: TypeSymbol, parameters: Ls[Opt[s.Pattern]]): Ls[Opt[Var -> Opt[s.Pattern]]] =
    parameters.iterator.zipWithIndex.map {
      case (N, _) => N
      case (S(s.NamePattern(name)), index) =>
        val symbol = parentScrutinee.getScrutineeSymbol.getSubScrutineeSymbolOrElse(
          parentClassLikeSymbol, index, name, new ValueSymbol(name, false)
        )
        S(name.withSymbol(symbol) -> N)
      case (S(parameterPattern @ (s.ClassPattern(_, _) | s.LiteralPattern(_) | s.TuplePattern(_))), index) =>
        val scrutinee = freshScrutinee(parentScrutinee, parentClassLikeSymbol.name, index)
        val symbol = parentScrutinee.getScrutineeSymbol.getSubScrutineeSymbolOrElse(
          parentClassLikeSymbol, index, scrutinee, new ValueSymbol(scrutinee, false)
        )
        S(scrutinee.withSymbol(symbol) -> S(parameterPattern))
      case _ => ??? // Other patterns are not implemented yet.
    }.toList

  /**
    * Recursively decompose and flatten a possibly nested class pattern. Any
    * user-declared and generated variables will be added to the given scope and
    * a augmented scope will be returned. Meanwhile, it produces a function that
    * wrap a split with all bindings and matches.
    * 
    * This function involves some higher-order function's compose operation, so
    * it is somewhat convoluted to read. However, this is a necessary
    * complication, as we need information from the scope when generating
    * variable names.
    *
    * @param pattern the class pattern
    * @param scrutinee the scrutinee of the pattern. The caller should make sure
    *                  that the scrutinee is associated with a symbol in the
    *                  given scope.
    * @param initialScope the scope before flattening the class pattern
    * @return a tuple of the augmented scope and a function that wrap a split
    */
  private def desugarClassPattern(pattern: s.ClassPattern, scrutinee: Var, initialScope: Scope): (Scope, c.Split => c.Branch) = {
    val scrutineeSymbol = scrutinee.getScrutineeSymbol
    val patternClassSymbol = pattern.nme.resolveTypeSymbol(initialScope)
    // Most importantly, we need to add the class to the list of matched classes.
    scrutineeSymbol.addMatchedClass(patternClassSymbol, pattern.nme.toLoc)
    val (scopeWithAll, bindAll) = pattern.parameters match {
      case S(parameters) =>
        // Before processing sub-patterns, we need to generate a variable that
        // holds the result of `unapply` method. Such variable might have been
        // generated by a previous branches. We MUST reuse so that we can merge
        // duplicated bindings during normalization.
        val unapp = scrutineeSymbol.getUnappliedVarOrElse(patternClassSymbol, {
          val vari = makeUnappliedVar(scrutinee, pattern.nme)
          vari.withSymbol(new ValueSymbol(vari, false))
        })
        val nestedPatterns = flattenClassParameters(scrutinee, patternClassSymbol, parameters)
        // First, handle bindings of parameters of the current class pattern.
        val bindClassParameters = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
          case ((N, _), bindNextParameter) => bindNextParameter
          case ((S(parameter -> _), index), bindNextParameter) => 
            bindNextParameter.andThen { c.Split.Let(false, parameter, Sel(unapp, Var(index.toString)), _) }
        }.andThen { c.Split.Let(false, unapp, makeUnapplyCall(scrutinee, pattern.nme), _): c.Split }
        val scopeWithClassParameters = initialScope ++ (unapp.symbol :: nestedPatterns.flatMap(_.map(_._1.symbol)))
        desugarNestedPatterns(nestedPatterns, scopeWithClassParameters, bindClassParameters)
      // If there is no parameter, then we are done.
      case N => (initialScope, identity(_: c.Split))
    }
    // Last, return the scope with all bindings and a function that adds all matches and bindings to a split.
    (scopeWithAll, split => c.Branch(scrutinee, c.Pattern.Class(pattern.nme), bindAll(split)))
  }

  /**
    * This function collects bindings from nested patterns and accumulate a
    * function that add let bindings to a split (we call such function a
    * "binder"). This function is supposed to be called from pattern desugaring
    * functions.
    *
    * @param nestedPatterns nested patterns are a list of sub-scrutinees and 
    *                       corresponding sub-patterns
    * @param scopeWithScrutinees a scope with all sub-scrutinees
    * @param bindScrutinees a function that adds all bindings to a split
    */
  private def desugarNestedPatterns(
      nestedPatterns: Ls[Opt[Var -> Opt[s.Pattern]]],
      scopeWithScrutinees: Scope,
      bindScrutinees: c.Split => c.Split
  ): (Scope, c.Split => c.Split) = {
    nestedPatterns.foldLeft((scopeWithScrutinees, bindScrutinees)) {
      // If this parameter is not matched with a sub-pattern, then we do
      // nothing and pass on scope and binder.
      case (acc, S(_ -> N)) => acc
      // If this sub-pattern is a class pattern, we need to recursively flatten
      // the class pattern. We will get a scope with all bindings and a function
      // that adds all bindings to a split. The scope can be passed on to the
      // next sub-pattern. The binder needs to be composed with the previous
      // binder.
      case ((scope, bindPrevious), S(nme -> S(pattern: s.ClassPattern))) =>
        val (scopeWithNestedAll, bindNestedAll) = desugarClassPattern(pattern, nme, scope)
        (scopeWithNestedAll, split => bindPrevious(bindNestedAll(split) :: c.Split.Nil))
      case ((scope, bindPrevious), S(nme -> S(pattern: s.LiteralPattern))) =>
        val test = freshTest().withFreshSymbol
        (scope + test.symbol, makeLiteralTest(test, nme, pattern.literal)(scope).andThen(bindPrevious))
      case ((scope, bindPrevious), S(nme -> S(s.TuplePattern(fields)))) =>
        val (scopeWithNestedAll, bindNestedAll) = desugarTuplePattern(fields, nme, scope)
        (scopeWithNestedAll, bindNestedAll.andThen(bindPrevious))
      // Well, other patterns are not supported yet.
      case (acc, S((nme, pattern))) => ???
      // If this parameter is empty (e.g. produced by wildcard), then we do
      // nothing and pass on scope and binder.
      case (acc, N) => acc
    }
  }

  private def flattenTupleFields(parentScrutinee: Var, fields: Ls[Opt[s.Pattern]]): Ls[Opt[Var -> Opt[s.Pattern]]] =
    fields.iterator.zipWithIndex.map {
      case (N, _) => N
      case (S(s.NamePattern(name)), index) =>
        val symbol = parentScrutinee.getScrutineeSymbol.getTupleSubScrutineeSymbolOrElse(
          index, name, new ValueSymbol(name, false)
        )
        S(name.withSymbol(symbol) -> N)
      case (S(parameterPattern @ (s.ClassPattern(_, _) | s.LiteralPattern(_) | s.TuplePattern(_))), index) =>
        val scrutinee = freshScrutinee(parentScrutinee, "Tuple$2", index)
        val symbol = parentScrutinee.getScrutineeSymbol.getTupleSubScrutineeSymbolOrElse(
          index, scrutinee, new ValueSymbol(scrutinee, false)
        )
        S(scrutinee.withSymbol(symbol) -> S(parameterPattern))
      case _ => ???
    }.toList

  private def desugarTuplePattern(fields: Ls[Opt[s.Pattern]], scrutinee: Var, initialScope: Scope): (Scope, c.Split => c.Split) = {
    val scrutineeSymbol = scrutinee.getScrutineeSymbol
    val nestedPatterns = flattenTupleFields(scrutinee, fields)
    val bindTupleFields = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
      case ((N, _), bindNextField) => bindNextField
      case ((S(parameter -> _), index), bindNextField) => 
        val indexVar = Var(index.toString).withLoc(parameter.toLoc)
        bindNextField.andThen { c.Split.Let(false, parameter, Sel(scrutinee, indexVar), _) }
    }
    val scopeWithTupleFields = initialScope ++ nestedPatterns.flatMap(_.map(_._1.symbol))
    desugarNestedPatterns(nestedPatterns, scopeWithTupleFields, bindTupleFields)
  }

  private def desugarPatternSplit(split: s.PatternSplit)(implicit scrutinee: Term, scope: Scope): c.Split = {
    def rec(scrutinee: Var, split: s.PatternSplit)(implicit scope: Scope): c.Split = split match {
      case s.Split.Cons(head, tail) => 
        head.pattern match {
          case s.AliasPattern(nme, pattern) => ???
          case s.LiteralPattern(literal) => ???
          case s.ConcretePattern(nme) => 
            val test = freshTest().withFreshSymbol
            c.Split.Let(
              rec = false,
              name = test,
              term = mkBinOp(scrutinee, Var("==="), nme, true),
              tail = c.Branch(
                scrutinee = test,
                pattern = truePattern,
                continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope + test.symbol)
              ) :: rec(scrutinee, tail)
            )
          case s.NamePattern(Var("_")) =>
            desugarTermSplit(head.continuation)(PartialTerm.Empty, scope) ++ rec(scrutinee, tail)
          case s.NamePattern(nme) =>
            // Share the scrutinee's symbol with its aliases.
            // nme.symbol = scrutinee.symbol // <-- This currently causes a bug, reuse this line after we remove `ScrutineeSymbol`.
            nme.symbol = new ValueSymbol(nme, false)
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope + nme.symbol)
            c.Branch(scrutinee, c.Pattern.Name(nme), continuation) :: rec(scrutinee, tail)(scope + nme.symbol)
          case pattern @ s.ClassPattern(nme, fields) =>
            println(s"find term symbol of $scrutinee in ${scope.showLocalSymbols}")
            scrutinee.symbol = scope.getTermSymbol(scrutinee.name).getOrElse(???)
            val (scopeWithAll, bindAll) = desugarClassPattern(pattern, scrutinee, scope)
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scopeWithAll)
            bindAll(continuation) :: rec(scrutinee, tail)
          case s.TuplePattern(fields) =>
            scrutinee.symbol = scope.getTermSymbol(scrutinee.name).getOrElse(???)
            val (scopeWithAll, bindAll) = desugarTuplePattern(fields, scrutinee, scope)
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scopeWithAll)
            val withBindings = bindAll(continuation)
            if (withBindings.hasElse) {
              withBindings
            } else {
              withBindings ++ rec(scrutinee, tail)
            }
          case s.RecordPattern(entries) => ???
        }
      case s.Split.Let(isRec, nme, rhs, tail) =>
        c.Split.Let(isRec, nme, rhs, rec(scrutinee, tail)(scope + nme.withFreshSymbol.symbol)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }
    scrutinee match {
      case nme: Var => rec(nme, split)
      case other =>
        val alias = freshScrutinee().withFreshSymbol
        c.Split.Let(false, alias, scrutinee, rec(alias, split)(scope + alias.symbol))
    }
  }
}

object Desugaring {
  class VariableGenerator(prefix: Str) {
    private var nextIndex = 0

    def apply(): Var = {
      val thisIndex = nextIndex
      nextIndex += 1
      Var(s"$prefix$thisIndex")
    }
  }

  val cachePrefix = "cache$"
  val scrutineePrefix = "scrut$"
  val testPrefix = "test$"
  val unappliedPrefix = "args_"

  def isCacheVar(nme: Var): Bool = nme.name.startsWith(cachePrefix)
  def isScrutineeVar(nme: Var): Bool = nme.name.startsWith(scrutineePrefix)
  def isTestVar(nme: Var): Bool = nme.name.startsWith(testPrefix)
  def isUnappliedVar(nme: Var): Bool = nme.name.startsWith(unappliedPrefix)
  def isGeneratedVar(nme: Var): Bool =
    isCacheVar(nme) || isScrutineeVar(nme) || isTestVar(nme) || isUnappliedVar(nme)
}