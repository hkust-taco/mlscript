package mlscript.ucs.stages

import mlscript.{App, Asc, Fld, FldFlags, Lit, Sel, Term, Tup, TypeName, Var}
import mlscript.ucs.syntax.{core => c, source => s}
import mlscript.ucs.context.{Context, ScrutineeData}
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol._
import mlscript.pretyper.{PreTyper, Scope}
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
  * 5. Associate each scrutinee with a unique `ScrutineeData`.
  * 
  * Desugared UCS terms (core abstract syntax) are in the form of `Split`, which
  * is a list of branches. Each branch consists of a scrutinee, a pattern, and a
  * continuation.
  */
trait Desugaring { self: PreTyper =>
  import Desugaring._

  /**
    * The entry point of the desugaring stage.
    *
    * @param term the root of source abstrax syntax term, obtained from the
    *             transformation stage
    * @param scope the scope is for resolving type symbols. The scope should
    *              contains a TypeSymbol for `true` literal.
    * @return the root of desugared core abstract syntax term
    */
  @inline def desugar(term: s.TermSplit)(implicit scope: Scope, context: Context): c.Split =
    desugarTermSplit(term)(PartialTerm.Empty, scope, context)

  /**
    * Coin a fresh name for a destructed parameter. The name consists of three
    * parts: the name of the parent scrutinee, the name of matched class, and
    * the index of the parameter. For example, if variable `x` is matched as
    * `Cons(hd, tl)`, then the name of `hd` will be `x$Cons_0` and the name of
    * `tl` will be `x$Cons_1`.
    */
  private def freshSubScrutineeVar(parentScrutinee: Var, parentClassName: Str, index: Int): Var =
    Var(s"${parentScrutinee.name}$$${parentClassName}_${index.toString}")

  /**
    * Coin a fresh name for the result of `unapply` method. The name begins with
    * `args_`, followed by the name of the scrutinee, and finally ends with the
    * name of the matched class. For example, if variable `x` is matched as
    * `Cons(hd, tl)`, then the name of `Cons.unapply(x)` will be `args_x$Cons`.
    * Parameters `hd` and `tl` are obtained by selecting `.1` and `.2` from
    * `args_x$Cons`.
    */
  private def makeUnappliedVar(scrutinee: Var, className: Var)(implicit context: Context): Var =
    Var(s"${context.unappliedPrefix}${scrutinee.name}$$${className.name}")

  /**
    * A shorthand for making a true pattern, which is useful in desugaring
    * Boolean conditions.
    */
  private def truePattern(implicit scope: Scope, context: Context) =
    c.Pattern.Class(Var("true").withResolvedClassLikeSymbol, false)
  private def falsePattern(implicit scope: Scope, context: Context) =
    c.Pattern.Class(Var("false").withResolvedClassLikeSymbol, false)

  private def desugarTermSplit(split: s.TermSplit)(implicit termPart: PartialTerm.Incomplete, scope: Scope, context: Context): c.Split =
    split match {
      case s.Split.Cons(head, tail) => desugarTermBranch(head) ++ desugarTermSplit(tail)
      case s.Split.Let(rec, nme, rhs, tail) =>
        c.Split.Let(rec, nme, rhs, desugarTermSplit(tail)(termPart, scope + nme.withFreshSymbol.symbol, context)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default); 
      case s.Split.Nil => c.Split.Nil
    }

  // This function does not need to can `withCachedTermPart` because all branches assume that
  // `termPart` is either empty or waiting for an RHS.
  private def desugarTermBranch(branch: s.TermBranch)(implicit termPart: PartialTerm.Incomplete, scope: Scope, context: Context): c.Split =
    trace(s"desugarTermBranch <== $termPart") {
      branch match {
        case s.TermBranch.Boolean(testPart, continuation) =>
          val test = context.freshTest().withFreshSymbol
          c.Split.Let(
            rec = false,
            name = test,
            term = Asc(termPart.addTerm(testPart).get, TypeName("Bool")),
            tail = c.Branch(test, truePattern, desugarTermSplit(continuation)(PartialTerm.Empty, scope + test.symbol, context)) :: c.Split.Nil
          )
        case s.TermBranch.Match(scrutinee, split) =>
          desugarPatternSplit(termPart.addTerm(scrutinee).get, split)
        case s.TermBranch.Left(left, continuation) =>
          desugarOperatorSplit(continuation)(termPart.addTerm(left), scope, context)
      }
    }()

  private def withCachedTermPart[B <: s.Branch](desugar: (PartialTerm.Total, Scope) => c.Split)(implicit termPart: PartialTerm.Total, scope: Scope, context: Context): c.Split =
    termPart.get match {
      case v: Var => desugar(termPart, scope) // No need to cache variables.
      case rhs =>
        val cache = context.freshCache().withFreshSymbol
        c.Split.Let(false, cache, rhs, desugar(PartialTerm.Total(cache, Nil), scope + cache.symbol))
    }

  private def desugarOperatorSplit(split: s.OperatorSplit)(implicit termPart: PartialTerm.Total, scope: Scope, context: Context): c.Split =
    withCachedTermPart { (termPart, scope) => split match {
      case s.Split.Cons(head, tail) => desugarOperatorBranch(head)(termPart, scope, context) ++ desugarOperatorSplit(tail)(termPart, scope, context)
      case s.Split.Let(rec, nme, rhs, tail) =>
        c.Split.Let(rec, nme, rhs, desugarOperatorSplit(tail)(termPart, scope + nme.withFreshSymbol.symbol, context)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }}

  private def desugarOperatorBranch(branch: s.OperatorBranch)(implicit termPart: PartialTerm.Total, scope: Scope, context: Context): c.Split =
    trace(s"desugarOperatorBranch <== $termPart") {
      branch match {
        case s.OperatorBranch.Binary(op, split) => desugarTermSplit(split)(termPart.addOp(op), scope, context)
        case s.OperatorBranch.Match(_, split) => desugarPatternSplit(termPart.get, split)(scope, context)
      }
    }()

  private def makeLiteralTest(scrutinee: Var, literal: Lit)(implicit scope: Scope): c.Split => c.Split =
    next => c.Branch(scrutinee, c.Pattern.Literal(literal), next) :: c.Split.Nil

  private def flattenClassParameters(
      parentScrutineeVar: Var,
      parentClassLikeSymbol: TypeSymbol,
      parameters: Ls[s.Pattern]
  )(implicit context: Context): Ls[Opt[Var -> Opt[s.Pattern]]] =
    trace(s"flattenClassParameters <== ${parentScrutineeVar.name} is ${parentClassLikeSymbol.name}") {
      // Make it `lazy` so that it will not be created if all fields are wildcards.
      lazy val classPattern = parentScrutineeVar.getOrCreateScrutinee.getOrCreateClassPattern(parentClassLikeSymbol)
      parameters.iterator.zipWithIndex.map {
        case (_: s.EmptyPattern, _) => N
        case (s.NamePattern(name), index) =>
          val subScrutinee = classPattern.getParameter(index).withAlias(name)
          S(name.withFreshSymbol.withScrutinee(subScrutinee) -> N)
        case (parameterPattern @ (s.ClassPattern(_, _, _) | s.LiteralPattern(_) | s.TuplePattern(_)), index) =>
          val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, parentClassLikeSymbol.name, index)
          val symbol = new LocalTermSymbol(subScrutineeVar)
          symbol.addScrutinee(classPattern.getParameter(index).withAlias(subScrutineeVar))
          S(subScrutineeVar.withSymbol(symbol) -> S(parameterPattern))
        case (pattern, _) =>
          raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
          N
      }.toList
    }(r => s"flattenClassParameters ==> ${r.mkString(", ")}")

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
  private def desugarClassPattern(
      pattern: s.ClassPattern,
      scrutineeVar: Var,
      initialScope: Scope,
      refined: Bool)(implicit context: Context): (Scope, c.Split => c.Branch) = {
    val scrutinee = scrutineeVar.getOrCreateScrutinee.withAlias(scrutineeVar)
    val patternClassSymbol = pattern.nme.resolveClassLikeSymbol(initialScope, context)
    val classPattern = scrutinee.getOrCreateClassPattern(patternClassSymbol)
    println(s"desugarClassPattern: ${scrutineeVar.name} is ${pattern.nme.name}")
    classPattern.addLocation(pattern.nme)
    val (scopeWithAll, bindAll) = pattern.parameters match {
      case S(parameters) =>
        // Before processing sub-patterns, we need to generate a variable that
        // holds the result of `unapply` method. Such variable might have been
        // generated by a previous branches. We MUST reuse so that we can merge
        // duplicated bindings during normalization.
        lazy val unapp = classPattern.getUnappliedVar {
          val vari = makeUnappliedVar(scrutineeVar, pattern.nme)
          vari.withSymbol(new LocalTermSymbol(vari))
        }
        val nestedPatterns = flattenClassParameters(scrutineeVar, patternClassSymbol, parameters)
        println(s"nestedPatterns = $nestedPatterns")
        // First, handle bindings of parameters of the current class pattern.
        val identity = (split: c.Split) => split
        val bindParameters = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
          case ((N, _), bindNextParameter) => bindNextParameter
          case ((S(parameter -> _), index), bindNextParameter) => 
            bindNextParameter.andThen { c.Split.Let(false, parameter, Sel(unapp, Var(index.toString)), _) }
        }
        println(s"bindParameters === identity: ${bindParameters === identity}")
        val bindAll = if (bindParameters === identity) bindParameters else bindParameters.andThen {
          c.Split.Let(false, unapp, makeUnapplyCall(scrutineeVar, pattern.nme), _): c.Split
        }
        val scopeWithClassParameters = initialScope ++ (unapp.symbol :: nestedPatterns.flatMap(_.map(_._1.symbol)))
        desugarNestedPatterns(nestedPatterns, scopeWithClassParameters, bindAll)
      // If there is no parameter, then we are done.
      case N => (initialScope, identity(_: c.Split))
    }
    println(s"${scrutineeVar.name}: ${scrutinee.showPatternsDbg}")
    // Last, return the scope with all bindings and a function that adds all matches and bindings to a split.
    (scopeWithAll, split => c.Branch(scrutineeVar, c.Pattern.Class(pattern.nme, refined), bindAll(split)))
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
  )(implicit context: Context): (Scope, c.Split => c.Split) =
    trace("desugarNestedPatterns") {
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
          println(s"${nme.name} is ${pattern.nme.name}")
          val (scopeWithNestedAll, bindNestedAll) = desugarClassPattern(pattern, nme, scope, pattern.refined)
          (scopeWithNestedAll, split => bindPrevious(bindNestedAll(split) :: c.Split.Nil))
        case ((scope, bindPrevious), S(nme -> S(pattern: s.LiteralPattern))) =>
          nme.getOrCreateScrutinee
             .withAlias(nme)
             .getOrCreateLiteralPattern(pattern.literal)
             .addLocation(pattern.literal)
          (scope, makeLiteralTest(nme, pattern.literal)(scope).andThen(bindPrevious))
        case ((scope, bindPrevious), S(nme -> S(s.TuplePattern(fields)))) =>
          val (scopeWithNestedAll, bindNestedAll) = desugarTuplePattern(fields, nme, scope)
          (scopeWithNestedAll, bindNestedAll.andThen(bindPrevious))
        // Well, other patterns are not supported yet.
        case (acc, S(nme -> S(pattern))) =>
          raiseDesugaringError(msg"unsupported pattern is" -> pattern.toLoc)
          acc
        // If this parameter is empty (e.g. produced by wildcard), then we do
        // nothing and pass on scope and binder.
        case (acc, N) => acc
      }
    }()

  private def flattenTupleFields(parentScrutineeVar: Var, fields: Ls[s.Pattern])(implicit context: Context): Ls[Opt[Var -> Opt[s.Pattern]]] = {
    // Make it `lazy` so that it will not be created if all fields are wildcards.
    lazy val tuplePattern = parentScrutineeVar.getOrCreateScrutinee.getOrCreateTuplePattern
    fields.iterator.zipWithIndex.map {
      case (_: s.EmptyPattern, _) => N
      case (s.NamePattern(name), index) =>
        S(name.withFreshSymbol.withScrutinee(tuplePattern.getField(index)) -> N)
      case (parameterPattern @ (s.ClassPattern(_, _, _) | s.LiteralPattern(_) | s.TuplePattern(_)), index) =>
        val arity = fields.length
        val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, s"Tuple$$$arity", index)
        val symbol = new LocalTermSymbol(subScrutineeVar)
        symbol.addScrutinee(tuplePattern.getField(index).withAlias(subScrutineeVar))
        S(subScrutineeVar.withSymbol(symbol) -> S(parameterPattern))
      case (pattern, _) =>
        raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
        N
    }.toList
  }

  private def desugarTuplePattern(fields: Ls[s.Pattern], scrutineeVar: Var, initialScope: Scope)(implicit context: Context): (Scope, c.Split => c.Split) = {
    val scrutinee = scrutineeVar.getOrCreateScrutinee.withAlias(scrutineeVar)
    val nestedPatterns = flattenTupleFields(scrutineeVar, fields)
    val bindFields = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
      case ((N, _), bindNextField) => bindNextField
      case ((S(parameter -> _), index), bindNextField) => 
        val indexVar = Var(index.toString).withLoc(parameter.toLoc)
        bindNextField.andThen { c.Split.Let(false, parameter, Sel(scrutineeVar, indexVar), _) }
    }
    val scopeWithFields = initialScope ++ nestedPatterns.flatMap(_.map(_._1.symbol))
    desugarNestedPatterns(nestedPatterns, scopeWithFields, bindFields)
  }

  private def desugarPatternSplit(scrutineeTerm: Term, split: s.PatternSplit)(implicit scope: Scope, context: Context): c.Split = {
    def rec(scrutineeVar: Var, split: s.PatternSplit)(implicit scope: Scope): c.Split = split match {
      // TODO: We should resolve `scrutineeVar`'s symbol and make sure it is a term symbol in the
      // beginning. So that we can call methods on the symbol directly. Now there are too many
      // helper functions on `VarOps`.
      case s.Split.Cons(head, tail) =>
        head.pattern match {
          case pattern @ s.AliasPattern(_, _) =>
            raiseDesugaringError(msg"alias pattern is not supported for now" -> pattern.toLoc)
            rec(scrutineeVar, tail)
          case s.LiteralPattern(literal) =>
            scrutineeVar.getOrCreateScrutinee.withAlias(scrutineeVar).getOrCreateLiteralPattern(literal).addLocation(literal)
            c.Branch(
              scrutinee = scrutineeVar,
              pattern = c.Pattern.Literal(literal),
              continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope, context)
            ) :: rec(scrutineeVar, tail)
          case s.ConcretePattern(nme @ (Var("true") | Var("false"))) =>
            scrutineeVar.getOrCreateScrutinee.withAlias(scrutineeVar).getOrCreateBooleanPattern(nme).addLocation(nme)
            c.Branch(
              scrutinee = scrutineeVar,
              pattern = c.Pattern.Class(nme.withResolvedClassLikeSymbol, false),
              continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope, context)
            ) :: rec(scrutineeVar, tail)
          case s.ConcretePattern(nme) =>
            val test = context.freshTest().withFreshSymbol
            c.Split.Let(
              rec = false,
              name = test,
              term = mkBinOp(scrutineeVar, Var("==="), nme, true),
              tail = c.Branch(
                scrutinee = test,
                pattern = truePattern,
                continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope + test.symbol, context)
              ) :: rec(scrutineeVar, tail)
            )
          case s.EmptyPattern(_) | s.NamePattern(Var("_")) =>
            desugarTermSplit(head.continuation)(PartialTerm.Empty, scope, context) ++ rec(scrutineeVar, tail)
          case s.NamePattern(nme) =>
            // Create a symbol for the binding.
            val symbol = new LocalTermSymbol(nme)
            // Share the scrutineeVar's symbol with its aliases.
            symbol.addScrutinee(scrutineeVar.getOrCreateScrutinee.withAlias(nme))
            // Associate the symbol with the binding.
            nme.symbol = symbol
            // Whoosh! Done.
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scope + nme.symbol, context)
            c.Branch(scrutineeVar, c.Pattern.Name(nme), continuation) :: rec(scrutineeVar, tail)(scope + nme.symbol)
          case pattern @ s.ClassPattern(nme, fields, rfd) =>
            val scrutineeSymbol = scrutineeVar.getOrResolveTermSymbol // TODO: Useless.
            val (scopeWithAll, bindAll) = desugarClassPattern(pattern, scrutineeVar, scope, rfd)
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scopeWithAll, context)
            bindAll(continuation) :: rec(scrutineeVar, tail)
          case s.TuplePattern(fields) =>
            val scrutineeSymbol = scrutineeVar.getOrResolveTermSymbol // TODO: Useless.
            val (scopeWithAll, bindAll) = desugarTuplePattern(fields, scrutineeVar, scope)
            val continuation = desugarTermSplit(head.continuation)(PartialTerm.Empty, scopeWithAll, context)
            val withBindings = bindAll(continuation)
            if (withBindings.hasElse) {
              withBindings
            } else {
              withBindings ++ rec(scrutineeVar, tail)
            }
          case pattern @ s.RecordPattern(_) =>
            raiseDesugaringError(msg"record pattern is not supported for now" -> pattern.toLoc)
            rec(scrutineeVar, tail)
        }
      case s.Split.Let(isRec, nme, rhs, tail) =>
        c.Split.Let(isRec, nme, rhs, rec(scrutineeVar, tail)(scope + nme.withFreshSymbol.symbol)) // <-- Weird use.
      case s.Split.Else(default) => c.Split.Else(default)
      case s.Split.Nil => c.Split.Nil
    }
    scrutineeTerm match {
      case nme: Var => rec(nme.withResolvedTermSymbol, split)
      case other =>
        val alias = context.freshScrutineeVar().withFreshSymbol
        c.Split.Let(false, alias, other, rec(alias, split)(scope + alias.symbol))
    }
  }
}

object Desugaring {
  /** Make a term like `ClassName.unapply(scrutinee)`. */
  private def makeUnapplyCall(scrutinee: Var, className: Var) = 
    App(Sel(className, Var("unapply").withLocOf(className)), Tup(N -> Fld(FldFlags.empty, scrutinee) :: Nil))
}
