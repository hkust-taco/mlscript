package mlscript
package ucs
package stages

import syntax.{core => c, source => s}
import context.{Context, Scrutinee}
import utils._, shorthands._, Message.MessageContext
import pretyper.symbol._, pretyper.{PreTyper, Scope}

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
  private def truePattern(implicit scope: Scope, context: Context) = {
    val className = Var("true")
    val classSymbol = className.resolveClassLikeSymbol
    c.Pattern.Class(className, classSymbol, false)
  }
  private def falsePattern(implicit scope: Scope, context: Context) = {
    val className = Var("false")
    val classSymbol = className.resolveClassLikeSymbol
    c.Pattern.Class(className, classSymbol, false)
  }

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
      parentScrutinee: Scrutinee,
      parentClassLikeSymbol: ClassLikeSymbol,
      parentRefined: Bool,
      parameters: Ls[s.Pattern],
  )(implicit context: Context): Ls[Opt[(Var, Opt[s.Pattern], Ls[Var])]] = {
    // Make it `lazy` so that it will not be created if all fields are wildcards.
    lazy val classPattern = parentScrutinee.getOrCreateClassPattern(parentClassLikeSymbol, parentRefined)
    def flattenPattern(
      parameterPattern: s.Pattern,
      index: Int,
      subScrutineeVarOpt: Opt[(Var, Scrutinee)],
      aliasVars: Ls[Var],
    ): Opt[(Var, Opt[s.Pattern], Ls[Var])] = { // scrutineeVar, subPattern, aliasVars
      lazy val (subScrutineeVar, subScrutinee) = subScrutineeVarOpt.getOrElse {
        val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, parentClassLikeSymbol.name, index)
        val symbol = new LocalTermSymbol(subScrutineeVar)
        val subScrutinee = classPattern.getParameter(index).withAliasVar(subScrutineeVar.withSymbol(symbol))
        symbol.addScrutinee(subScrutinee)
        (subScrutineeVar, subScrutinee)
      }
      parameterPattern match {
        case _: s.EmptyPattern => N
        case s.NamePattern(name) =>
          val subScrutinee = classPattern.getParameter(index).withAliasVar(name)
          S((name.withFreshSymbol.withScrutinee(subScrutinee), N, aliasVars.reverse))
        case parameterPattern @ (s.ClassPattern(_, _, _) | s.LiteralPattern(_) | s.TuplePattern(_)) =>
          S((subScrutineeVar, S(parameterPattern), aliasVars.reverse))
        case parameterPattern @ s.AliasPattern(aliasVar, innerPattern) =>
          println(s"alias pattern found ${subScrutineeVar.name} -> ${aliasVar.name}")
          flattenPattern(innerPattern, index, S((subScrutineeVar, subScrutinee)), aliasVar.withFreshSymbol.withScrutinee(subScrutinee) :: aliasVars)
        case pattern =>
          raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
          N
      }
    }
    trace(s"flattenClassParameters <== ${parentScrutineeVar.name} is ${parentClassLikeSymbol.name}") {
      parameters.iterator.zipWithIndex.map {
        case (pattern, index) => flattenPattern(pattern, index, N, Nil)
      }.toList
    }(r => s"flattenClassParameters ==> ${r.mkString(", ")}")
  }

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
      refined: Bool
  )(implicit context: Context): (Scope, c.Split => c.Branch) = {
    val scrutinee = scrutineeVar.getOrCreateScrutinee.withAliasVar(scrutineeVar)
    val patternClassSymbol = pattern.nme.resolveClassLikeSymbol(initialScope, context)
    val classPattern = scrutinee.getOrCreateClassPattern(patternClassSymbol, refined)
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
        val nestedPatterns = flattenClassParameters(scrutineeVar, scrutinee, patternClassSymbol, refined, parameters)
        println(s"nestedPatterns = $nestedPatterns")
        // First, handle bindings of parameters of the current class pattern.
        val identity = (split: c.Split) => split
        val bindParameters = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
          case ((N, _), bindNextParameter) => bindNextParameter
          case ((S((parameter, _, _)), index), bindNextParameter) => 
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
    (scopeWithAll, split => c.Branch(scrutineeVar, c.Pattern.Class(pattern.nme, patternClassSymbol, refined), bindAll(split)))
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
      nestedPatterns: Ls[Opt[(Var, Opt[s.Pattern], Ls[Var])]],
      scopeWithScrutinees: Scope,
      bindScrutinees: c.Split => c.Split
  )(implicit context: Context): (Scope, c.Split => c.Split) =
    trace("desugarNestedPatterns") {
      nestedPatterns.foldLeft((scopeWithScrutinees, bindScrutinees)) {
        // If this parameter is empty (e.g. produced by wildcard), then we do
        // nothing and pass on scope and binder.
        case (acc, N) => acc
        // If this sub-pattern is a class pattern, we need to recursively flatten
        // the class pattern. We will get a scope with all bindings and a function
        // that adds all bindings to a split. The scope can be passed on to the
        // next sub-pattern. The binder needs to be composed with the previous
        // binder.
        case (acc @ (scope, bindPrevious), S((nme, patternOpt, aliasVars))) =>
          println(s"subScrut = ${nme.name}; aliasVars = ${aliasVars.iterator.map(_.name).mkString("[", ", ", "]")}")
          val bindAliasVars = aliasVars.foldRight[c.Split => c.Split](identity[c.Split]) {
            case (aliasVar, bindNext) => (inner: c.Split) => c.Split.Let(false, aliasVar, nme, bindNext(inner))
          }
          patternOpt match {
            // If this parameter is not matched with a sub-pattern, then we do
            // nothing and pass on scope and binder.
            case N => (scope, bindAliasVars.andThen(bindPrevious))
            case S(pattern) => pattern match {
              case pattern: s.ClassPattern =>
                println(s"${nme.name} is ${pattern.nme.name}")
                val (scopeWithNestedAll, bindNestedAll) = desugarClassPattern(pattern, nme, scope, pattern.refined)
                (scopeWithNestedAll, split => bindPrevious(bindNestedAll(bindAliasVars(split)) :: c.Split.Nil))
              case pattern @ s.ConcretePattern(Var("true") | Var("false")) =>
                println(s"${nme.name} is ${pattern.nme.name}")
                val classSymbol = pattern.nme.resolveClassLikeSymbol(scope, context)
                (scope, split => bindPrevious(c.Branch(nme, c.Pattern.Class(pattern.nme, classSymbol, false), bindAliasVars(split)) :: c.Split.Nil))
              case s.LiteralPattern(literal) =>
                nme.getOrCreateScrutinee
                  .withAliasVar(nme)
                  .getOrCreateLiteralPattern(literal)
                  .addLocation(literal)
                (scope, bindAliasVars.andThen(makeLiteralTest(nme, literal)(scope)).andThen(bindPrevious))
              case s.TuplePattern(fields) =>
                val (scopeWithNestedAll, bindNestedAll) = desugarTuplePattern(fields, nme, scope)
                (scopeWithNestedAll, bindAliasVars.andThen(bindNestedAll).andThen(bindPrevious))
              // Well, other patterns are not supported yet.
              case _ =>
                raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
                acc
            }
          }
      }
    }()

  private def flattenTupleFields(
      parentScrutineeVar: Var,
      parentScrutinee: Scrutinee,
      fields: Ls[s.Pattern]
  )(implicit context: Context): Ls[Opt[(Var, Opt[s.Pattern], Ls[Var])]] = {
    // Make it `lazy` so that it will not be created if all fields are wildcards.
    lazy val tuplePattern = parentScrutinee.getOrCreateTuplePattern
    lazy val tupleDummyClassName = s"Tuple$$${fields.length}"
    def flattenPattern(
        pattern: s.Pattern,
        index: Int,
        subScrutineeVarOpt: Opt[(Var, Scrutinee)],
        aliasVars: Ls[Var],
    ): Opt[(Var, Opt[s.Pattern], Ls[Var])] = {
      lazy val (subScrutineeVar, subScrutinee) = subScrutineeVarOpt.getOrElse {
        val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, tupleDummyClassName, index)
        val symbol = new LocalTermSymbol(subScrutineeVar)
        val subScrutinee = tuplePattern.getField(index).withAliasVar(subScrutineeVar.withSymbol(symbol))
        symbol.addScrutinee(subScrutinee)
        (subScrutineeVar, subScrutinee)
      }
      pattern match {
        case _: s.EmptyPattern => N
        case s.NamePattern(name) =>
          S((name.withFreshSymbol.withScrutinee(tuplePattern.getField(index)), N, aliasVars.reverse))
        case parameterPattern @ (s.ClassPattern(_, _, _) | s.LiteralPattern(_) | s.TuplePattern(_)) =>
          val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, tupleDummyClassName, index)
          val symbol = new LocalTermSymbol(subScrutineeVar)
          symbol.addScrutinee(tuplePattern.getField(index).withAliasVar(subScrutineeVar))
          S((subScrutineeVar.withSymbol(symbol), S(parameterPattern), aliasVars.reverse))
        case parameterPattern @ s.ConcretePattern(nme @ (Var("true") | Var("false"))) =>
          val subScrutineeVar = freshSubScrutineeVar(parentScrutineeVar, tupleDummyClassName, index)
          val symbol = new LocalTermSymbol(subScrutineeVar)
          symbol.addScrutinee(tuplePattern.getField(index).withAliasVar(subScrutineeVar))
          S((subScrutineeVar.withSymbol(symbol), S(parameterPattern), aliasVars.reverse))
        case parameterPattern @ s.AliasPattern(aliasVar, innerPattern) =>
          println(s"alias pattern found ${subScrutineeVar.name} -> ${aliasVar.name}")
          flattenPattern(innerPattern, index, S((subScrutineeVar, subScrutinee)), aliasVar.withFreshSymbol.withScrutinee(subScrutinee) :: aliasVars)
        case pattern =>
          raiseDesugaringError(msg"unsupported pattern" -> pattern.toLoc)
          N
      }
    }
    fields.iterator.zipWithIndex.map { case (pattern, index) => flattenPattern(pattern, index, N, Nil) }.toList
  }

  private def desugarTuplePattern(fields: Ls[s.Pattern], scrutineeVar: Var, initialScope: Scope)(implicit context: Context): (Scope, c.Split => c.Split) = {
    val scrutinee = scrutineeVar.getOrCreateScrutinee.withAliasVar(scrutineeVar)
    val nestedPatterns = flattenTupleFields(scrutineeVar, scrutinee, fields)
    val bindFields = nestedPatterns.iterator.zipWithIndex.foldRight[c.Split => c.Split](identity) {
      case ((N, _), bindNextField) => bindNextField
      case ((S((parameter, _, _)), index), bindNextField) => 
        val indexVar = Var(index.toString).withLoc(parameter.toLoc)
        bindNextField.andThen { c.Split.Let(false, parameter, Sel(scrutineeVar, indexVar), _) }
    }
    val scopeWithFields = initialScope ++ nestedPatterns.flatMap(_.map(_._1.symbol))
    desugarNestedPatterns(nestedPatterns, scopeWithFields, bindFields)
  }

  private def desugarPatternSplit(
      scrutineeTerm: Term,
      split: s.PatternSplit
  )(implicit scope: Scope, context: Context): c.Split = {
    def rec(scrutineeVar: Var, split: s.PatternSplit)(implicit scope: Scope): c.Split = split match {
      case s.Split.Cons(head, tail) =>
        val scrutineeSymbol = scrutineeVar.getOrResolveTermSymbol
        val scrutinee = scrutineeSymbol.getOrCreateScrutinee
        scrutinee.addAliasVar(scrutineeVar)
        // Some functions that allow me to write less code, this function was
        // very long before I introduced them.
        def desugarRight(implicit scope: Scope) =
          desugarTermSplit(head.continuation)(PartialTerm.Empty, scope, context)
        def desugarTail(implicit scope: Scope) = rec(scrutineeVar, tail)
        def desugarPatternBranch(pattern: s.Pattern): c.Split = pattern match {
          case pattern @ s.AliasPattern(aliasVar, nestedPattern) =>
            scrutinee.addAliasVar(aliasVar.withFreshSymbol)
            c.Split.Let(false, aliasVar, scrutineeVar, desugarPatternBranch(nestedPattern))
          case s.LiteralPattern(literal) =>
            scrutinee.getOrCreateLiteralPattern(literal).addLocation(literal)
            c.Branch(scrutineeVar, c.Pattern.Literal(literal), desugarRight) :: desugarTail
          case s.ConcretePattern(nme @ (Var("true") | Var("false"))) =>
            val classSymbol = nme.resolveClassLikeSymbol
            scrutinee.getOrCreateClassPattern(classSymbol, false).addLocation(nme)
            c.Branch(
              scrutinee = scrutineeVar,
              pattern = c.Pattern.Class(nme, classSymbol, false),
              continuation = desugarRight
            ) :: desugarTail
          case s.ConcretePattern(nme) =>
            val testVar = context.freshTest().withFreshSymbol
            val testTerm = App(Var("==="), PlainTup(scrutineeVar, nme))
            c.Split.Let(false, testVar, testTerm,
              c.Branch(testVar, truePattern, desugarRight(scope + testVar.symbol)) :: desugarTail)
          case s.EmptyPattern(_) | s.NamePattern(Var("_")) =>
            desugarRight ++ desugarTail
          case s.NamePattern(nme) =>
            // If the top-level pattern is a name pattern, we need to check if
            // `nme` shadows any variables in the scope. For example, code
            // `fun f(x, y) = if x is y then "yes" else "no"` may read like
            // `if x === y then "yes" else "no"`.
            scope.getTermSymbol(nme.name) match {
              case S(shadowed) =>
                raiseDesugaringWarning(
                  msg"the outer binding `${nme.name}`" -> shadowed.nameVar.toLoc,
                  msg"is shadowed by name pattern `${nme.name}`" -> nme.toLoc
                )
              case N => ()
            }
            val symbol = freshSymbol(nme).withScrutinee(scrutinee)
            val scopeWithSymbol = scope + symbol
            c.Branch(scrutineeVar, c.Pattern.Name(nme.withSymbol(symbol)),
              desugarRight(scopeWithSymbol)) :: desugarTail(scopeWithSymbol)
          case pattern @ s.ClassPattern(nme, fields, rfd) =>
            val (scopeWithAll, bindAll) = desugarClassPattern(pattern, scrutineeVar, scope, rfd)
            bindAll(desugarRight(scopeWithAll)) :: desugarTail
          case s.TuplePattern(fields) =>
            val (scopeWithAll, bindAll) = desugarTuplePattern(fields, scrutineeVar, scope)
            bindAll(desugarRight(scopeWithAll)) ++ desugarTail
          case pattern @ s.RecordPattern(_) =>
            raiseDesugaringError(msg"record pattern is not supported for now" -> pattern.toLoc)
            desugarTail
        }
        desugarPatternBranch(head.pattern)
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
