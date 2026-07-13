package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import collection.immutable.HashMap, collection.mutable.Buffer
import syntax.{Keyword, SpreadKind, Tree}, Tree.{Ident, StrLit}
import Elaborator.State, Message.MessageContext, ucs.error
import scala.annotation.tailrec, util.chaining.*
import utils.{TraceLogger, tl}

object Pattern:
  /** The reason why a variable obtained from `Pattern.variables` is invalid. */
  enum InvalidReason:
    /** The variable shadowed another variable.
     *  @param previous The identifiers shadowed by the current aliases. */
    case Duplicated(previous: Ls[Ident])
    /** The variable presents in one side of disjunction, but not the other. */
    case Inconsistent(disjunction: Pattern.Composition, missingOnTheLeft: Bool)
    /** The variable is bound in a `Negation` pattern. */
    case Negated(negation: Pattern.Negation)
    /** Higher-order pattern arguments contain free variables. For example, `x`
     *  in `pattern MaybeInt = Nullable(pattern Int as x)` is invalid. Because
     *  `MaybeInt` does not guarantee that `Int as x` is used in `Nullable`. */
    case Escaped(pattern: Pattern)
  
  import InvalidReason.*
  
  /** A set of variables that present in a pattern.
   *  
   *  These variables are represented by `Tree.Ident` because not every identifier
   *  can represent a meaningful binding. This set is used in the computed property
   *  on the `Pattern` tree. We only create `VarSymbol` for these variables at the
   *  root node or when elaborating the term of a `Transform` pattern.
   * 
   *  @param varMap A map from variable names to their valid aliases. Multiple
   *                aliases are allowed when they are in different disjunctions.
   *  @param invalidVars A list of variables and the reason why they are invalid.
   */
  final case class Variables(
      varMap: HashMap[Str, Ls[Pattern.Alias]],
      invalidVars: Ls[(Pattern.Alias, InvalidReason)]
  ):
    /** Allocate symbols for all variables. */
    def allocate(using State, TraceLogger): Seq[(Str, VarSymbol)] =
      varMap.iterator.map: (name, aliases) =>
        // We need to assign the same symbol to the same name. But I realize
        // that the following cases will break this constraint: `(x where x > 0)
        // | (x where x < 0)`. In both alternatives, `x` needs to be allocated
        // in advanced, but at the level of the disjunction, `x` needs to be
        // assigned to the same variable. This represents an edge case which
        // needs to be fixed later.
        val symbols = aliases.iterator.flatMap(_.symbolOption).toSet
        // TODO: The above edge case would fail the following assertion.
        assert(symbols.size <= 1)
        // If no symbol had been created before, create a new symbol now.
        val symbol = symbols.headOption.getOrElse(VarSymbol(Ident(name)))
        aliases.foreach: alias =>
          // For guarded patterns (`p where t`), the variables in `p` have to be
          // allocated before `t` is elaborated. In that case, we don't need to
          // allocate the variables in `p` again when the variables of pattern
          // containing `p` are allocated.
          if alias.symbolOption.isEmpty then alias.symbol = symbol
        (name, symbol)
      .toSeq
    
    /** Get all symbols for the variables. */
    def symbols: Ls[VarSymbol] =
      varMap.iterator.flatMap(_._2.head.symbolOption).toList
    
    /** Add a single variable to the variable set. */
    def +(alias: Pattern.Alias): Variables =
      varMap.get(alias.id.name) match
        // Add the alias to the variable set if the name has not been used.
        case N => Variables(varMap + (alias.id.name -> Ls(alias)), invalidVars)
        case S(oldAliases) => Variables(
          varMap.updated(alias.id.name, Ls(alias)),
          // Append the invalid reason: `alias` shadows `oldAliases`.
          invalidVars :+ (alias -> Duplicated(oldAliases.map(_.id))))
    
    /** Union two variable sets. If the latter contains a variable that is
     *  already present in the former, the variable is considered duplicated. */
    def ++(that: Variables): Variables =
      val duplicated: Buffer[(Alias, InvalidReason)] = Buffer.empty
      Variables(
        varMap.merged(that.varMap):
          case ((name, previous), (_, aliases)) =>
            duplicated ++= aliases.map(_ -> Duplicated(previous.map(_.id)))
            (name, aliases),
        invalidVars ::: that.invalidVars ::: duplicated.toList)
    
    /** For debugging purpose only. */
    def display: Str = varMap.iterator.map:
      case (key, aliases) =>
        key + " -> " + aliases.iterator.map(_.id.name).mkString(", ")
    .mkString("{", "; ", "}")
    
    /** Intersect two variable sets and move variables that are only present in
     *  one side to the invalid variables. This method considers `this` as the
     *  left side, and `that` as the right side. */
    def intersect(that: Variables, pattern: Pattern.Composition): Variables =
      // Check if two variable sets are the same.
      val notInThat = varMap.removedAll(that.varMap.keys)
      val notInThis = that.varMap.removedAll(varMap.keys)
      Variables(
        // Merge two sets and remove variables that only present in one side.
        varMap.merged(that.varMap):
          case ((name, left), (_, right)) => (name, left ::: right)
        .removedAll(Iterable.concat(notInThat.keys, notInThis.keys)),
        // Add variables that only present in one side to the invalid variables.
        invalidVars :::
          notInThis.iterator.flatMap(_._2.map(_ -> Inconsistent(pattern, true))).toList :::
          notInThat.iterator.flatMap(_._2.map(_ -> Inconsistent(pattern, false))).toList)
    
    /** Mark all variables in this set as invalid. */
    def invalidated(reason: InvalidReason): Variables =
      Variables(HashMap.empty, invalidVars appendedAll varMap.iterator.flatMap(_._2.map(_ -> reason)))
    
    /** Report all invalid variables. */
    def report(using Raise): Unit = invalidVars.foreach:
      case (Alias(_, id), Duplicated(previous)) => raise(ErrorReport(
        msg"Duplicated pattern variable." -> id.toLoc ::
        msg"The previous definition ${if previous.size === 1 then "is" else "are"} as follows." -> previous.head.toLoc ::
        previous.tail.map(msg"" -> _.toLoc)))
      case (Alias(_, id), Inconsistent(disjunction, missingOnTheLeft)) => error(
        msg"Found an inconsistent variable in disjunction patterns." -> id.toLoc,
        msg"The variable is missing from this sub-pattern." -> (
          if missingOnTheLeft then disjunction.left else disjunction.right
        ).toLoc)
      case (Alias(pattern, id), Negated(negation)) => error(
        pattern match
          case Wildcard() => msg"This variable cannot be accessed." -> id.toLoc
          case _: Pattern => msg"This pattern cannot be bound." -> pattern.toLoc,
        msg"Because the pattern it belongs to is negated." -> negation.toLoc)
      case (Alias(_, id), Escaped(p)) => error(
        msg"This pattern variable escapes its higher-order pattern argument." -> id.toLoc,
        msg"It is bound in this pattern." -> p.toLoc)
    
  object Variables:
    lazy val empty: Variables = Variables(HashMap.empty, Nil)
  
  extension (patterns: IterableOnce[Pattern])
    def variables: Variables = patterns.iterator.foldLeft(Variables.empty):
      case (vars, pattern) => vars ++ pattern.variables
  
  /** A shorthand for creating a variable pattern. */
  def Variable = Pattern.Wildcard() binds (_: Ident)
  
  trait ConstructorImpl:
    self: Pattern.Constructor =>
    
    /** Get the resolved symbol of the target term. */
    def symbol: Opt[Symbol] = self.target.resolvedSym
    
    /** Expect the `symbol` to be set. */
    def symbol_! : Symbol = symbol.getOrElse:
      lastWords(s"target term `${self.target}` does not resolve to a symbol")
  
  /** Add a mutable field to the `Alias` pattern to store the symbol for the
   *  variable. Note that NOT every `Alias` pattern has a symbol. */
  trait AliasImpl:
    self: Pattern.Alias =>
    private var _symbol: Opt[VarSymbol] = N
    /** Directly set the symbol for the variable. This should be called in the
     *  elaborator when elaborating the non-`Transform` top-level pattern. */
    def symbol_=(symbol: VarSymbol): Unit = _symbol = S(symbol)
    def symbolOption: Opt[VarSymbol] = _symbol
    def symbol: VarSymbol = _symbol.getOrElse:
      lastWords(s"no symbol was assigned to variable `${id.name}` at ${id.toLoc}")

import Pattern.*, InvalidReason.*

/** An inductive data type for patterns. */
enum Pattern extends AutoLocated:
  /** A pattern that matches a constructor and its arguments.
   *  @param target The term representing the constructor.
   *  @param arguments `None` if the pattern does not have a parameter list. The
   *      patterns that are used to destruct the constructor's arguments.
   */
  case Constructor(
      target: Term,
      arguments: Opt[Ls[Pattern]]
  ) extends Pattern with ConstructorImpl
  
  /** A pattern that is the composition of two patterns.
   *  @param polarity `true` if the pattern is a disjunction, `false` if it is
   *                  a conjunction.
   */
  case Composition(polarity: Bool, left: Pattern, right: Pattern)
  
  /** A pattern that is the negation of another pattern. We don't allow negation
   *  patterns to be nested. They can only be used as the top-level pattern.
   *  Also, what's the point of binding the inner pattern? 
   */
  case Negation(pattern: Pattern)
  
  /** A pattern that matches any value. It is syntically denoted by `_`. */
  case Wildcard()
  
  /** A pattern that matches the given literal. */
  case Literal(literal: syntax.Literal)
  
  /** A pattern that matches a range of values. */
  case Range(lower: syntax.Literal, upper: syntax.Literal, rightInclusive: Bool)
  
  /** A pattern that matches the concatenation of two string patterns. The
   *  concatenation of non-string patterns results in a never-match pattern. */
  case Concatenation(left: Pattern, right: Pattern)
  
  /** A pattern that matches a tuple. At most one `spread` pattern is allowed.
    * When the `spread` pattern is absent, sub-patterns should be placed in the 
    * `leading` field.
    * @param leading matches a fixed number of leading elements in the tuple.
    * @param spread matches a variable number of elements in the tuple plus
    *               the trailing elements.
    */
  case Tuple(
      leading: Ls[Pattern],
      spread: Opt[(SpreadKind, Pattern, Ls[Pattern])],
  )
  
  /** A pattern that matches a record consisting of a list of fields. Note that
   *  the fields are not ordered semantically. */
  case Record(fields: Ls[(Ident, Pattern)])
  
  /** Chain one pattern to another. The pattern matches the input value against
   *  the `first` pattern, and then matches its output against the `second`
   *  pattern. It fails when either of the patterns fails.
   */
  case Chain(first: Pattern, second: Pattern)
  
  /** A pattern that matches the same value as another pattern, but bind the
   *  matched value to a new variable. This is the only class that holds the
   *  symbol for the variable. */
  case Alias(pattern: Pattern, id: Ident) extends Pattern with AliasImpl
  
  /** A pattern that matches the same value as other pattern, with an additional
    * function applied to the bound variables in the pattern.
    *
    * @param pattern The pattern to be matched against.
    * @param parameters A map from the variable symbols to parameter symbols.
    * @param transform The term that should be applied to the extracted values.
   */
  case Transform(pattern: Pattern, parameters: Ls[(VarSymbol, VarSymbol)], transform: Term)
  
  /** If the term is `Error`, we add `Opt[Loc]` to the list instead. */
  case Annotated(pattern: Pattern, annotations: Vector[Opt[Loc] \/ Term])
  
  /** A pattern that comes with an extra condition. It works in a way similar to
   *  `and` in split. */
  case Guarded(pattern: Pattern, guard: Term)
  
  infix def binds(id: Ident): Pattern.Alias = Pattern.Alias(this, id)
  
  /** Annotate the pattern using the given term. If the term is `Error`, then
    * use the location of the original tree for error reporting. */
  def annotate(annotation: Term, treeLoc: Opt[Loc]): Pattern.Annotated =
    val elem = if annotation.isInstanceOf[Term.Error] then L(treeLoc) else R(annotation)
    this match
      case Annotated(pattern, annotations) =>
        Annotated(pattern, annotations :+ elem)
      case _ => Annotated(this, Vector.single(elem))
  
  inline def withGuard(guard: Term) = Pattern.Guarded(this, guard)
  
  /** Collect all variables in the pattern. Meanwhile, list invalid variables,
   *  which will be reported when constructing symbols for variables. We use a
   *  map because we want to replace variables. */
  lazy val variables: Variables = this match
    case Constructor(_, arguments) => arguments.fold(Variables.empty)(_.variables)
    case Composition(false, left, right) => left.variables ++ right.variables
    case union @ Composition(true, left, right) => left.variables.intersect(right.variables, union)
    // If we only allow negation patterns to be used as the top-level pattern
    // and the arguments represent the diagnostic information of match failure,
    // then we can bind the variables in the pattern to the arguments.
    // case Negation(Constructor(_, arguments)) => arguments.variables
    // Otherwise, negation patterns should not bind any variables.
    case negation @ Negation(pattern) => pattern.variables.invalidated(Negated(negation))
    case _: (Wildcard | Literal | Range | Transform) => Variables.empty
    case Concatenation(left, right) => left.variables ++ right.variables
    case Tuple(leading, spread) => leading.variables ++ spread.fold(Variables.empty):
      case (_, middle, trailing) => middle.variables ++ trailing.variables
    case Record(fields) => fields.iterator.map(_._2).variables
    case alias @ Alias(pattern, _) => pattern.variables + alias
    case Chain(first, second) => first.variables ++ second.variables
    case Annotated(pattern, _) => pattern.variables
    case Guarded(pattern, _) => pattern.variables
  
  /** Collect the names of pattern variables that are actually referenced
    * as free variables inside guard terms of `Guarded` patterns. Only
    * variables whose names appear free (not locally re-bound) in the guard
    * are included, so that truly unused pattern bindings (e.g.,
    * `[x] where true`) and shadowed bindings (e.g.,
    * `[x, y] where (let x = ..., x)`) still trigger warnings. */
  lazy val varNamesUsedInGuards: Set[Str] = this match
    case Guarded(pattern, guard) =>
      val boundNames = pattern.variables.varMap.keySet
      val referencedNames = guard.freeVars
      (boundNames & referencedNames) ++ pattern.varNamesUsedInGuards
    case _ =>
      children.iterator.collect:
        case p: Pattern => p.varNamesUsedInGuards
      .foldLeft(Set.empty[Str])(_ ++ _)
  
  def children: Vector[Located] = this match
    case Constructor(target, arguments) => target +: arguments.fold(Vector.empty)(_.toVector)
    case Composition(polarity, left, right) => Vector.double(left, right)
    case Negation(pattern) => Vector.single(pattern)
    case Wildcard() => Vector.empty
    case Literal(literal) => Vector.single(literal)
    case Range(lower, upper, rightInclusive) => Vector.double(lower, upper)
    case Concatenation(left, right) => Vector.double(left, right)
    case Tuple(leading, spread) => leading.toVector ++ spread.fold(Vector.empty):
      case (_, middle, trailing) => middle +: trailing.toVector
    case Record(fields) =>
      fields.iterator.flatMap:
        case (name, pattern) => name +: pattern.children
      .toVector
    case Chain(first, second) => Vector.double(first, second)
    case Alias(pattern, alias) => Vector.double(pattern, alias)
    case Transform(pattern, _, transform) => Vector.double(pattern, transform)
    case Annotated(pattern, annotations) => pattern +:
      annotations.iterator.collect { case R(term) => term }.toVector
    case Guarded(pattern, guard) => pattern.children :+ guard
  
  def subTerms: Vector[Term] = this match
    case Constructor(target, arguments) =>
      target +: Vector.concat(arguments.fold(Vector.empty)(_.iterator.flatMap(_.subTerms).toVector))
    case Composition(_, left, right) => left.subTerms ++ right.subTerms
    case Negation(pattern) => pattern.subTerms
    case _: (Wildcard | Literal | Range) => Vector.empty
    case Concatenation(left, right) => left.subTerms ++ right.subTerms
    case Tuple(leading, spread) => leading.iterator.flatMap(_.subTerms).toVector ++ spread.fold(Vector.empty):
      case (_, middle, trailing) => middle.subTerms ++ trailing.iterator.flatMap(_.subTerms).toVector
    case Record(fields) => fields.iterator.flatMap(_._2.subTerms).toVector
    case Chain(first, second) => first.subTerms ++ second.subTerms
    case Alias(pattern, _) => pattern.subTerms
    case Transform(pattern, _, transform) => pattern.subTerms :+ transform
    case Annotated(pattern, annotations) => pattern.subTerms ++
      annotations.iterator.collect { case R(term) => term }.toList
    case Guarded(pattern, guard) => pattern.subTerms :+ guard
  
  def describe: Str = this match
    case Constructor(_, _) => "constructor"
    case Composition(true, _, _) => "disjunction"
    case Composition(false, _, _) => "conjunction"
    case Negation(_) => "negation"
    case Wildcard() => "wildcard"
    case Literal(_) => "literal"
    case Range(_, _, _) => "range"
    case Concatenation(_, _) => "concatenation"
    case Tuple(_, _) => "tuple"
    case Record(_) => "record"
    case Chain(_, _) => "chain"
    case Alias(_, _) => "alias"
    case Transform(_, _, _) => "transform"
    case Annotated(_, _) => "annotated pattern"
    case Guarded(_, _) => "guarded pattern"
  
  private def showDbgWithPar(using DebugPrinter): Str =
    val addPar = this match
      case _: (Constructor | Wildcard | Literal | Tuple | Record | Negation | Annotated) => false
      case Alias(Wildcard(), _) => false
      case _: (Alias | Composition | Transform | Range | Concatenation | Chain | Guarded) => true
    if addPar then s"(${showDbg})" else showDbg
  
  def showDbg(using DebugPrinter): Str = this match
    case Constructor(target, arguments) =>
      target.symbol.fold(target.showDbg)(_.nme) + arguments.fold(""):
        args => s"(${args.map(_.showDbg).mkString(", ")})"
    case Composition(true, left, right) => s"${left.showDbg} ∨ ${right.showDbg}"
    case Composition(false, left, right) => s"${left.showDbg} ∧ ${right.showDbg}"
    case Negation(pattern) => s"¬${pattern.showDbgWithPar}"
    case Wildcard() => "_"
    case Literal(literal) => literal.idStr
    case Range(lower, upper, rightInclusive) =>
      s"${lower.idStr} ${if rightInclusive then "to" else "until"} ${upper.idStr}"
    case Concatenation(left, right) => s"${left.showDbg} ~ ${right.showDbg}"
    case Tuple(leading, spread) =>
      (leading.iterator.map(_.showDbg) ++ spread.fold(Iterator.empty):
        case (spreadKind, middle, trailing) =>
          Iterator.single(spreadKind.str + middle.showDbg) ++
            trailing.iterator.map(_.showDbg)).mkString("[", ", ", "]")
    case Record(fields) => s"{${fields.map((k, v) => s"${k.name}: ${v.showDbg}").mkString(", ")}}"
    case Chain(first, second) => s"${first.showDbgWithPar} as ${second.showDbgWithPar}"
    case Alias(Wildcard(), alias) => alias.name
    case Alias(pattern, alias) => s"${pattern.showDbgWithPar} as ${alias.name}"
    case Transform(pattern, _, transform) => s"${pattern.showDbgWithPar} => ${transform.showDbg}"
    case Annotated(pattern, annotations) => annotations.iterator.map:
        case L(errorLoc) => "error"
        case R(term) => term.showDbg
      .mkString("@", " @", " ") + pattern.showDbgWithPar
    case Guarded(pattern, guard) => pattern.showDbg + " where " + guard.showDbg
