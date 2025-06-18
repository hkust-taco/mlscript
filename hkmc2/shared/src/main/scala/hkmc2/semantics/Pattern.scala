package hkmc2
package semantics

import mlscript.utils.*, shorthands.*, collection.immutable.HashMap
import syntax.Tree, Tree.Ident, Elaborator.State, Message.MessageContext, ucs.error
import scala.annotation.tailrec, util.chaining.*

object Pattern:
  /** The reason why a variable obtained from `Pattern.variables` is invalid. */
  enum InvalidReason:
    /** The variable shadowed another variable. */
    case Duplicated(previous: Ident)
    /** The variable presents in one side of disjunction, but not the other. */
    case Inconsistent(disjunction: Pattern.Composition, missingOnTheLeft: Bool)
    /** The variable is bound in a `Negation` pattern. */
    case Negated(negation: Pattern.Negation)
  
  
  import InvalidReason.*
  
  /** A set of variables that present in a pattern.
   *  
   *  These variables are represented by `Tree.Ident` because not every identifier
   *  can represent a meaningful binding. This set is used in the computed property
   *  on the `Pattern` tree. We only create `VarSymbol` for these variables at the
   *  root node or when elaborating the term of a `Transform` pattern.
   * 
   *  @param varMap A map from variable names to their latest aliases.
   *  @param invalidVars A list of variables and the reason why they are invalid.
   */
  final case class Variables(
      varMap: HashMap[Str, Pattern.Alias],
      invalidVars: Ls[(Pattern.Alias, InvalidReason)]
  ):
    /** Apply a function to all variables. */
    def map[A](f: Pattern.Alias => A): Iterator[A] = varMap.iterator.map(_._2).map(f)
    
    /** Add a single variable to the variable set. */
    def +(alias: Pattern.Alias): Variables =
      varMap.get(alias.id.name) match
        case N => Variables(varMap + (alias.id.name -> alias), invalidVars)
        case S(oldVar) => Variables(
          varMap.updated(alias.id.name, alias),
          invalidVars :+ (oldVar, Duplicated(alias.id)))
    
    /** Union two variable sets. If the latter contains a variable that is
     *  already present in the former, the variable is considered duplicated. */
    def ++(that: Variables): Variables = Variables(
      varMap.merged(that.varMap):
        case ((name, _), (_, id)) => (name, id),
      invalidVars ::: that.invalidVars ::: that.varMap.iterator.collect:
        case (name, id) if varMap.contains(name) =>
          (id, Duplicated(varMap(name).id))
      .toList)
    
    /** Intersect two variable sets and move variables that are only present in
     *  one side to the invalid variables. This method considers `this` as the
     *  left side, and `that` as the right side. */
    def intersect(that: Variables, pattern: Pattern.Composition): Variables =
      // Check if two variable sets are the same.
      val notInThat = varMap.removedAll(that.varMap.keys)
      val notInThis = that.varMap.removedAll(varMap.keys)
      Variables(
        // Remove variables that only present in one side.
        varMap.removedAll(Iterable.concat(notInThat.keys, notInThis.keys)),
        // Add variables that only present in one side to the invalid variables.
        invalidVars :::
          notInThis.iterator.map(_._2 -> Inconsistent(pattern, true)).toList :::
          notInThat.iterator.map(_._2 -> Inconsistent(pattern, false)).toList)
    
    /** Mark all variables in this set as invalid. */
    def invalidated(reason: InvalidReason): Variables =
      Variables(HashMap.empty, invalidVars appendedAll varMap.iterator.map(_._2 -> reason))
    
    /** Report all invalid variables. */
    def report(using Raise): Unit = invalidVars.foreach:
      case (Alias(_, id), Duplicated(previous)) => error(
        msg"Duplicate pattern variable." -> id.toLoc,
        msg"The previous definition is here." -> previous.toLoc)
      case (Alias(_, id), Inconsistent(disjunction, missingOnTheLeft)) => error(
        msg"Found an inconsistent variable in disjunction patterns." -> id.toLoc,
        msg"The variable is missing from this sub-pattern." -> (
          if missingOnTheLeft then disjunction.left else disjunction.right
        ).toLoc)
      case (Alias(pattern, id), Negated(negation)) => error(pattern match
        case Wildcard() => msg"This variable cannot be accessed." -> id.toLoc
        case _: Pattern => msg"This pattern cannot be bound." -> pattern.toLoc,
        msg"Because the pattern it belongs to is negated." -> negation.toLoc)
    
  object Variables:
    lazy val empty: Variables = Variables(HashMap.empty, Nil)
  
  extension (patterns: IterableOnce[Pattern])
    def variables: Variables = patterns.iterator.foldLeft(Variables.empty):
      case (vars, pattern) => vars ++ pattern.variables
  
  /** A shorthand for creating a variable pattern. */
  def Variable(id: Ident): Pattern.Alias = Pattern.Wildcard().bind(id)
  
  trait ConstructorImpl:
    self: Pattern.Constructor =>
    
    /** Get the resolved symbol of the target term. */
    def symbol: Opt[Symbol] = self.target.resolvedSymbol
    
    /** Expect the `symbol` to be set. */
    def symbol_! : Symbol = symbol.getOrElse(lastWords("symbol is not set"))
  
  /** Add a mutable field to the `Alias` pattern to store the symbol for the
   *  variable. Note that NOT every `Alias` pattern has a symbol. */
  trait AliasImpl:
    self: Pattern.Alias =>
    private var _symbol: Opt[VarSymbol] = N
    /** Directly set the symbol for the variable. This should be called in the
     *  elaborator when elaborating the non-`Transform` top-level pattern. */
    def symbol_=(symbol: VarSymbol): Unit = _symbol = S(symbol)
    def symbol: VarSymbol = _symbol.getOrElse(lastWords("symbol is not set"))
    /** Allocate the symbol for the variable. This should be called in the
     *  elaborator and before elaborating the term from `Transform`. */
    def allocate(using State): VarSymbol = VarSymbol(self.id).tap(symbol_=)

import Pattern.*, InvalidReason.*

/** An inductive data type for patterns. */
enum Pattern extends AutoLocated:
  /** A pattern that matches a constructor and its arguments. */
  case Constructor(target: Term, arguments: Ls[Pattern])
  
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
   *  When the `spread` pattern is absent, sub-patterns should be placed in the 
   *  `leading` field. */
  case Tuple(leading: Ls[Pattern], spread: Opt[Pattern], trailing: Ls[Pattern])
  
  /** A pattern that matches a record consisting of a list of fields. Note that
   *  the fields are not ordered semantically. */
  case Record(fields: Ls[(Ident, Pattern)])
  
  /** A pattern that matches the same value as another pattern, but bind the
   *  matched value to a new variable. This is the only class that holds the
   *  symbol for the variable. */
  case Alias(pattern: Pattern, id: Ident) extends Pattern with AliasImpl
  
  /** A pattern that matches the same value as other pattern, with an additional
   *  function applied to the bound variables in the pattern.
   */
  case Transform(pattern: Pattern, transform: Term)
  
  infix def bind(id: Ident): Pattern.Alias = Pattern.Alias(this, id)
  
  /** Collect all variables in the pattern. Meanwhile, list invalid variables,
   *  which will be reported when constructing symbols for variables. We use a
   *  map becuase we want to replace variables. */
  lazy val variables: Variables = this match
    case Constructor(_, arguments) => arguments.variables
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
    case Tuple(leading, spread, trailing) =>
      leading.variables ++ spread.map(_.variables).getOrElse(Variables.empty) ++ trailing.variables
    case Record(fields) => fields.iterator.map(_._2).variables
    case alias @ Alias(pattern, _) => pattern.variables + alias
  
  def children: Ls[Located] = this match
    case Constructor(target, arguments) => target :: arguments
    case Composition(polarity, left, right) => left :: right :: Nil
    case Negation(pattern) => pattern :: Nil
    case Wildcard() => Nil
    case Literal(literal) => Nil
    case Range(lower, upper, rightInclusive) => lower :: upper :: Nil
    case Concatenation(left, right) => left :: right :: Nil
    case Tuple(leading, spread, trailing) => leading ::: spread.toList ::: trailing
    case Record(fields) => fields.flatMap:
      case (name, pattern) => name :: pattern.children
    case Alias(pattern, alias) => pattern :: alias :: Nil
    case Transform(pattern, transform) => pattern :: transform :: Nil
  
  def subTerms: Ls[Term] = this match
    case Constructor(target, arguments) => target :: arguments.flatMap(_.subTerms)
    case Composition(_, left, right) => left.subTerms ::: right.subTerms
    case Negation(pattern) => pattern.subTerms
    case _: (Wildcard | Literal | Range) => Nil
    case Concatenation(left, right) => left.subTerms ::: right.subTerms
    case Tuple(leading, spread, trailing) => leading.flatMap(_.subTerms) :::
      spread.fold(Nil)(_.subTerms) ::: trailing.flatMap(_.subTerms)
    case Record(fields) => fields.flatMap(_._2.subTerms)
    case Alias(pattern, _) => pattern.subTerms
    case Transform(pattern, transform) => pattern.subTerms :+ transform
  
  private def showDbgWithPar =
    val addPar = this match
      case _: (Constructor | Wildcard | Literal | Tuple | Record | Negation) => false
      case Alias(Wildcard(), _) => false
      case _: (Alias | Composition | Transform | Range | Concatenation) => true
    if addPar then s"(${showDbg})" else showDbg
  
  def showDbg: Str = this match
    case Constructor(target, arguments) =>
      val targetText = target.symbol.fold(target.showDbg)(_.toString())
      s"$targetText(${arguments.map(_.showDbg).mkString(", ")})"
    case Composition(true, left, right) => s"${left.showDbg} \u2228 ${right.showDbg}"
    case Composition(false, left, right) => s"${left.showDbg} \u2227 ${right.showDbg}"
    case Negation(pattern) => s"\u00ac${pattern.showDbgWithPar}"
    case Wildcard() => "_"
    case Literal(literal) => literal.idStr
    case Range(lower, upper, rightInclusive) =>
      s"${lower.idStr} ${if rightInclusive then "to" else "until"} ${upper.idStr}"
    case Concatenation(left, right) => s"${left.showDbg} ~ ${right.showDbg}"
    case Tuple(leading, spread, trailing) =>
      (leading.iterator.map(_.showDbg) ++
        spread.iterator.map(s => "..." + s.showDbg) ++
        trailing.iterator.map(_.showDbg)).mkString("[", ", ", "]")
    case Record(fields) => s"{${fields.map((k, v) => s"${k.name}: ${v.showDbg}").mkString(", ")}}"
    case Alias(Wildcard(), alias) => alias.name
    case Alias(pattern, alias) => s"${pattern.showDbgWithPar} as ${alias.name}"
    case Transform(pattern, transform) => s"${pattern.showDbgWithPar} => ${transform.showDbg}"
