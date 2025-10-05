package hkmc2
package semantics
package ups

import mlscript.utils.*, shorthands.*
import Elaborator.{Ctx, State, ctx}
import Message.MessageContext, ucs.{error, warn}
import semantics.Pattern as SP, Pattern.*
import syntax.Tree, Tree.{StrLit, Ident, IntLit}
import collection.mutable.{Map as MutMap, Queue as MutQueue}
import utils.TL
import scala.collection.immutable.SeqMap

object Instantiator:
  type Subst = Map[VarSymbol, Pat]

class Instantiator(using tl: TL)(using Ctx, State, Raise):
  import tl.*
  
  /** The map contains all instantiated patterns. The key is a pattern symbol
   *  paired with fully instantiated patterns as arguments. The value is the
   *  pattern symbol's definition with all parameters have been substituted.
   *  If the value is `None`, the pattern has not been instantiated yet. */
  val progress: MutMap[Instantiation, Opt[Pat]] = MutMap.empty
  
  /** We instantiate patterns in a breadth-first manner. The queue contains all
   *  patterns that need to be instantiated. */
  val thingsToDo: MutQueue[Instantiation] = MutQueue.empty
  
  /** Instantiate a pattern and patterns used in it. */
  def apply(
    symbol: PatternSymbol,
    arguments: Ls[SP],
    useSiteLoc: Opt[Loc]
  ): (Pat, Context) = scoped("ucs:instantiation"):
    val entryPoint = Instantiation(symbol, arguments.map(instantiate(_)(using Map.empty)))(useSiteLoc)
    val result = schedule(entryPoint)
    while thingsToDo.nonEmpty do
      val instantiation = thingsToDo.dequeue()
      val defn = instantiation.symbol.defn.get
      // Check if the number of pattern parameters and pattern arguments match.
      if defn.patternParams.size != instantiation.arguments.size then
        val parameterCount = "pattern parameter" countBy defn.patternParams.size
        val argumentCount = "pattern argument" countBy instantiation.arguments.size
        error(msg"Pattern `${instantiation.symbol.nme}` has $parameterCount." -> Loc(defn.patternParams),
          msg"But $argumentCount were provided." -> instantiation.toLoc)
        // The entire pattern will not be instantiated. Use never instead.
        progress += (instantiation -> S(Pattern.Never))
      else
        val subst = defn.patternParams.iterator.map(_.sym).zip(instantiation.arguments).toMap
        log("Instantiating " + instantiation.showDbg)
        val instantiated = instantiate(defn.pattern)(using subst)
        log(s"Instantiated ${instantiation.showDbg}\n" +
          s"arity = ${instantiation.symbol.defn.get.patternParams.size}\n" +
          s"arguments = ${instantiation.arguments.iterator.map(_.showDbg).mkString(", ")}\n" +
          s"instantiated = ${instantiated.showDbg}")
        // Add the instantiated pattern to the progress map.
        progress += (instantiation -> S(instantiated))
    // Finally, return the synonym representing the entry point pattern and all
    // instantiated pattern definitions.
    val definitions = progress.view.mapValues:
      _.getOrElse(lastWords("The pattern is expected to be instantiated."))
    .toMap
    (Synonym(result), Context(definitions))
  
  /** Add the instantiation to the queue if it has not been instantiated yet. */
  def schedule(instantiation: Instantiation): Instantiation =
    if !progress.contains(instantiation) then
      progress += (instantiation -> N)
      thingsToDo.enqueue(instantiation)
    else
      log(s"Already instantiated ${instantiation.showDbg}")
    progress(instantiation) 
    instantiation
  
  /** Instantiate the given pattern with a substitution map. */
  def instantiate(pattern: SP)(using subst: Map[VarSymbol, Pat]): Pat = pattern match
    case SP.Constructor(target, patternArguments, arguments) => target.symbol match
      // Look up the corresponding pattern from the substitution.
      case S(symbol: VarSymbol) => subst(symbol)
      // Recursively instantiate the arguments of constructor patterns.
      case S(symbol) => symbol.asClsLike match
        case S(symbol: ClassSymbol) =>
          val keyedArguments = symbol.defn.get.paramsOpt match
            case S(ParamList(_, params, _)) => arguments match
              case S(arguments) =>
                if params.size != arguments.size then
                  error(msg"Class `${symbol.nme}` has ${params.size} parameters." -> Loc(params),
                    msg"But ${arguments.size} arguments were provided." -> Loc(arguments))
                S(params.iterator.zip(arguments).flatMap:
                  case (param, argument) if param.flags.isVal =>
                    // The names are not from the source and are retrieved from
                    // parameters in class definitions. Therefore, no `Loc`
                    // should be attached.
                    S(new Ident(param.sym.id.name) -> instantiate(argument))
                  case (param, argument) =>
                    error(msg"Parameter `${param.sym.nme}` is not accessible." -> param.toLoc)
                    N
                .to(SeqMap))
              case N => N // The class has parameters but no arguments are provided.
            case N => arguments match
              case N => N // No arguments are provided.
              case S(arguments) =>
                error(msg"Class `${symbol.nme}` has no parameters." -> Loc(arguments))
                N
          ClassLike(symbol, keyedArguments)
        case S(symbol: ModuleOrObjectSymbol) =>
          arguments match
            case N => ClassLike(symbol, N)
            case S(arguments) => error(
              msg"`${symbol.nme}` is a module, thus it cannot have arguments." -> Loc(arguments))
          ClassLike(symbol, N)
        case S(symbol: PatternSymbol) =>
          val arguments = patternArguments.map(instantiate(_))
          val instantiation = Instantiation(symbol, arguments)(pattern.toLoc)
          Synonym(schedule(instantiation))
    case SP.Composition(true, left, right) => instantiate(left) or instantiate(right)
    case SP.Composition(false, left, right) => instantiate(left) and instantiate(right)
    case SP.Negation(pattern) => Not(instantiate(pattern))
    case SP.Wildcard() => Wildcard
    case SP.Literal(literal) => Literal(literal)
    case SP.Range(lower, upper, rightInclusive) =>
      // Currently, we expand the range pattern into a list of literals. After
      // the `where` clause or chain patterns are implemented, we could directly
      // expand the range pattern into a range test.
      (lower, upper) match
        case (StrLit(lower), StrLit(upper)) =>
          Or((lower.head to upper.head).map(c => Literal(StrLit(c.toString))).toList)
        case (IntLit(lower), IntLit(upper)) =>
          Or((lower to upper).map(i => Literal(IntLit(i))).toList)
        case _ =>
          error(msg"Range patterns are not supported in pattern compilation." -> pattern.toLoc)
          Never
    case SP.Concatenation(left, right) =>
      error(msg"String concatenation is not supported in pattern compilation." -> pattern.toLoc)
      Never
    case SP.Tuple(leading, spread, trailing) => Tuple(leading.map(instantiate(_)), spread.map(instantiate(_)), trailing.map(instantiate(_)))
    case SP.Record(fields) => Record(fields.iterator.map((id, pattern) => (id, instantiate(pattern))).to(SeqMap))
    case SP.Chain(first, second) =>
      error(msg"Pattern chaining is not supported in pattern compilation." -> pattern.toLoc)
      Never
    case alias @ SP.Alias(pattern, id) => alias.symbolOption match
      case N => instantiate(pattern)
      case S(symbol) => Rename(instantiate(pattern), symbol)
    // Pattern arguments are accessible throughout the pattern.
    case SP.Transform(pattern, transform) => Extract(instantiate(pattern), transform)
