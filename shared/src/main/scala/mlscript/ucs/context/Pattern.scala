package mlscript.ucs.context

import collection.mutable.{Buffer, SortedMap => MutSortedMap}
import mlscript.{Lit, Loc, Located, SimpleTerm, TypeName, Var}
import mlscript.pretyper.symbol.TypeSymbol
import mlscript.utils._, shorthands._
import mlscript.pretyper.symbol.DummyClassSymbol

sealed abstract class Pattern {
  private val locationsBuffer: Buffer[Loc] = Buffer.empty

  def addLocation(located: Located): Unit = located.getLoc.foreach(locationsBuffer += _)

  def addLocation(location: Opt[Loc]): Unit = locationsBuffer ++= location

  /** Get the location of this pattern's first occurrence. */
  def firstOccurrence: Option[Loc] = locationsBuffer.headOption

  def locations: Ls[Loc] = locationsBuffer.toList

  def arity: Opt[Int]

  def showDbg: Str

  /** Get a string suitable for diagnostics. */
  def showInDiagnostics: Str

  /**
    * Checks if the pattern is same as expressed by the given `SimpleTerm`. Note
    * that we should pass `pat` of `Case` to this function.
    */
  def matches(pat: SimpleTerm): Bool

  /** Create a `SimpleTerm` which can be used as `pat` of `Case`. */
  def toCasePattern: SimpleTerm
}

object Pattern {
  final case class ClassLike(val classLikeSymbol: TypeSymbol, scrutinee: Scrutinee) extends Pattern {
    private var unappliedVarOpt: Opt[Var] = N
    private val parameters: MutSortedMap[Int, Scrutinee] = MutSortedMap.empty

    private[context] def findSubScrutinee(scrutinee: Scrutinee): Opt[Int] =
      parameters.find(_._2 === scrutinee).map(_._1)

    /**
      * Get or create a sub-scrutinee for the given parameter index.
      *
      * @param index the index of the parameter.
      * @return a `ScrutineeData` for the parameter whose parent scrutinee is the
      *         current scrutinee
      */
    def getParameter(index: Int): Scrutinee = {
      require(index >= 0)
      parameters.getOrElseUpdate(index, scrutinee.freshSubScrutinee)
    }

    def getUnappliedVar(default: => Var): Var =
      unappliedVarOpt.getOrElse {
        val unappliedVar = default
        unappliedVarOpt = S(unappliedVar)
        unappliedVar
      }

    override def arity: Opt[Int] = parameters.keysIterator.maxOption.map(_ + 1)

    override def showDbg: Str = s"${classLikeSymbol.name}"

    override def showInDiagnostics: Str = s"${(classLikeSymbol match {
      case dummySymbol: DummyClassSymbol => "class"
      case otherSymbol: TypeSymbol => otherSymbol.defn.kind.str
    })} `${classLikeSymbol.name}`"

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case pat: Var => pat.symbolOption match {
          case S(patternSymbol: TypeSymbol) =>
            patternSymbol === classLikeSymbol || patternSymbol.hasBaseClass(classLikeSymbol)
          case S(_) | N => false
        }
        case _: Lit => false
      }

    override def toCasePattern: SimpleTerm =
      Var(classLikeSymbol.name).withLoc(firstOccurrence).withSymbol(classLikeSymbol)
  }

  final case class Tuple(scrutinee: Scrutinee) extends Pattern {
    private val fields: MutSortedMap[Int, Scrutinee] = MutSortedMap.empty

    def getField(index: Int): Scrutinee =
      fields.getOrElseUpdate(index, scrutinee.freshSubScrutinee)

    override def arity: Opt[Int] = fields.keysIterator.maxOption.map(_ + 1)

    override def showDbg: Str = s"tuple#${arity.getOrElse("?")}"

    override def showInDiagnostics: Str =
      "tuple of " + (arity match {
        case N => "certain number of elements"
        case S(1) => "1 element"
        case S(n) => s"${n} elements"
      })

    override def matches(pat: SimpleTerm): Bool = false

    /**
      * Note that currently we only support simple tuple patterns. They should
      * disappear after desugaring stage, therefore, it will be an error if you
      * find an instance of this class.
      */
    override def toCasePattern: SimpleTerm = ???
  }

  final case class Literal(val literal: Lit) extends Pattern {
    override def arity: Opt[Int] = N

    override def showDbg: Str = literal.idStr

    override def showInDiagnostics: Str = s"literal ${literal.idStr}"

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case _: Var => false
        case pat => pat === literal
      }

    override def toCasePattern: SimpleTerm = literal.withLoc(firstOccurrence)
  }

  /**
    * This can be actually merged with `Pattern.Literal`. However, there's no
    * `Lit` sub-classes for Boolean types, so the representation is a little bit
    * awkward, also, it makes sense to consider Boolean patterns separately
    * because we can check the Boolean exhaustiveness with them.
    */
  final case class Boolean(val value: Var) extends Pattern {
    require(value.name === "true" || value.name === "false")

    override def arity: Opt[Int] = N

    override def showDbg: Str = value.name

    override def showInDiagnostics: Str = s"Boolean value ${value.name}"

    override def matches(pat: SimpleTerm): Bool =
      pat match {
        case Var(name) => value.name === name
        case _ => false
      }

    override def toCasePattern: SimpleTerm = value.withLoc(firstOccurrence)
  }
}
