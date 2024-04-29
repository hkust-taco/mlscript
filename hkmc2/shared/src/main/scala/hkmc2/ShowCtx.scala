package hkmc2

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.immutable.SortedMap

import math.Ordered.orderingToOrdered

import mlscript.utils._, shorthands._


final case class ShowCtx(
    vs: SortedMap[TypeVar, Str],
    indentLevel: Int,
    angletards: Bool = false,
  )
:
  lazy val indStr: Str = ShowCtx.indentation * indentLevel
  def lnIndStr: Str = "\n" + indStr
  def indent: ShowCtx = copy(indentLevel = indentLevel + 1)
  def < : Str = if angletards then "<" else "["
  def > : Str = if angletards then ">" else "]"
object ShowCtx:
  val ExtrusionPrefix: Str = "??"
  
  def indentation: Str = "  "
  /**
    * Create a context from a list of types. For named variables and
    * hinted variables use what is given. For unnamed variables generate
    * completely new names. If same name exists increment counter suffix
    * in the name.
    */
  def mk(tys: IterableOnce[TypeLike], _pre: Str = "'"): ShowCtx =
    val (otherVars, namedVars) = tys.iterator.toList.flatMap(_.typeVarsList).distinct.partitionMap { tv =>
      tv.identifier match { case L(_) => L(tv.nameHint -> tv); case R(nh) => R(nh -> tv) }
    }
    val (hintedVars, unnamedVars) = otherVars.partitionMap:
      case (S(nh), tv) => L(nh -> tv)
      case (N, tv) => R(tv)
    val usedNames = MutMap.empty[Str, Int]
    def assignName(n: Str): Str =
      val pre = if n.startsWith("'") || n.startsWith(ExtrusionPrefix) then "" else _pre
      usedNames.get(n) match
        case S(cnt) =>
          usedNames(n) = cnt + 1
          pre + 
          n + cnt
        case N =>
          usedNames(n) = 0
          pre + 
          n
    val namedMap = (namedVars ++ hintedVars).map { case (nh, tv) =>
      // tv -> assignName(nh.dropWhile(_ === '\''))
      tv -> assignName(nh.stripPrefix(_pre))
    }.toSortedMap
    val used = usedNames.keySet
    
    // * Generate names for unnamed variables
    val numLetters = 'z' - 'a' + 1
    val names = Iterator.unfold(0) { idx =>
      val postfix = idx/numLetters
      S(('a' + idx % numLetters).toChar.toString + (if postfix === 0 then "" else postfix.toString), idx + 1)
    }.filterNot(used).map(assignName)
    
    ShowCtx(namedMap ++ unnamedVars.zip(names), indentLevel = 0)


