package simplesub

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet}
import scala.collection.immutable.SortedSet


// Helper methods for types

abstract class TypeImpl { self: Type =>
  
  lazy val typeVars: Set[TypeVar] = this match {
    case uv: TypeVar => Set(uv)
    case Recursive(n, b) => b.typeVars + n
    case _ => children.iterator.flatMap(_.typeVars).toSet
  }
  
  def show: String = {
    val vars = typeVars
    val ctx = vars.zipWithIndex.map {
      case (tv, idx) =>
        def nme = {
          assert(idx <= 'z' - 'a', "TODO handle case of not enough chars")
          ('a' + idx).toChar.toString
        }
        tv -> ("'" + nme)
    }.toMap
    showIn(ctx, 0)
  }
  
  private def parensIf(str: String, cnd: Boolean): String = if (cnd) "(" + str + ")" else str
  def showIn(ctx: Map[TypeVar, String], outerPrec: Int): String = this match {
    case Top => "⊤"
    case Bot => "⊥"
    case Primitive(name) => name
    case uv: TypeVar => ctx(uv)
    case Recursive(n, b) => s"${b.showIn(ctx, 31)} as ${ctx(n)}"
    case Function(l, r) => parensIf(l.showIn(ctx, 11) + " -> " + r.showIn(ctx, 10), outerPrec > 10)
    case Record(fs) => fs.map(nt => s"${nt._1}: ${nt._2.showIn(ctx, 0)}").mkString("{", ", ", "}")
    case Union(l, r) => parensIf(l.showIn(ctx, 20) + " ∨ " + r.showIn(ctx, 20), outerPrec > 20)
    case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " ∧ " + r.showIn(ctx, 25), outerPrec > 25)
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Record(fs) => fs.map(_._2)
    case Union(l, r) => l :: r :: Nil
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
  }
  
}
