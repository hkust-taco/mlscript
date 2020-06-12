package funtypes

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet}
import scala.collection.immutable.SortedSet

import funtypes.utils._, shorthands._


// Auxiliary definitions for types

abstract class TypeImpl { self: Type =>
  
  lazy val typeVarsList: List[TypeVar] = this match {
    case uv: TypeVar => uv :: Nil
    case Recursive(n, b) => n :: b.typeVarsList
    case _ => children.flatMap(_.typeVarsList)
  }
  
  def show: String = {
    val vars = typeVarsList.distinct
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


// Auxiliary definitions for terms

abstract class TermImpl { self: Term =>
  
  override def toString: String = this match {
    case Bra(true, trm) => s"{$trm}"
    case Bra(false, trm) => s"($trm)"
    case Blk(stmts) => stmts.map("" + _ + ";").mkString(" ")
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case Var(name) => name
    case Lam(name, rhs) => s"($name => $rhs)"
    case App(lhs, rhs) => s"($lhs $rhs)"
    case Rcd(fields) =>
      fields.iterator.map(nv => nv._1 + ": " + nv._2).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => receiver.toString + "." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"(let${if (isRec) " rec" else ""} $name = $rhs in $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) => n.fold("")(_ + ": ") + t + "," }.mkString("(", " ", ")")
  }
  
}

trait Located {
  def children: List[Located]
  
  private var spanStart: Int = -1
  private var spanEnd: Int = -1
  
  def withLoc(s: Int, e: Int): this.type = {
    assert(spanStart < 0)
    assert(spanEnd < 0)
    spanStart = s
    spanEnd = e
    this
  }
  def toLoc: Opt[Loc] = {
    def subLocs = children.iterator.flatMap(_.toLoc.iterator)
    if (spanStart < 0) spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    if (spanEnd < 0) spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    S(Loc(spanStart, spanEnd))
  }
}

trait StatementImpl extends Located {
  
  def children: List[Statement] = this match {
    case Var(name) => Nil
    case Lam(lhs, rhs) => lhs :: rhs :: Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case Tup(fields) => fields.map(_._2)
    case Rcd(fields) => fields.map(_._2)
    case Sel(receiver, fieldName) => receiver :: Nil
    case Let(isRec, name, rhs, body) => rhs :: body :: Nil
    case Blk(stmts) => stmts
    case IntLit(_) | DecLit(_) | StrLit(_) => Nil
  }
  
  override def toString: String = this match {
    case LetS(isRec, name, rhs) => s"let${if (isRec) " rec" else ""} $name = $rhs"
    case _: Term => super.toString
  }
}

trait BlkImpl { self: Blk =>
  
  def flatten: Blk = Blk(stmts.flatMap {
    case b: Blk => b.flatten.stmts
    case t => t :: Nil
  })
  
}
