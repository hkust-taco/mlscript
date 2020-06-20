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
  
  def show: String =
    showIn(ShowCtx.mk(this :: Nil), 0)
  
  private def parensIf(str: String, cnd: Boolean): String = if (cnd) "(" + str + ")" else str
  def showIn(ctx: ShowCtx, outerPrec: Int): String = this match {
    case Top => "anything"
    case Bot => "nothing"
    case Primitive(name) => name
    // case uv: TypeVar => ctx.vs.getOrElse(uv, s"[??? $uv ???]")
    // case Recursive(n, b) => s"${b.showIn(ctx, 31)} as ${ctx.vs.getOrElse(n, s"[??? $n ???]")}"
    case uv: TypeVar => ctx.vs(uv)
    case Recursive(n, b) => s"${b.showIn(ctx, 31)} as ${ctx.vs(n)}"
    case Function(l, r) => parensIf(l.showIn(ctx, 11) + " -> " + r.showIn(ctx, 10), outerPrec > 10)
    case Record(fs) => fs.map(nt => s"${nt._1}: ${nt._2.showIn(ctx, 0)}").mkString("{", ", ", "}")
    case Tuple(fs) => fs.map(nt => s"${nt._1.fold("")(_ + ": ")}${nt._2.showIn(ctx, 0)},").mkString("(", " ", ")")
    case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Record(fs) => fs.map(_._2)
    case Tuple(fs) => fs.map(_._2)
    case Union(l, r) => l :: r :: Nil
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
  }
  
}

final case class ShowCtx(vs: Map[TypeVar, Str], debug: Bool) // TODO make use of `debug` or rm
object ShowCtx {
  def mk(tys: IterableOnce[Type], pre: Str = "'", debug: Bool = false): ShowCtx = {
     val allVars = tys.iterator.toList.flatMap(_.typeVarsList).distinct
     ShowCtx(allVars.zipWithIndex.map {
        case (tv, idx) =>
          def nme = {
            assert(idx <= 'z' - 'a', "TODO handle case of not enough chars")
            ('a' + idx).toChar.toString
          }
          tv -> (pre + nme)
      }.toMap, debug)
  }
}

// Auxiliary definitions for terms

abstract class TermImpl { self: Term =>
  
  def describe: Str = this match {
    case Bra(_, trm) => trm.describe
    case Blk((trm: Term) :: Nil) => trm.describe
    case Blk(_) => "block of statements"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case Var(name) => "variable reference"
    case Lam(name, rhs) => "lambda expression"
    case App(App(op, lhs), rhs)
      if op.toLoc.exists(l => lhs.toLoc.exists(l.spanStart > _.spanStart))
      => "operator application"
    case App(op, lhs)
      if op.toLoc.exists(l => lhs.toLoc.exists(l.spanStart > _.spanStart))
      => "operator application"
    case App(lhs, rhs) => "application"
    case Rcd(fields) => "record"
    case Sel(receiver, fieldName) => "field selection"
    case Let(isRec, name, rhs, body) => "let binding"
    case Tup(xs) => "tuple expression"
  }
  
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
      s"(let${if (isRec) " rec" else ""} $name = $rhs; $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) => n.fold("")(_ + ": ") + t + "," }.mkString("(", " ", ")")
  }
  
}

trait Located {
  def children: List[Located]
  
  private var spanStart: Int = -1
  private var spanEnd: Int = -1
  private var origin: Opt[Origin] = N
  
  // TODO just store the Loc directly...
  def withLoc(s: Int, e: Int, ori: Origin): this.type = {
    assert(origin.isEmpty)
    origin = S(ori)
    assert(spanStart < 0)
    assert(spanEnd < 0)
    spanStart = s
    spanEnd = e
    this
  }
  def withLocOf(that: Located): this.type = {
    spanStart = that.spanStart
    spanEnd = that.spanEnd
    origin = that.origin
    this
  }
  lazy val toLoc: Opt[Loc] = getLoc
  private def getLoc: Opt[Loc] = {
    def subLocs = children.iterator.flatMap(_.toLoc.iterator)
    if (spanStart < 0) spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    if (spanEnd < 0) spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    val origins = origin.fold(subLocs.map(_.origin).toList.distinct)(_ :: Nil)
    assert(origins.size === 1)
    S(Loc(spanStart, spanEnd, origins.head))
  }
  /** Like toLoc, but we make sure the span includes the spans of all subterms. */
  def toCoveringLoc: Opt[Loc] = {
    // TODO factor logic with above
    def subLocs = (this :: children).iterator.flatMap(_.toLoc.iterator)
    val spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    val spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    val origins = origin.fold(subLocs.map(_.origin).toList.distinct)(_ :: Nil)
    assert(origins.size === 1)
    S(Loc(spanStart, spanEnd, origins.head))
  }
}

trait StatementImpl extends Located { self: Statement =>
  
  lazy val freeVars: Set[String] = this match {
    case _: Lit => Set.empty
    case Var(name) => Set.empty[String] + name
    case Lam(pat, rhs) => rhs.freeVars -- pat.freeVars
    case App(lhs, rhs) => lhs.freeVars ++ rhs.freeVars
    case Rcd(fields) => fields.iterator.flatMap(_._2.freeVars).toSet
    case Sel(receiver, fieldName) => receiver.freeVars
    case Let(isRec, name, rhs, body) =>
      (body.freeVars - name) ++ (if (isRec) rhs.freeVars - name else rhs.freeVars)
    case Bra(_, trm) => trm.freeVars
    case Blk(sts) => sts.iterator.flatMap(_.freeVars).toSet
    case Tup(trms) => trms.iterator.flatMap(_._2.freeVars).toSet
    case LetS(false, pat, rhs) => rhs.freeVars
    case LetS(true, pat, rhs) => rhs.freeVars -- pat.freeVars
  }
  
  def children: List[Statement] = this match {
    case Bra(_, trm) => trm :: Nil
    case Var(name) => Nil
    case Lam(lhs, rhs) => lhs :: rhs :: Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case Tup(fields) => fields.map(_._2)
    case Rcd(fields) => fields.map(_._2)
    case Sel(receiver, fieldName) => receiver :: Nil
    case Let(isRec, name, rhs, body) => rhs :: body :: Nil
    case Blk(stmts) => stmts
    case LetS(_, pat, rhs) => pat :: rhs :: Nil
    case _: Lit => Nil
  }
  
  def size: Int = children.iterator.map(_.size).sum + 1
  
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
