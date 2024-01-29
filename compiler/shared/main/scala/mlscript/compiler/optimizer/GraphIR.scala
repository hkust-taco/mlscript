package mlscript.compiler.optimizer

import mlscript.utils.*
import mlscript.utils.shorthands.*

import collection.mutable.{Map as MutMap, Set as MutSet, HashMap, ListBuffer}
import mlscript.*
import mlscript.compiler.optimizer.*

import annotation.unused
import util.Sorting

// -----------------------------------------------

case class GOProgram(
  val classes: Set[ClassInfo],
  val defs: Set[GODef],
  // TODO add a cache of split defs
  val main: GONode,
):
  override def equals(o: Any): Bool = o match {
    case o: GOProgram if this.isInstanceOf[GOProgram] =>
      o.classes == classes &&
      o.defs == defs &&
      o.main == main
    case _ => false
  }
  override def toString: String =
    val t1 = classes.toArray
    val t2 = defs.toArray
    Sorting.quickSort(t1)
    Sorting.quickSort(t2)
    s"GOProgram({${t1.mkString(",")}}, {\n${t2.mkString("\n")}\n},\n$main)"
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

implicit object ClassInfoOrdering extends Ordering[ClassInfo] {
  def compare(a: ClassInfo, b: ClassInfo) = a.id.compare(b.id)
}
implicit object GODefOrdering extends Ordering[GODef] {
  def compare(a: GODef, b: GODef) = a.id.compare(b.id)
}

case class ClassInfo(
  val id: Int,
  val ident: Str,
  val fields: Ls[Str],
):
  override def equals(o: Any): Bool = o match {
    case o: ClassInfo if this.isInstanceOf[ClassInfo] => o.id == id
    case _ => false
  }
  override def hashCode: Int = id
  override def toString: String =
    s"ClassInfo($id, $ident, [${fields mkString ","}])"
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

case class Name(val str: Str):
  override def equals(o: Any): Bool = o match {
    case Name(s2) => str == s2
    case _ => false
  }

  private var intro: Opt[Intro] = None
  private var elim: Set[Elim] = Set.empty

  def copy: Name = Name(str)
  def trySubst(map: Map[Str, Name]) = map.getOrElse(str, this)
  
  private def show_intro = intro match
    case Some(i) => "+" + i.toShortString
    case None => ""

  private def show_elim = elim match
    case e if e.isEmpty => ""
    case e => "-" + e.toSeq.sorted.map(_.toShortString).mkString

  private def toStringDbg = 
    val x = s"$show_intro$show_elim"
    if x != "" then s"$str[$x]" else str
  
  override def toString: String =
    str

  def accept_def_visitor(v: GONameVisitor) = v.visit_name_def(this)
  def accept_use_visitor(v: GONameVisitor) = v.visit_name_use(this)
  def accept_param_visitor(v: GONameVisitor) = v.visit_param(this)
  def accept_def_iterator(v: GONameIterator) = v.iterate_name_def(this)
  def accept_use_iterator(v: GONameIterator) = v.iterate_name_use(this)
  def accept_param_iterator(v: GONameIterator) = v.iterate_param(this)

class GODefRef(var defn: Either[GODef, Str]):
  def getName: String = defn match {
    case Left(godef) => godef.getName
    case Right(name) => name
  }
  def expectDefn: GODef = defn match {
    case Left(godef) => godef
    case Right(name) => throw Exception(s"Expected a def, but got $name")
  }
  
  def getDefn: Opt[GODef] = defn match {
    case Left(godef) => Some(godef)
    case Right(name) => None
  }

  override def equals(o: Any): Bool = o match {
    case o: GODefRef if this.isInstanceOf[GODefRef] =>
      o.getName == this.getName
    case _ => false
  }
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)

case class ElimInfo(elim: Elim, loc: DefnLocMarker):
  override def toString: String = s"<$elim@$loc>"

implicit object ElimInfoOrdering extends Ordering[ElimInfo]:
  override def compare(a: ElimInfo, b: ElimInfo) = a.toString.compare(b.toString)

enum Elim:
  case EDirect
  case EApp(n: Int)
  case EDestruct
  case EIndirectDestruct
  case ESelect(x: Str)

  override def toString: String = this match
    case EDirect => "EDirect"
    case EApp(n) => s"EApp($n)"
    case EDestruct => s"EDestruct"
    case EIndirectDestruct => s"EIndirectDestruct"
    case ESelect(x: Str) => s"ESelect($x)"

  def toShortString: String = this match
    case EDirect => "T"
    case EApp(n) => s"A$n"
    case EDestruct => s"D"
    case EIndirectDestruct => s"I"
    case ESelect(x: Str) => s"S($x)"
  

implicit object ElimOrdering extends Ordering[Elim]:
  override def compare(a: Elim, b: Elim) = a.toString.compare(b.toString)

case class IntroInfo(intro: Intro, loc: DefnLocMarker):
  override def toString: String = s"$intro"

enum Intro:
  case ICtor(c: Str)
  case ILam(n: Int)
  case IMulti(n: Int)
  case IMix(i: Set[Intro])

  override def toString: String = this match
    case ICtor(c) => s"ICtor($c)"
    case ILam(n) => s"ILam($n)"
    case IMulti(n) => s"IMulti($n)"
    case IMix(i) => s"IMix(${i.toSeq.sorted.mkString(",")})"

  def toShortString: String = this match
    case ICtor(c) => s"C($c)"
    case ILam(n) => s"L$n"
    case IMulti(n) => s"M$n"
    case IMix(i) => s"X(${i.toSeq.map(_.toShortString).sorted.mkString})"

  override def equals(o: Any): Boolean = o match
    case o: Intro if this.isInstanceOf[Intro] =>
      (o, this) match
        case (ICtor(c1), ICtor(c2)) => c1 == c2
        case (ILam(n1), ILam(n2)) => n1 == n2
        case (IMulti(n1), IMulti(n2)) => n1 == n2
        case (IMix(i1), IMix(i2)) => 
          i1 == i2
        case _ => false
    case _ => false

implicit object IntroOrdering extends Ordering[Intro]:
  override def compare(a: Intro, b: Intro) = a.toString.compare(b.toString)

case class GODef(
  val id: Int,
  val name: Str,
  val isjp: Bool,
  val params: Ls[Name],
  val resultNum: Int,
  var specialized: Opt[Ls[Opt[Intro]]],
  var body: GONode
):
  var activeInputs: Set[Ls[Opt[Intro]]] = Set()
  var activeResults: Ls[Opt[Intro]] = Ls(None)
  var newActiveInputs: Set[Ls[Opt[IntroInfo]]] = Set()
  var newActiveParams: Ls[Set[ElimInfo]] = Ls(Set())
  var newActiveResults: Ls[Opt[IntroInfo]] = Ls(None)
  var recBoundary: Opt[Int] = None

  override def equals(o: Any): Bool = o match {
    case o: GODef if this.isInstanceOf[GODef] =>
      o.id == id &&
      o.body == body
    case _ => false
  }
  override def hashCode: Int = id
  def getName: String = name
  def accept_visitor(v: GOVisitor) = v.visit(this)
  def accept_iterator(v: GOIterator) = v.iterate(this)
  override def toString: String =
    val name2 = if (isjp) s"@join $name" else s"$name"
    val ps = params.map(_.toString).mkString("[", ",", "]")
    val naps = newActiveParams.map(_.toSeq.sorted.mkString("{", ",", "}")).mkString("[", ",", "]")
    val ais = activeInputs.map(_.toSeq.sorted.mkString("[", ",", "]")).mkString("[", ",", "]")
    val ars = activeResults.map(_.toString()).mkString("[", ",", "]")
    val spec = specialized.map(_.toSeq.sorted.mkString("[", ",", "]")).toString()
    s"Def($id, $name2, $ps, $naps,\nS: $spec,\nI: $ais,\nR: $ars,\nRec: $recBoundary,\n$resultNum, \n$body\n)"

sealed trait TrivialExpr:
  import GOExpr._
  override def toString: String
  def show: String
  def toDocument: Document
  def accept_visitor(v: GOTrivialExprVisitor): TrivialExpr = this match
    case x: Ref => v.visit(x)
    case x: Literal => v.visit(x)
  def accept_iterator(v: GOTrivialExprIterator): Unit = this match
    case x: Ref => v.iterate(x)
    case x: Literal => v.iterate(x)
  // how to fix this
  def map_name_of_texpr(f: Name => Name): TrivialExpr = this match
    case x: Ref => Ref(f(x.name))
    case x: Literal => x

  def to_expr: GOExpr = this match { case x: GOExpr => x }

private def show_args(args: Ls[TrivialExpr]) = args map (_.show) mkString ","

case class DefnTag(inner: Int):
  def is_valid = inner >= 0
  override def equals(x: Any): Bool = x match
    case o: DefnTag if this.isInstanceOf[DefnTag] =>
      (this, o) match
        case (DefnTag(a), DefnTag(b)) => this.is_valid && o.is_valid && a == b
    case _ => false
  override def toString(): String = if is_valid then s"#$inner" else "#x"

case class DefnLocMarker(val defn: Str, val marker: LocMarker):
  override def toString: String = s"$defn:$marker"
  def matches = marker.matches _

enum LocMarker:
  case MRef(name: Str)
  case MLit(lit: Lit)
  case MCtorApp(name: ClassInfo, args: Ls[LocMarker])
  case MSelect(name: Str, cls: ClassInfo, field: Str)
  case MBasicOp(name: Str, args: Ls[LocMarker])
  case MResult(res: Ls[LocMarker])
  case MJump(name: Str, args: Ls[LocMarker])
  case MCase(scrut: Str, cases: Ls[ClassInfo])
  case MLetExpr(name: Str, expr: LocMarker)
  case MLetCall(names: Ls[Str], defn: Str, args: Ls[LocMarker])
  var tag = DefnTag(-1)

  def toDocument: Document = this match
    case MResult(res) => raw("...")
    case MJump(jp, args) =>
      raw("jump")
      <:> raw(jp)
      <:> raw("...")
    case MCase(x, Ls(tcls, fcls)) if tcls.ident == "True" && fcls.ident == "False" =>
      raw("if") <:> raw(x.toString) <:> raw("...")
    case MCase(x, cases) =>
      raw("case") <:> raw(x.toString) <:> raw("of") <:> raw("...")
    case MLetExpr(x, expr) => 
      raw("let")
        <:> raw(x.toString)
        <:> raw("=")
        <:> raw("...")
    case MLetCall(xs, defn, args) =>
      raw("let*")
        <:> raw("(")
        <#> raw(xs.map(_.toString).mkString(","))
        <#> raw(")")
        <:> raw("=")
        <:> raw(defn)
        <:> raw("...")
    case MRef(s) => s.toString |> raw
    case MLit(IntLit(lit)) => s"$lit" |> raw
    case MLit(DecLit(lit)) => s"$lit" |> raw
    case MLit(StrLit(lit)) => s"$lit" |> raw
    case MLit(UnitLit(lit)) => s"$lit" |> raw
    case _ => raw("...")

  def show = s"$tag-" + toDocument.print

  override def toString(): String = show

  def matches(x: GONode): Bool = this.tag == x.tag

  override def equals(x: Any): Boolean = x match
    case x: LocMarker if this.isInstanceOf[LocMarker] =>
      this.tag == x.tag
    case _ => false

enum GOExpr:
  case Ref(name: Name) extends GOExpr, TrivialExpr 
  case Literal(lit: Lit) extends GOExpr, TrivialExpr
  case CtorApp(name: ClassInfo, args: Ls[TrivialExpr])
  case Select(name: Name, cls: ClassInfo, field: Str)
  case BasicOp(name: Str, args: Ls[TrivialExpr])
  
  override def toString: String = show

  def show: String =
    toDocument.print
  
  def toDocument: Document = this match
    case Ref(s) => s.toString |> raw
    case Literal(IntLit(lit)) => s"$lit" |> raw
    case Literal(DecLit(lit)) => s"$lit" |> raw
    case Literal(StrLit(lit)) => s"$lit" |> raw
    case Literal(UnitLit(lit)) => s"$lit" |> raw
    case CtorApp(ClassInfo(_, name, _), args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")
    case Select(s, _, fld) =>
      raw(s.toString) <#> raw(".") <#> raw(fld)
    case BasicOp(name: Str, args) =>
      raw(name) <#> raw("(") <#> raw(args |> show_args) <#> raw(")")

  def map_name(f: Name => Name): GOExpr = this match
    case Ref(name) => Ref(f(name))
    case Literal(lit) => Literal(lit)
    case CtorApp(cls, args) => CtorApp(cls, args.map(_.map_name_of_texpr(f)))
    case Select(x, cls, field) => Select(f(x), cls, field)
    case BasicOp(name, args) => BasicOp(name, args.map(_.map_name_of_texpr(f)))
  
  def accept_visitor(v: GOVisitor): GOExpr = this match
    case x: Ref => v.visit(x).to_expr
    case x: Literal => v.visit(x).to_expr
    case x: CtorApp => v.visit(x)
    case x: Select => v.visit(x)
    case x: BasicOp => v.visit(x)

  def accept_iterator(v: GOIterator): Unit = this match
    case x: Ref => v.iterate(x)
    case x: Literal => v.iterate(x)
    case x: CtorApp => v.iterate(x)
    case x: Select => v.iterate(x)
    case x: BasicOp => v.iterate(x)

  def loc_marker: LocMarker = this match
    case Ref(name) => LocMarker.MRef(name.str)
    case Literal(lit) => LocMarker.MLit(lit)
    case CtorApp(name, args) => LocMarker.MCtorApp(name, args.map(_.to_expr.loc_marker))
    case Select(name, cls, field) => LocMarker.MSelect(name.str, cls, field)
    case BasicOp(name, args) => LocMarker.MBasicOp(name, args.map(_.to_expr.loc_marker))
  

enum GONode:
  // Terminal forms:
  case Result(res: Ls[TrivialExpr])
  case Jump(defn: GODefRef, args: Ls[TrivialExpr])
  case Case(scrut: Name, cases: Ls[(ClassInfo, GONode)])
  // Intermediate forms:
  case LetExpr(name: Name, expr: GOExpr, body: GONode)
  case LetCall(names: Ls[Name], defn: GODefRef, args: Ls[TrivialExpr], body: GONode)

  var tag = DefnTag(-1)

  def attach_tag(x: FreshInt): GONode =
    this.tag = DefnTag(x.make)
    this
  def attach_tag_as[V](x: FreshInt): V =
    attach_tag(x).asInstanceOf[V]
  def copy_tag(x: GONode) =
    this.tag = x.tag
    this

  override def toString: String = show

  def show: String =
    toDocument.print

  def map_name(f: Name => Name): GONode = this match
    case Result(res) => Result(res.map(_.map_name_of_texpr(f)))
    case Jump(defn, args) => Jump(defn, args.map(_.map_name_of_texpr(f)))
    case Case(scrut, cases) => Case(f(scrut), cases.map { (cls, arm) => (cls, arm.map_name(f)) })
    case LetExpr(name, expr, body) => LetExpr(f(name), expr.map_name(f), body.map_name(f))
    case LetCall(names, defn, args, body) => LetCall(names.map(f), defn, args.map(_.map_name_of_texpr(f)), body.map_name(f))  
  
  def copy(ctx: Map[Str, Name]): GONode = this match
    case Result(res) => Result(res.map(_.map_name_of_texpr(_.trySubst(ctx))))
    case Jump(defn, args) => Jump(defn, args.map(_.map_name_of_texpr(_.trySubst(ctx))))
    case Case(scrut, cases) => Case(ctx(scrut.str), cases.map { (cls, arm) => (cls, arm.copy(ctx)) })
    case LetExpr(name, expr, body) => 
      val name_copy = name.copy
      LetExpr(name_copy, expr.map_name(_.trySubst(ctx)), body.copy(ctx + (name_copy.str -> name_copy)))
    case LetCall(names, defn, args, body) => 
      val names_copy = names.map(_.copy)
      LetCall(names_copy, defn, args.map(_.map_name_of_texpr(_.trySubst(ctx))), body.copy(ctx ++ names_copy.map(x => x.str -> x)))

  private def toDocument: Document = this match
    case Result(res) => raw(res |> show_args) <:> raw(s"-- $tag")
    case Jump(jp, args) =>
      raw("jump")
      <:> raw(jp.getName)
      <#> raw("(")
      <#> raw(args |> show_args)
      <#> raw(")")
      <:> raw(s"-- $tag") 
    case Case(x, Ls((tcls, tru), (fcls, fls))) if tcls.ident == "True" && fcls.ident == "False" =>
      val first = raw("if") <:> raw(x.toString) <:> raw(s"-- $tag") 
      val tru2 = indent(raw("true") <:> raw ("=>") <:> tru.toDocument)
      val fls2 = indent(raw("false") <:> raw ("=>") <:> fls.toDocument)
      Document.Stacked(Ls(first, tru2, fls2))
    case Case(x, cases) =>
      val first = raw("case") <:> raw(x.toString) <:> raw("of") <:> raw(s"-- $tag") 
      val other = cases map {
        case (ClassInfo(_, name, _), node) =>
          indent(raw(name) <:> raw("=>") <:> node.toDocument)
      }
      Document.Stacked(first :: other)
    case LetExpr(x, expr, body) => 
      stack(
        raw("let")
          <:> raw(x.toString)
          <:> raw("=")
          <:> expr.toDocument
          <:> raw(s"-- $tag") ,
        raw("in") <:> body.toDocument |> indent)
    case LetCall(xs, defn, args, body) => 
      stack(
        raw("let*")
          <:> raw("(")
          <#> raw(xs.map(_.toString).mkString(","))
          <#> raw(")")
          <:> raw("=")
          <:> raw(defn.getName)
          <#> raw("(")
          <#> raw(args.map{ x => x.toString }.mkString(","))
          <#> raw(")")
          <:> raw(s"-- $tag") ,
        raw("in") <:> body.toDocument |> indent
      )

  def accept_visitor(v: GOVisitor): GONode  = this match
    case x: Result => v.visit(x)
    case x: Jump => v.visit(x)
    case x: Case => v.visit(x)
    case x: LetExpr => v.visit(x)
    case x: LetCall => v.visit(x)

  def accept_iterator(v: GOIterator): Unit  = this match
    case x: Result => v.iterate(x)
    case x: Jump => v.iterate(x)
    case x: Case => v.iterate(x)
    case x: LetExpr => v.iterate(x)
    case x: LetCall => v.iterate(x)
  
  def loc_marker: LocMarker =
    val marker = this match
      case Result(res) => LocMarker.MResult(res.map(_.to_expr.loc_marker))
      case Jump(defn, args) => LocMarker.MJump(defn.getName, args.map(_.to_expr.loc_marker))
      case Case(scrut, cases) => LocMarker.MCase(scrut.str, cases.map(_._1))
      case LetExpr(name, expr, _) => LocMarker.MLetExpr(name.str, expr.loc_marker)
      case LetCall(names, defn, args, _) => LocMarker.MLetCall(names.map(_.str), defn.getName, args.map(_.to_expr.loc_marker))
    marker.tag = this.tag
    marker

trait GONameVisitor:
  def visit_name_def(x: Name): Name = x
  def visit_name_use(x: Name): Name = x
  def visit_param(x: Name): Name    = x

trait GOTrivialExprVisitor extends GONameVisitor:
  import GOExpr._
  def visit(x: Ref): TrivialExpr     = Ref(x.name.accept_use_visitor(this))   
  def visit(x: Literal): TrivialExpr = x

trait GOVisitor extends GOTrivialExprVisitor:
  import GOExpr._
  import GONode._
  def visit(x: CtorApp): GOExpr      = x match
    case CtorApp(cls, xs)            => CtorApp(cls.accept_visitor(this), xs.map(_.accept_visitor(this)))
  def visit(x: Select): GOExpr       = x match
    case Select(x, cls, field)       => Select(x.accept_use_visitor(this), cls.accept_visitor(this), field)
  def visit(x: BasicOp): GOExpr      = x match
    case BasicOp(op, xs)             => BasicOp(op, xs.map(_.accept_visitor(this)))
  def visit(x: Result): GONode       = x match
    case Result(xs)                  => Result(xs.map(_.accept_visitor(this)))
  def visit(x: Jump): GONode         = x match
    case Jump(jp, xs)                => Jump(jp.accept_visitor(this), xs.map(_.accept_visitor(this)))
  def visit(x: Case): GONode         = x match
    case Case(x, cases)              => Case(x.accept_use_visitor(this), cases map { (cls, arm) => (cls, arm.accept_visitor(this)) })
  def visit(x: LetExpr): GONode      = x match
    case LetExpr(x, e1, e2)          => LetExpr(x.accept_def_visitor(this), e1.accept_visitor(this), e2.accept_visitor(this))
  def visit(x: LetCall): GONode      = x match
    case LetCall(xs, f, as, e2)      => LetCall(xs.map(_.accept_def_visitor(this)), f.accept_visitor(this), as.map(_.accept_visitor(this)), e2.accept_visitor(this))
  def visit(x: GODefRef): GODefRef   = x
  def visit(x: ClassInfo): ClassInfo = x
  def visit(x: GODef): GODef         =
    GODef(
      x.id,
      x.name,
      x.isjp,
      x.params.map(_.accept_param_visitor(this)),
      x.resultNum,
      x.specialized,
      x.body.accept_visitor(this))
  def visit(x: GOProgram): GOProgram =
    GOProgram(
      x.classes.map(_.accept_visitor(this)),
      x.defs.map(_.accept_visitor(this)),
      x.main.accept_visitor(this))

trait GONameIterator:
  def iterate_name_def(x: Name): Unit = ()
  def iterate_name_use(x: Name): Unit = ()
  def iterate_param(x: Name): Unit    = ()

trait GOTrivialExprIterator extends GONameIterator:
  import GOExpr._
  def iterate(x: Ref): Unit         = x.name.accept_use_iterator(this)
  def iterate(x: Literal): Unit     = ()

trait GOIterator extends GOTrivialExprIterator:
  import GOExpr._
  import GONode._
  def iterate(x: CtorApp): Unit        = x match
    case CtorApp(cls, xs)              => cls.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Select): Unit         = x match
    case Select(x, cls, field)         => x.accept_use_iterator(this); cls.accept_iterator(this)
  def iterate(x: BasicOp): Unit        = x match
    case BasicOp(op, xs)               => xs.foreach(_.accept_iterator(this))
  def iterate(x: Result): Unit         = x match
    case Result(xs)                    => xs.foreach(_.accept_iterator(this))
  def iterate(x: Jump): Unit           = x match
    case Jump(jp, xs)                  => jp.accept_iterator(this); xs.foreach(_.accept_iterator(this))
  def iterate(x: Case): Unit           = x match
    case Case(x, cases)                => x.accept_use_iterator(this); cases foreach { (cls, arm) => arm.accept_iterator(this) }
  def iterate(x: LetExpr): Unit        = x match
    case LetExpr(x, e1, e2)            => x.accept_def_iterator(this); e1.accept_iterator(this); e2.accept_iterator(this)
  def iterate(x: LetCall): Unit        = x match
    case LetCall(xs, f, as, e2)        => xs.foreach(_.accept_def_iterator(this)); f.accept_iterator(this); as.foreach(_.accept_iterator(this)); e2.accept_iterator(this)
  def iterate(x: GODefRef): Unit       = ()
  def iterate(x: ClassInfo): Unit      = ()
  def iterate(x: GODef): Unit =
    x.params.foreach(_.accept_param_iterator(this))
    x.body.accept_iterator(this)
  def iterate(x: GOProgram): Unit =
    x.classes.foreach(_.accept_iterator(this))
    x.defs.foreach(_.accept_iterator(this))
    x.main.accept_iterator(this)

trait GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef]
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str]

object GODefDfs:
  import GONode._
  private class Successors extends GOIterator:
    var succ: ListBuffer[GODef] = ListBuffer()
    override def iterate(x: GODefRef) =
      succ += x.expectDefn

  private class SuccessorNames extends GOIterator:
    var succ: ListBuffer[Str] = ListBuffer()
    override def iterate(x: GODefRef) =
      succ += x.getName

  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[GODef], postfix: Bool)(x: GODef): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x
    val succ = Successors()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }
    if (postfix)
      out += x
  
  private def dfs(using visited: HashMap[Str, Bool], out: ListBuffer[GODef], postfix: Bool)(x: GONode): Unit =
    val succ = Successors()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y.name))
        dfs(y)
    }

  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[GODef], out: ListBuffer[Str], postfix: Bool)(x: GODef): Unit =
    visited.update(x.name, true)
    if (!postfix)
      out += x.name
    val succ = SuccessorNames()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y))
        dfs_names(defs.find(_.name == y).get)
    }
    if (postfix)
      out += x.name
  
  private def dfs_names(using visited: HashMap[Str, Bool], defs: Set[GODef], out: ListBuffer[Str], postfix: Bool)(x: GONode): Unit =
    val succ = SuccessorNames()
    x.accept_iterator(succ)
    succ.succ.foreach { y =>
      if (!visited(y))
        dfs_names(defs.find(_.name == y).get)
    }

  def dfs(entry: GONode, defs: Set[GODef], postfix: Bool): Ls[GODef] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[GODef]()
    dfs(using visited, out, postfix)(entry)
    out.toList

  def dfs_names(entry: GONode, defs: Set[GODef], postfix: Bool): Ls[Str] =
    val visited = HashMap[Str, Bool]()
    visited ++= defs.map(_.name -> false)
    val out = ListBuffer[Str]()
    dfs_names(using visited, defs, out, postfix)(entry)
    out.toList
    
object GODefRevPostOrdering extends GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef] =
    GODefDfs.dfs(entry, defs, true).reverse
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str] =
    GODefDfs.dfs_names(entry, defs, true).reverse

object GODefRevPreOrdering extends GODefTraversalOrdering:
  def ordered(entry: GONode, defs: Set[GODef]): Ls[GODef] =
    GODefDfs.dfs(entry, defs, false).reverse
  def ordered_names(entry: GONode, defs: Set[GODef]): Ls[Str] =
    GODefDfs.dfs_names(entry, defs, false).reverse
