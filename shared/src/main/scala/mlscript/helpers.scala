package mlscript

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet}
import scala.collection.immutable.SortedSet

import mlscript.utils._, shorthands._


// Auxiliary definitions for types

abstract class TypeImpl extends Located { self: Type =>
  
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
    case Applied(Applied(Primitive(op), l), r) if !op.head.isLetter =>
      parensIf(l.showIn(ctx, 11) + " " + op + " " + r.showIn(ctx, 11), outerPrec >= 11)
    case Applied(Primitive(op), t) if op.head === '\\' =>
      s"${t.showIn(ctx, 100)}$op"
    case Applied(Primitive(op), t) if op === "~" =>
      s"~${t.showIn(ctx, 100)}"
    case Applied(l, r) => parensIf(l.showIn(ctx, 32) + " " + r.showIn(ctx, 32), outerPrec > 32)
    case Record(fs) => fs.map(nt => s"${nt._1}: ${nt._2.showIn(ctx, 0)}").mkString("{", ", ", "}")
    case Tuple(fs) => fs.map(nt => s"${nt._1.fold("")(_ + ": ")}${nt._2.showIn(ctx, 0)},").mkString("(", " ", ")")
    case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
    case AppliedType(n, args) => s"${n.name}[${args.map(_.showIn(ctx, 0)).mkString(", ")}]"
    // case Rem(b, ns) => s"${b.showIn(ctx, 100)}${ns.map("\\"+_).mkString}" // Not yet used
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Applied(l, r) => l :: r :: Nil
    case Record(fs) => fs.map(_._2)
    case Tuple(fs) => fs.map(_._2)
    case Union(l, r) => l :: r :: Nil
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
    case AppliedType(n, ts) => ts
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

object OpApp {
  def apply(op: Str, trm: Term): Term = App(Var(op), trm)
  def unapply(trm: Term): Opt[Term -> Term] = trm |>? {
    case App(op, lhs)
      if op.toLoc.exists(l => lhs.toLoc.exists(l.spanStart > _.spanStart))
      => (op, lhs)
  }
}

trait DeclImpl extends Located { self: Decl =>
  val body: Located
  def children: Ls[Located] = self match {
    case d @ Def(rec, nme, _) => d.body :: Nil
    case TypeDef(kind, nme, tparams, body) => nme :: body :: Nil
  }
  def show: Str = showHead + (this match {
    case TypeDef(Als, _, _, _) => " = "; case _ => ": " }) + body
  def showHead: Str = this match {
    case Def(true, n, b) => s"rec def $n"
    case Def(false, n, b) => s"def $n"
    case TypeDef(k, n, tps, b) =>
      s"${k.str} ${n.name}${if (tps.isEmpty) "" else tps.mkString("[", ", ", "]")}"
  }
}

trait TermImpl extends StatementImpl { self: Term =>
  val original: this.type = this
  override def children: Ls[Statement] = super[StatementImpl].children
  
  def describe: Str = this match {
    case Bra(true, Tup(_ :: _ :: _) | Tup((S(_), _) :: _) | Blk(_)) => "record"
    case Bra(_, trm) => trm.describe
    case Blk((trm: Term) :: Nil) => trm.describe
    case Blk(_) => "block of statements"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case Var(name) => "reference" // "variable reference"
    case Asc(trm, ty) => "type ascription"
    case Lam(name, rhs) => "lambda expression"
    case App(OpApp(Var("|"), lhs), rhs) => "type union"
    case App(OpApp(Var("&"), lhs), rhs) => "type intersection"
    case App(OpApp(op, lhs), rhs) => "operator application"
    case OpApp(op, lhs) => "operator application"
    case App(lhs, rhs) => "application"
    case Rcd(fields) => "record"
    case Sel(receiver, fieldName) => "field selection"
    case Let(isRec, name, rhs, body) => "let binding"
    case Tup((N, x) :: Nil) => x.describe
    case Tup((S(_), x) :: Nil) => "binding"
    case Tup(xs) => "tuple expression"
    case Bind(l, r) => "'as' binding"
    case Test(l, r) => "'is' test"
    case With(t, n, v) =>  "`with` extension"
    case CaseOf(scrut, cases) =>  "case of" 
  }
  
  override def toString: String = this match {
    case Bra(true, trm) => s"{$trm}"
    case Bra(false, trm) => s"($trm)"
    case Blk(stmts) => stmts.map("" + _ + ";").mkString(" ")
    // case Blk(stmts) => stmts.map("" + _ + ";").mkString("‹", " ", "›") // for better legibility in debugging
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case Var(name) => name
    case Asc(trm, ty) => s"$trm : $ty"
    case Lam(name, rhs) => s"($name => $rhs)"
    case App(lhs, rhs) => s"($lhs $rhs)"
    case Rcd(fields) =>
      fields.iterator.map(nv => nv._1 + ": " + nv._2).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => receiver.toString + "." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"(let${if (isRec) " rec" else ""} $name = $rhs; $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) => n.fold("")(_ + ": ") + t + "," }.mkString("(", " ", ")")
    case Bind(l, r) => s"($l as $r)"
    case Test(l, r) => s"($l is $r)"
    case With(t, n, v) =>  s"$t with {$n = $v}"
    case CaseOf(s, c) => s"case $s of $c"
  }
  
}

trait LitImpl { self: Lit =>
  def baseClass: Var = this match {
    case _: IntLit => Var("int")
    case _: StrLit => Var("string")
    case _: DecLit => Var("number")
  }
}

trait VarImpl { self: Var =>
  def isPatVar: Bool =
    name.head.isLetter && name.head.isLower && name =/= "true" && name =/= "false"
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

trait DesugaredStatementImpl extends Located { self: DesugaredStatement =>
  val original: Statement
  def children: List[Statement] = original.children
  def getFreeVars: Set[Str] = this match {
    case LetDesug(false, _, rhs) => rhs.freeVars
    case LetDesug(true, Var(nme), rhs) => rhs.freeVars - nme
    case DatatypeDesug(_, params, body) =>
      // TODO deal with params properly... they can have free vars!
      body.iterator.flatMap(_.getFreeVars).toSet -- params.iterator.flatMap(_.freeVars)
    case DataDesug(_, params) => Set.empty // TODO
    case t: Term => t.freeVars
  }
}

trait StatementImpl extends Located { self: Statement =>
  
  lazy val desugared = doDesugar
  private def doDesugar: Ls[Diagnostic] -> DesugaredStatement = this match {
    case l @ LetS(isrec, pat, rhs) =>
      val (diags, v, args) = desugDefnPattern(pat, Nil)
      diags -> LetDesug(isrec, v, args.foldRight(rhs)(Lam(_, _)))(l)
    case d @ DataDefn(body) =>
      val (diags, dd :: Nil) = desugarCases(body :: Nil)
      diags -> dd
    case d @ DatatypeDefn(hd, bod) =>
      val (diags, v, args) = desugDefnPattern(hd, Nil)
      val (diags2, cs) = desugarCases(bod)
      (diags ::: diags2) -> DatatypeDesug(v, args, cs)(d)
    case t: Term => Nil -> t
  }
  import Message._
  protected def desugDefnPattern(pat: Term, args: Ls[Term]): (Ls[Diagnostic], Var, Ls[Term]) = pat match {
    case App(l, r) => desugDefnPattern(l, r :: args)
    case v: Var => (Nil, v, args)
    case _ => (TypeError(msg"Unsupported pattern shape" -> pat.toLoc :: Nil) :: Nil, Var("<error>"), args) // TODO
  }
  protected def desugarCases(bod: Term): (Ls[Diagnostic], Ls[DataDesug]) = bod match {
    case Blk(stmts) => desugarCases(stmts)
    case Tup(comps) =>
      val stmts = comps.map {
        case N -> d => d
        case S(n) -> d => ???
      }
      desugarCases(stmts)
    case _ => (TypeError(msg"Unsupported data type case shape" -> bod.toLoc :: Nil) :: Nil, Nil)
  }
  protected def desugarCases(stmts: Ls[Statement]): (Ls[Diagnostic], Ls[DataDesug]) = stmts match {
    case stmt :: stmts =>
      val (diags0, st) = stmt.desugared
      lazy val (diags2, cs) = desugarCases(stmts)
      st match {
        case t: Term =>
          val (diags1, v, args) = desugDefnPattern(t, Nil)
          (diags0 ::: diags1 ::: diags2) -> (DataDesug(v, args)(t) :: cs)
        case _ => ???
      }
    case Nil => Nil -> Nil
  }
  
  // TODO This definition is not quite right;
  // we should account for variables bound within tuples and statement blocks,
  // removing them from the set of freeVars (and similarly for patterns).
  // However, it's currently not really used (only in the expression generation routine!)
  lazy val freeVars: Set[Str] = this match {
    case _: Lit => Set.empty
    case Var(name) => Set.empty[String] + name
    case Asc(trm, ty) => trm.freeVars
    case Lam(pat, rhs) => rhs.freeVars -- pat.freeVars
    case App(lhs, rhs) => lhs.freeVars ++ rhs.freeVars
    case Rcd(fields) => fields.iterator.flatMap(_._2.freeVars).toSet
    case Sel(receiver, fieldName) => receiver.freeVars
    case Let(isRec, name, rhs, body) =>
      (body.freeVars - name) ++ (if (isRec) rhs.freeVars - name else rhs.freeVars)
    case Bra(_, trm) => trm.freeVars
    case Blk(sts) => sts.iterator.flatMap(_.freeVars).toSet
    case Tup(trms) => trms.iterator.flatMap(_._2.freeVars).toSet
    case let: LetS =>
      // Note: in `let f x = ...`, `f` is not a FV!
      let.desugared._2.getFreeVars
    case DatatypeDefn(head, body) => body.freeVars -- head.freeVars
    case DataDefn(head) => Set.empty
    case Bind(l, r) => l.freeVars ++ r.freeVars
    case Test(l, r) => l.freeVars ++ r.freeVars
    case With(t, n, v) => t.freeVars ++ v.freeVars
    case CaseOf(s, c) => s.freeVars ++ c.iterator.flatMap(_.body.freeVars)
  }
  
  def children: List[Statement] = this match {
    case Bra(_, trm) => trm :: Nil
    case Var(name) => Nil
    case Asc(trm, ty) => trm :: Nil
    case Lam(lhs, rhs) => lhs :: rhs :: Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case Tup(fields) => fields.map(_._2)
    case Rcd(fields) => fields.map(_._2)
    case Sel(receiver, fieldName) => receiver :: Nil
    case Let(isRec, name, rhs, body) => rhs :: body :: Nil
    case Blk(stmts) => stmts
    case LetS(_, pat, rhs) => pat :: rhs :: Nil
    case DatatypeDefn(head, body) => head :: body :: Nil
    case DataDefn(body) => body :: Nil
    case _: Lit => Nil
    case Bind(l, r) => l :: r :: Nil
    case Test(l, r) => l :: r :: Nil
    case With(t, n, v) => t :: v :: Nil
    case CaseOf(s, c) => s :: c.iterator.map(_.body).toList
  }
  
  def size: Int = children.iterator.map(_.size).sum + 1
  
  override def toString: String = this match {
    case LetS(isRec, name, rhs) => s"let${if (isRec) " rec" else ""} $name = $rhs"
    case DatatypeDefn(head, body) => s"data type $head of $body"
    case DataDefn(head) => s"data $head"
    case _: Term => super.toString
  }
}

trait BlkImpl { self: Blk =>
  
  def flatten: Blk = Blk(stmts.flatMap {
    case b: Blk => b.flatten.stmts
    case t => t :: Nil
  })
  
}

trait CaseBranchesImpl { self: CaseBranches =>
  
  def iterator: Ite[Case] = this match {
    case c: Case => Ite.single(c) ++ c.rest.iterator
    case _ => Ite.empty
  }
  
  lazy val toList: Ls[Case] = this match {
    case c: Case => c :: c.rest.toList
    case _ => Nil
  }
  
}
