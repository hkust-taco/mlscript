package mlscript

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.immutable.SortedSet

import math.Ordered.orderingToOrdered

import mlscript.utils._, shorthands._


// Auxiliary definitions for types

abstract class TypeImpl extends Located { self: Type =>
  
  lazy val typeVarsList: List[TypeVar] = this match {
    case uv: TypeVar => uv :: Nil
    case Recursive(n, b) => n :: b.typeVarsList
    case _ => children.flatMap(_.typeVarsList)
  }

  /**
    * @return
    *  set of free type variables in type
    */
  lazy val freeTypeVariables: Set[TypeVar] = this match {
    case Recursive(uv, body) => body.freeTypeVariables - uv
    case t: TypeVar => Set.single(t)
    case _ => this.children.foldRight(Set.empty[TypeVar])((ty, acc) => ty.freeTypeVariables ++ acc)
  }
  
  def show: Str = showIn(ShowCtx.mk(this :: Nil), 0)
  
  private def parensIf(str: Str, cnd: Boolean): Str = if (cnd) "(" + str + ")" else str
  private def showField(f: Field, ctx: ShowCtx): Str = f match {
    case Field(N, ub) => ub.showIn(ctx, 0)
    case Field(S(lb), ub) if lb === ub => ub.showIn(ctx, 0)
    case Field(S(Bot), ub) => s"out ${ub.showIn(ctx, 0)}"
    case Field(S(lb), Top) => s"in ${lb.showIn(ctx, 0)}"
    case Field(S(lb), ub) => s"in ${lb.showIn(ctx, 0)} out ${ub.showIn(ctx, 0)}"
  }
  def showIn(ctx: ShowCtx, outerPrec: Int): Str = this match {
  // TODO remove obsolete pretty-printing hacks
    case Top => "anything"
    case Bot => "nothing"
    case TypeName(name) => name
    // case uv: TypeVar => ctx.vs.getOrElse(uv, s"[??? $uv ???]")
    case uv: TypeVar => ctx.vs(uv)
    case Recursive(n, b) => parensIf(s"${b.showIn(ctx, 2)} as ${ctx.vs(n)}", outerPrec > 1)
    case WithExtension(b, r) => parensIf(s"${b.showIn(ctx, 2)} with ${r.showIn(ctx, 0)}", outerPrec > 1)
    case Function(Tuple((N,Field(N,l)) :: Nil), r) => Function(l, r).showIn(ctx, outerPrec)
    case Function(l, r) => parensIf(l.showIn(ctx, 31) + " -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Neg(t) => s"~${t.showIn(ctx, 100)}"
    case Record(fs) => fs.map { nt =>
        val nme = nt._1.name
        if (nme.isCapitalized) nt._2 match {
          case Field(N | S(Bot), Top) => s"$nme"
          case Field(S(lb), ub) if lb === ub => s"$nme = ${ub.showIn(ctx, 0)}"
          case Field(N | S(Bot), ub) => s"$nme <: ${ub.showIn(ctx, 0)}"
          case Field(S(lb), Top) => s"$nme :> ${lb.showIn(ctx, 0)}"
          case Field(S(lb), ub) => s"$nme :> ${lb.showIn(ctx, 0)} <: ${ub.showIn(ctx, 0)}"
        }
        else s"${nt._2.mutStr}${nme}: ${showField(nt._2, ctx)}"
      }.mkString("{", ", ", "}")
    case Tuple(fs) =>
      fs.map(nt => s"${nt._2.mutStr}${nt._1.fold("")(_.name + ": ")}${showField(nt._2, ctx)},").mkString("(", " ", ")")
    case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
      TypeName("bool").showIn(ctx, 0)
    // case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    // case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
    case c: Composed =>
      val prec = if (c.pol) 20 else 25
      val opStr = if (c.pol) " | " else " & "
      c.distinctComponents match {
        case Nil => (if (c.pol) Bot else Top).showIn(ctx, prec)
        case x :: Nil => x.showIn(ctx, prec)
        case _ =>
          parensIf(c.distinctComponents.iterator
            .map(_.showIn(ctx, prec))
            .reduce(_ + opStr + _), outerPrec > prec)
      }
    // 
    case Bounds(Bot, Top) => s"?"
    case Bounds(lb, ub) if lb === ub => lb.showIn(ctx, outerPrec)
    case Bounds(Bot, ub) => s"out ${ub.showIn(ctx, 0)}"
    case Bounds(lb, Top) => s"in ${lb.showIn(ctx, 0)}"
    case Bounds(lb, ub) => s"in ${lb.showIn(ctx, 0)} out ${ub.showIn(ctx, 0)}"
    // 
    case AppliedType(n, args) => s"${n.name}[${args.map(_.showIn(ctx, 0)).mkString(", ")}]"
    case Rem(b, ns) => s"${b.showIn(ctx, 90)}${ns.map("\\"+_).mkString}"
    case Literal(IntLit(n)) => n.toString
    case Literal(DecLit(n)) => n.toString
    case Literal(StrLit(s)) => "\"" + s + "\""
    case Constrained(b, ws) => parensIf(s"${b.showIn(ctx, 0)}\n  where${ws.map {
      case (uv, Bounds(Bot, ub)) =>
        s"\n    ${ctx.vs(uv)} <: ${ub.showIn(ctx, 0)}"
      case (uv, Bounds(lb, Top)) =>
        s"\n    ${ctx.vs(uv)} :> ${lb.showIn(ctx, 0)}"
      case (uv, Bounds(lb, ub)) if lb === ub =>
        s"\n    ${ctx.vs(uv)} := ${lb.showIn(ctx, 0)}"
      case (uv, Bounds(lb, ub)) =>
        val vstr = ctx.vs(uv)
        s"\n    ${vstr             } :> ${lb.showIn(ctx, 0)}" +
        s"\n    ${" " * vstr.length} <: ${ub.showIn(ctx, 0)}"
    }.mkString}", outerPrec > 0)
    case Literal(UnitLit(b)) => if (b) "undefined" else "null"
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Bounds(l, r) => l :: r :: Nil
    case Neg(b) => b :: Nil
    case Record(fs) => fs.flatMap(f => f._2.in.toList ++ (f._2.out :: Nil))
    case Tuple(fs) => fs.flatMap(f => f._2.in ++ (f._2.out :: Nil))
    case Union(l, r) => l :: r :: Nil.toList
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
    case AppliedType(n, ts) => ts
    case Rem(b, _) => b :: Nil
    case WithExtension(b, r) => b :: r :: Nil
    case Constrained(b, ws) => b :: ws.flatMap(c => c._1 :: c._2 :: Nil)
  }

  /**
    * Collect fields recursively during code generation.
    * Note that the type checker will reject illegal cases.
    */
  lazy val collectFields: Ls[Str] = this match {
    case Record(fields) => fields.map(_._1.name)
    case Inter(ty1, ty2) => ty1.collectFields ++ ty2.collectFields
    case _: Union | _: Function | _: Tuple | _: Recursive
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName | _: Constrained =>
      Nil
  }

  /**
    * Collect `TypeName`s recursively during code generation.
    * Note that the type checker will reject illegal cases.
    */
  lazy val collectTypeNames: Ls[Str] = this match {
    case TypeName(name) => name :: Nil
    case AppliedType(TypeName(name), _) => name :: Nil
    case Inter(lhs, rhs) => lhs.collectTypeNames ++ rhs.collectTypeNames
    case _: Union | _: Function | _: Record | _: Tuple | _: Recursive
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot
        | _: Literal | _: TypeVar | _: Constrained =>
      Nil
  }

  // Collect fields and types of record types that are intersected
  // by traversing the first level of intersection. This is used
  // for finding the fields and types of a class body, since the
  // body is made of up an intersection of classes and records
  lazy val collectBodyFieldsAndTypes: List[Var -> Type] = this match {
    case Record(fields) => fields.map(field => (field._1, field._2.out))
    case Inter(ty1, ty2) => ty1.collectBodyFieldsAndTypes ++ ty2.collectBodyFieldsAndTypes
    case _: Union | _: Function | _: Tuple | _: Recursive
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName | _: Constrained =>
      Nil
  }
}


final case class ShowCtx(vs: Map[TypeVar, Str], debug: Bool) // TODO make use of `debug` or rm
object ShowCtx {
  /**
    * Create a context from a list of types. For named variables and
    * hinted variables use what is given. For unnamed variables generate
    * completely new names. If same name exists increment counter suffix
    * in the name.
    */
  def mk(tys: IterableOnce[Type], pre: Str = "'", debug: Bool = false): ShowCtx = {
    val (otherVars, namedVars) = tys.iterator.toList.flatMap(_.typeVarsList).distinct.partitionMap { tv =>
      tv.identifier match { case L(_) => L(tv.nameHint -> tv); case R(nh) => R(nh -> tv) }
    }
    val (hintedVars, unnamedVars) = otherVars.partitionMap {
      case (S(nh), tv) => L(nh -> tv)
      case (N, tv) => R(tv)
    }
    val usedNames = MutMap.empty[Str, Int]
    def assignName(n: Str): Str =
      usedNames.get(n) match {
        case S(cnt) =>
          usedNames(n) = cnt + 1
          pre + 
          n + cnt
        case N =>
          usedNames(n) = 0
          pre + 
          n
      }
    val namedMap = (namedVars ++ hintedVars).map { case (nh, tv) =>
      tv -> assignName(nh.dropWhile(_ === '\''))
      // tv -> assignName(nh.stripPrefix(pre))
    }.toMap
    val used = usedNames.keySet
    
    // * Generate names for unnamed variables
    val numLetters = 'z' - 'a' + 1
    val names = Iterator.unfold(0) { idx =>
      val postfix = idx/numLetters
      S(('a' + idx % numLetters).toChar.toString + (if (postfix === 0) "" else postfix.toString), idx + 1)
    }.filterNot(used).map(assignName)
    
    ShowCtx(namedMap ++ unnamedVars.zip(names), debug)
  }
}

trait ComposedImpl { self: Composed =>
  val lhs: Type
  val rhs: Type
  def components: Ls[Type] = (lhs match {
    case c: Composed if c.pol === pol => c.components
    case _ => lhs :: Nil
  }) ::: (rhs match {
    case c: Composed if c.pol === pol => c.components
    case _ => rhs :: Nil
  })
  lazy val distinctComponents =
    components.filterNot(c => if (pol) c === Bot else c === Top).distinct
}

abstract class PolyTypeImpl extends Located { self: PolyType =>
  def children: List[Located] =  targs :+ body
  def show: Str = s"${targs.iterator.map(_.name).mkString("[", ", ", "] ->")} ${body.show}"
}

trait TypeVarImpl extends Ordered[TypeVar] { self: TypeVar =>
  def compare(that: TypeVar): Int = {
    (this.identifier.fold((_, ""), (0, _))) compare (that.identifier.fold((_, ""), (0, _)))
  }
}

// Auxiliary definitions for terms

trait PgrmImpl { self: Pgrm =>
  lazy val desugared: (Ls[Diagnostic] -> (Ls[TypeDef], Ls[Terms])) = {
    val diags = Buffer.empty[Diagnostic]
    val res = tops.flatMap { s =>
        val (ds, d) = s.desugared
        diags ++= ds
        d
    }.partitionMap {
      case td: TypeDef => L(td)
      case ot: Terms => R(ot)
    }
    diags.toList -> res
  }
  override def toString = tops.map("" + _ + ";").mkString(" ")
}

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
  def showBody: Str = this match {
    case Def(_, _, rhs) => rhs.fold(_.toString, _.show)
    case td: TypeDef => td.body.show
  }
  def describe: Str = this match {
    case _: Def => "definition"
    case _: TypeDef => "type declaration"
  }
  def show: Str = showHead + (this match {
    case TypeDef(Als, _, _, _, _, _) => " = "; case _ => ": " }) + showBody
  def showHead: Str = this match {
    case Def(true, n, b) => s"rec def $n"
    case Def(false, n, b) => s"def $n"
    case TypeDef(k, n, tps, b, _, _) =>
      s"${k.str} ${n.name}${if (tps.isEmpty) "" else tps.map(_.name).mkString("[", ", ", "]")}"
  }
}

trait TypeNameImpl extends Ordered[TypeName] { self: TypeName =>
  def compare(that: TypeName): Int = this.name compare that.name
}

trait TermImpl extends StatementImpl { self: Term =>
  val original: this.type = this
  
  def describe: Str = this match {
    case Bra(true, Tup(_ :: _ :: _) | Tup((S(_), _) :: _) | Blk(_)) => "record"
    case Bra(_, trm) => trm.describe
    case Blk((trm: Term) :: Nil) => trm.describe
    case Blk(_) => "block of statements"
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case UnitLit(value) => if (value) "undefined literal" else "null literal"
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
    case Tup((N, (x, _)) :: Nil) => x.describe
    case Tup((S(_), x) :: Nil) => "binding"
    case Tup(xs) => "tuple"
    case Bind(l, r) => "'as' binding"
    case Test(l, r) => "'is' test"
    case With(t, fs) =>  "`with` extension"
    case CaseOf(scrut, cases) =>  "`case` expression" 
    case Subs(arr, idx) => "array access"
    case Assign(lhs, rhs) => "assignment"
  }
  
  override def toString: Str = this match {
    case Bra(true, trm) => s"{$trm}"
    case Bra(false, trm) => s"($trm)"
    case Blk(stmts) => stmts.map("" + _ + ";").mkString(" ")
    // case Blk(stmts) => stmts.map("" + _ + ";").mkString("‹", " ", "›") // for better legibility in debugging
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if (value) "undefined" else "null"
    case Var(name) => name
    case Asc(trm, ty) => s"$trm : $ty"
    case Lam(name, rhs) => s"($name => $rhs)"
    case App(lhs, rhs) => s"($lhs $rhs)"
    case Rcd(fields) =>
      fields.iterator.map(nv =>
        (if (nv._2._2) "mut " else "") + nv._1.name + ": " + nv._2._1).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => receiver.toString + "." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"(let${if (isRec) " rec" else ""} $name = $rhs; $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) =>
        (if (t._2) "mut " else "") + n.fold("")(_.name + ": ") + t._1 + "," }.mkString("(", " ", ")")
    case Bind(l, r) => s"($l as $r)"
    case Test(l, r) => s"($l is $r)"
    case With(t, fs) =>  s"$t with $fs"
    case CaseOf(s, c) => s"case $s of $c"
    case Subs(a, i) => s"$a[$i]"
    case Assign(lhs, rhs) => s" $lhs <- $rhs"
  }
  
  def toType: Diagnostic \/ Type =
    try R(toType_!) catch {
      case e: NotAType =>
        import Message._
        L(TypeError(msg"not a recognized type: ${e.trm.toString}"->e.trm.toLoc::Nil)) }
  protected def toType_! : Type = (this match {
    case Var(name) if name.startsWith("`") => TypeVar(R(name.tail), N)
    case Var(name) => TypeName(name)
    case App(App(Var("|"), lhs), rhs) => Union(lhs.toType_!, rhs.toType_!)
    case App(App(Var("&"), lhs), rhs) => Inter(lhs.toType_!, rhs.toType_!)
    case Lam(lhs, rhs) => Function(lhs.toType_!, rhs.toType_!)
    case App(lhs, rhs) => lhs.toType_! match {
      case AppliedType(base, targs) => AppliedType(base, targs :+ rhs.toType_!)
      case p: TypeName => AppliedType(p, rhs.toType_! :: Nil)
      case _ => throw new NotAType(this)
    }
    // TODO:
    // case Tup(fields) => ???
    // case Rcd(fields) => ???
    // case Sel(receiver, fieldName) => ???
    // case Let(isRec, name, rhs, body) => ???
    // case Blk(stmts) => ???
    // case Bra(rcd, trm) => ???
    // case Asc(trm, ty) => ???
    // case Bind(lhs, rhs) => ???
    // case Test(trm, ty) => ???
    // case With(trm, fieldNme, fieldVal) => ???
    // case CaseOf(trm, cases) => ???
    // case IntLit(value) => ???
    // case DecLit(value) => ???
    // case StrLit(value) => ???
    case _ => throw new NotAType(this)
  }).withLocOf(this)
  
}
private class NotAType(val trm: Term) extends Throwable

trait LitImpl { self: Lit =>
  def baseClasses: Set[TypeName] = this match {
    case _: IntLit => Set.single(TypeName("int")) + TypeName("number")
    case _: StrLit => Set.single(TypeName("string"))
    case _: DecLit => Set.single(TypeName("number"))
    case _: UnitLit => Set.empty
  }
}

trait VarImpl { self: Var =>
  def isPatVar: Bool =
    name.head.isLetter && name.head.isLower && name =/= "true" && name =/= "false"
}

trait SimpleTermImpl extends Ordered[SimpleTerm] { self: SimpleTerm =>
  def compare(that: SimpleTerm): Int = this.idStr compare that.idStr
  val idStr: Str = this match {
    case Var(name) => name
    case lit: Lit => lit.toString
  }
}

trait FieldImpl extends Located { self: Field =>
  def children: List[Located] =
    self.in.toList ::: self.out :: Nil
  def isMutabe: Bool = in.isDefined
  def mutStr: Str = if (isMutabe) "mut " else ""
}

trait Located {
  def children: List[Located]
  
  private var spanStart: Int = -1
  private var spanEnd: Int = -1
  private var origin: Opt[Origin] = N
  
  // TODO just store the Loc directly...
  def withLoc(s: Int, e: Int, ori: Origin): this.type = {
    // assert(origin.isEmpty)
    origin = S(ori)
    // assert(spanStart < 0)
    // assert(spanEnd < 0)
    spanStart = s
    spanEnd = e
    this
  }
  def withLoc(loco: Opt[Loc]): this.type = {
    loco.foreach { that =>
      spanStart = that.spanStart
      spanEnd = that.spanEnd
      origin = S(that.origin)
    }
    this
  }
  def withLocOf(that: Located): this.type = withLoc(that.toLoc)
  def hasLoc: Bool = origin.isDefined
  lazy val toLoc: Opt[Loc] = getLoc
  private def getLoc: Opt[Loc] = {
    def subLocs = children.iterator.flatMap(_.toLoc.iterator)
    if (spanStart < 0) spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    if (spanEnd < 0) spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    val origins = origin.fold(subLocs.map(_.origin).toList.distinct)(_ :: Nil)
    assert(origins.size === 1, origins)
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
  def describe: Str
}

trait StatementImpl extends Located { self: Statement =>
  
  lazy val desugared = doDesugar
  private def doDesugar: Ls[Diagnostic] -> Ls[DesugaredStatement] = this match {
    case l @ LetS(isrec, pat, rhs) =>
      val (diags, v, args) = desugDefnPattern(pat, Nil)
      diags -> (Def(isrec, v, L(args.foldRight(rhs)(Lam(_, _)))).withLocOf(l) :: Nil) // TODO use v, not v.name
    case d @ DataDefn(body) => desugarCases(body :: Nil, Nil)
    case d @ DatatypeDefn(hd, bod) =>
      val (diags, v, args) = desugDefnPattern(hd, Nil)
      val (diags3, targs) = args.partitionMap {
        case v @ Var(nme) => R(TypeName(nme).withLocOf(v))
        case t =>
          import Message._
          L(TypeError(msg"illegal datatype type parameter shape: ${t.toString}" -> t.toLoc :: Nil))
      }
      val (diags2, cs) = desugarCases(bod, targs)
      val dataDefs = cs.collect{case td: TypeDef => td}
      (diags ::: diags2 ::: diags3) -> (TypeDef(Als, TypeName(v.name).withLocOf(v), targs,
          dataDefs.map(td => AppliedType(td.nme, td.tparams)).reduceOption(Union).getOrElse(Bot)
        ).withLocOf(hd) :: cs)
    case t: Term => Nil -> (t :: Nil)
    case d: Decl => Nil -> (d :: Nil)
  }
  import Message._
  protected def desugDefnPattern(pat: Term, args: Ls[Term]): (Ls[Diagnostic], Var, Ls[Term]) = pat match {
    case App(l, r) => desugDefnPattern(l, r :: args)
    case v: Var => (Nil, v, args)
    case _ => (TypeError(msg"Unsupported pattern shape" -> pat.toLoc :: Nil) :: Nil, Var("<error>"), args) // TODO
  }
  protected def desugarCases(bod: Term, baseTargs: Ls[TypeName]): (Ls[Diagnostic], Ls[Decl]) = bod match {
    case Blk(stmts) => desugarCases(stmts, baseTargs)
    case Tup(comps) =>
      val stmts = comps.map {
        case N -> (d -> _) => d
        case S(n) -> (d -> _) => ???
      }
      desugarCases(stmts, baseTargs)
    case _ => (TypeError(msg"Unsupported data type case shape" -> bod.toLoc :: Nil) :: Nil, Nil)
  }
  protected def desugarCases(stmts: Ls[Statement], baseTargs: Ls[TypeName]): (Ls[Diagnostic], Ls[Decl]) = stmts match {
    case stmt :: stmts =>
      val (diags0, sts) = stmt.desugared
      val (diags2, cs) = desugarCases(stmts, baseTargs)
      val allDiags = Buffer.from(diags0)
      val res = sts.flatMap {
        case t: Term =>
          val (diags1, v, args) = desugDefnPattern(t, Nil)
          allDiags ++= diags1
          val tparams = Buffer.from(baseTargs)
          val fields = SortedMutMap.empty[Var, Type]
          def getFields(t: Term): Ls[Type] = t match {
            case v: Var =>
              // TOOD check not already defined
              val tp = baseTargs.find(_.name === v.name).map(_.copy()).getOrElse(
                if (v.name.startsWith("`")) TypeVar(R(v.name.tail), N)
                else TypeName(v.name) tap (tparams += _)).withLocOf(v)
              fields += v -> tp
              tp :: Nil
            case Blk((t: Term)::Nil) => getFields(t)
            case Blk(_) => ??? // TODO proper error
            case Bra(b, Blk((t:Term)::Nil)) => getFields(Bra(b, t))
            case Bra(false, t) => getFields(t)
            case Bra(true, Tup(fs)) =>
              Record(fs.map {
                case (S(n) -> (t -> tmut)) =>
                  val ty = t.toType match {
                    case L(d) => allDiags += d; Top
                    case R(t) => t
                  }
                  fields += n -> ty
                  n -> Field(None, ty)
                case _ => ???
              }) :: Nil
            case Bra(true, t) => lastWords(s"$t ${t.getClass}")
            case Tup(fs) => // TODO factor with case Bra(true, Tup(fs)) above
              Tuple(fs.map {
                case (S(n) -> (t -> tmut)) =>
                  val ty = t.toType match {
                    case L(d) => allDiags += d; Top
                    case R(t) => t
                  }
                  fields += n -> ty
                  S(n) -> Field(None, ty)
                case _ => ???
              }) :: Nil
            case _ => ??? // TODO proper error
          }
          val params = args.flatMap(getFields)
          val clsNme = TypeName(v.name).withLocOf(v)
          val tps = tparams.toList
          val ctor = Def(false, v, R(PolyType(tps,
            params.foldRight(AppliedType(clsNme, tps):Type)(Function(_, _))))).withLocOf(stmt)
          val td = TypeDef(Cls, clsNme, tps, Record(fields.toList.mapValues(Field(None, _)))).withLocOf(stmt)
          td :: ctor :: cs
        case _ => ??? // TODO methods in data type defs? nested data type defs?
      }
      allDiags ++= diags2
      allDiags.toList -> res
    case Nil => Nil -> Nil
  }
  
  def children: List[Located] = this match {
    case Bra(_, trm) => trm :: Nil
    case Var(name) => Nil
    case Asc(trm, ty) => trm :: Nil
    case Lam(lhs, rhs) => lhs :: rhs :: Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case Tup(fields) => fields.map(_._2._1)
    case Rcd(fields) => fields.map(_._2._1)
    case Sel(receiver, fieldName) => receiver :: fieldName :: Nil
    case Let(isRec, name, rhs, body) => rhs :: body :: Nil
    case Blk(stmts) => stmts
    case LetS(_, pat, rhs) => pat :: rhs :: Nil
    case DatatypeDefn(head, body) => head :: body :: Nil
    case DataDefn(body) => body :: Nil
    case _: Lit => Nil
    case Bind(l, r) => l :: r :: Nil
    case Test(l, r) => l :: r :: Nil
    case With(t, fs) => t :: fs :: Nil
    case CaseOf(s, c) => s :: c :: Nil
    case d @ Def(_, n, b) => n :: d.body :: Nil
    case TypeDef(kind, nme, tparams, body, _, _) => nme :: tparams ::: body :: Nil
    case Subs(a, i) => a :: i :: Nil
    case Assign(lhs, rhs) => lhs :: rhs :: Nil
  }
  
  
  override def toString: Str = this match {
    case LetS(isRec, name, rhs) => s"let${if (isRec) " rec" else ""} $name = $rhs"
    case DatatypeDefn(head, body) => s"data type $head of $body"
    case DataDefn(head) => s"data $head"
    case _: Term => super.toString
    case d: Decl => d.show
  }
}

trait BlkImpl { self: Blk =>
  
  def flatten: Blk = Blk(stmts.flatMap {
    case b: Blk => b.flatten.stmts
    case t => t :: Nil
  })
  
}

trait CaseBranchesImpl extends Located { self: CaseBranches =>
  
  def children: List[Located] = this match {
    case Case(pat, body, rest) => pat :: body :: rest :: Nil
    case Wildcard(body) => body :: Nil
    case NoCases => Nil
  }
  
  lazy val toList: Ls[Case] = this match {
    case c: Case => c :: c.rest.toList
    case _ => Nil
  }
  
}
