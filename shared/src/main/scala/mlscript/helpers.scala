package mlscript

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.immutable.SortedSet

import mlscript.utils._, shorthands._

/**
  * A class to hold to the context while converting mlscript types to
  * typescript representation.
  * 
  * polarity tracks polarity of the current type.
  * * a type has no polarity by default
  * * a type has negative polarity at function input position
  * * a type has positive polarity at function output position
  * 
  * argCounter tracks number of new argument variable names introduced
  * and then is used to generate unique names
  * 
  * newTypeAlias and typeParams stores information of any new type aliases and params
  * defined when converting. This information is collected to arrange the
  * source code in proper order.
  * 
  * Existing type vars is used to maintain a mapping from originally
  * created type variables to their names. This is then used to resolve
  * `TypeVar` to their SourceCode representation.
  *
  * @param polarity
  * @param argCounter
  * @param existingTypeVars
  * @param newTypeAlias
  * @param typeParams
  */
class ToTsTypegenContext(
  var polarity: Option[Boolean] = None,
  var argCounter: Int = 0,
  var existingTypeVars: Map[TypeVar, String] = Map.empty,
  // adhoc type vars introduced during conversion
  var newTypeAlias: List[SourceCode] = List.empty,
  // adhoc type parameters introduced during conversion
  var newTypeParams: List[SourceCode] = List.empty
) {
  /**
    * Polarity follows is like multiplication where true is positive
    * and false is negative polarity. However adding a polarity to
    * None (no polarity) makes it a Some (giving it a polarity)
    *
    * @param newPolarity
    */
  def multiplyPolarity(newPolarity: Boolean): Unit = {
    this.polarity = this.polarity.map(prev => prev ^ newPolarity).orElse(Some(newPolarity));
  }
}
object ToTsTypegenContext {
  def empty: ToTsTypegenContext = new ToTsTypegenContext();
}

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
  // TODO remove obsolete pretty-printing hacks
    case Top => "anything"
    case Bot => "nothing"
    case TypeName(name) => name
    // case uv: TypeVar => ctx.vs.getOrElse(uv, s"[??? $uv ???]")
    // case Recursive(n, b) => s"${b.showIn(ctx, 31)} as ${ctx.vs.getOrElse(n, s"[??? $n ???]")}"
    case uv: TypeVar => ctx.vs(uv)
    case Recursive(n, b) => parensIf(s"${b.showIn(ctx, 2)} as ${ctx.vs(n)}", outerPrec > 1)
    case WithExtension(b, r) => parensIf(s"${b.showIn(ctx, 2)} with ${r.showIn(ctx, 0)}", outerPrec > 1)
    case Function(Tuple((N,l) :: Nil), r) => Function(l, r).showIn(ctx, outerPrec)
    case Function(l, r) => parensIf(l.showIn(ctx, 31) + " -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Neg(t) => s"~${t.showIn(ctx, 100)}"
    case Record(fs) => fs.map { nt =>
      val nme = nt._1.name
      if (nme.isCapitalized) nt._2 match { // TODO maybe rm this
        case Function(Bot, Top) => s"$nme"
        case Function(lb, ub) if lb === ub => s"$nme = ${ub.showIn(ctx, 0)}"
        case Function(Bot, ub) => s"$nme <: ${ub.showIn(ctx, 0)}"
        case Function(lb, Top) => s"$nme :> ${lb.showIn(ctx, 0)}"
        case Function(lb, ub) => s"$nme :> ${lb.showIn(ctx, 0)} <: ${ub.showIn(ctx, 0)}"
        case Bot | Top => s"$nme"
        case unexpected => s"${nme}: ${unexpected.showIn(ctx, 0)}" // not supposed to happen...
      }
      else s"${nme}: ${nt._2.showIn(ctx, 0)}"
    }.mkString("{", ", ", "}")
    case Tuple(fs) => fs.map(nt => s"${nt._1.fold("")(_.name + ": ")}${nt._2.showIn(ctx, 0)},").mkString("(", " ", ")")
    case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
      TypeName("bool").showIn(ctx, 0)
    case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
    case Bounds(Bot, Top) => s"?"
    case Bounds(Bot, ub) => s".. ${ub.showIn(ctx, 0)}"
    case Bounds(lb, Top) => s"${lb.showIn(ctx, 0)} .."
    case Bounds(lb, ub) => s"${lb.showIn(ctx, 0)} .. ${ub.showIn(ctx, 0)}"
    case AppliedType(n, args) => s"${n.name}[${args.map(_.showIn(ctx, 0)).mkString(", ")}]"
    case Rem(b, ns) => s"${b.showIn(ctx, 90)}${ns.map("\\"+_).mkString}"
    case Literal(IntLit(n)) => n.toString
    case Literal(DecLit(n)) => n.toString
    case Literal(StrLit(s)) => "\"" + s + "\""
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Bounds(l, r) => l :: r :: Nil
    case Neg(b) => b :: Nil
    case Record(fs) => fs.map(_._2)
    case Tuple(fs) => fs.map(_._2)
    case Union(l, r) => l :: r :: Nil
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
    case AppliedType(n, ts) => ts
    case Rem(b, _) => b :: Nil
    case WithExtension(b, r) => b :: r :: Nil
  }
  
  /** Converts a term to its typescript type declarations, including
    * any new type aliases created in order to represent it's type
    *
    * @param termName name of term that's been declared. If none is given
    *                 default "res" is used to indicate type of value of result
    *                 from evaluating the term
    * @return
    */
  def toTsTypeSourceCode(termName: Option[String] = None): SourceCode = {
    val ctx = ToTsTypegenContext.empty;
    
    // Create a mapping from type var to their friendly name for lookup
    // Also add them as type parameters to the current type because typescript
    // uses parametric polymorphism
    ctx.existingTypeVars = ShowCtx.mk(this :: Nil, "t").vs;
    val tsType = this.toTsType(ctx);
    
    ctx.newTypeParams = ctx.newTypeParams ++ ctx.existingTypeVars.map(tup => SourceCode(tup._2));
    val completeTypegenStatement = termName match {
      // term definitions bound to names are exported
      // as declared variables with their derived types
      case S(name) =>
        SourceCode("// start ts") +
        SourceCode.concat(ctx.newTypeAlias) +
        (SourceCode(s"export declare const $name") ++
          SourceCode.paramList(ctx.newTypeParams) ++
          SourceCode.colon ++
          tsType
        ) +
        SourceCode("// end ts")
      // terms definitions not bound to names are not exported by default
      // they are bound to an implicit res variable and the type of res
      // is shown here
      case N =>
        SourceCode("// start ts") +
        SourceCode.concat(ctx.newTypeAlias) +
        (SourceCode(s"type res") ++
          SourceCode.paramList(ctx.newTypeParams) ++
          SourceCode.equalSign ++
          tsType
        ) +
        SourceCode("// end ts")
    }
      
    completeTypegenStatement
  }

  /**
    * Converts an mlscript type to source code representation of a ts type. It also
    * keep tracks of extra type variables and type parameters defined through the context.
    *
    * Takes a context to maintain state.
    * @param ctx
    * @return
    */
  def toTsType(implicit ctx: ToTsTypegenContext = ToTsTypegenContext.empty): SourceCode = {
    this match {
      // these types can be inferred from expression that do not need to be
      // assigned to a variable
      case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) => SourceCode("boolean")
      case Union(lhs, rhs) => SourceCode.sepBy(List(lhs.toTsType, rhs.toTsType), SourceCode.separator)
      case Inter(lhs, rhs) => SourceCode.sepBy(List(lhs.toTsType, rhs.toTsType), SourceCode.ampersand)
      case Record(fields) => SourceCode.recordWithEntries(fields.map(entry => (SourceCode(entry._1.name), entry._2.toTsType)))
      // unwrap extra parenthesis when tuple has single element
      case Tuple(fields) => if (fields.length === 1) {
        fields(0)._2.toTsType
      } else {
        SourceCode.horizontalArray(fields.map(field => field._2.toTsType))
      }
      case Top => SourceCode("unknown")
      case Bot => SourceCode("never")
      case TypeName(name) => SourceCode(name)
      case Literal(IntLit(n)) => SourceCode(n.toString + (if (JSBackend isSafeInteger n) "" else "n"))
      case Literal(DecLit(n)) => SourceCode(n.toString)
      case Literal(StrLit(s)) => SourceCode(JSLit.makeStringLiteral(s))
      
      // the below types are inferred from expressions that need to be assigned to variables or definitions
      // or require information from previous declarations to be completed
      
      // typescript function types must have a named parameter
      // e.g. (val: number) => string
      case Function(lhs, rhs) =>
        {
          val currArgCount = ctx.argCounter;
          val currPolarity = ctx.polarity;
          
          ctx.argCounter += 1;
          ctx.multiplyPolarity(false)
          val lhsTypeSource = lhs.toTsType;
          ctx.polarity = currPolarity;
          
          ctx.multiplyPolarity(true)
          val rhsTypeSource = rhs.toTsType;
          
          (SourceCode(s"arg${currArgCount}") ++ SourceCode.colon ++ lhsTypeSource).parenthesized ++
          SourceCode.fatArrow ++
          rhsTypeSource
        }
      // a recursive type is wrapped in a self referencing Recursion type
      // this wrapped form is used only inside it's body
      case Recursive(uv, body) => {
        val uvTsType = uv.toTsType
        
        // use modified context for converting body type. This will replace
        // all use of uv type var with it's wrapped type.
        ctx.newTypeAlias = (SourceCode("type ") ++ uvTsType ++
          SourceCode.equalSign ++ body.toTsType) +: ctx.newTypeAlias
          
        // recursive type is no longer a type variable it's an alias instead
        ctx.existingTypeVars = ctx.existingTypeVars.removed(uv)
        
        uvTsType
      }
      // this occurs when polymorphic types (usually classes) are applied
      case AppliedType(base, targs) => if (targs.length =/= 0) {
          SourceCode(base.name) ++ SourceCode.openAngleBracket ++ SourceCode.sepBy(targs.map(_.toTsType)) ++ SourceCode.closeAngleBracket
        } else {
          // no type arguments required then print without brackets
          SourceCode(base.name)
        }
      // Neg requires creating a parameterized type alias to hold the negated definition
      case Neg(base) => {
        val typeParam = s"T${ctx.argCounter}";
        ctx.argCounter += 1;
        val typeAliasName = s"talias${ctx.argCounter}<$typeParam>"
        ctx.argCounter += 1;
        val typeAlias = s"type $typeAliasName = $typeParam extends ${base.toTsType} ? never : $typeParam"
        
        ctx.newTypeParams = SourceCode(typeParam) +: ctx.newTypeParams;
        ctx.newTypeAlias = SourceCode(typeAlias) +: ctx.newTypeAlias;
        SourceCode(typeAliasName)
      }
      case Rem(base, names) => SourceCode("Omit") ++
        SourceCode.openAngleBracket ++ base.toTsType ++ SourceCode.commaSpace ++
        SourceCode.record(names.map(name => SourceCode(name.name))) ++ SourceCode.closeAngleBracket
      case Bounds(lb, ub) => {
        ctx.polarity match {
          // positive polarity takes upper bound
          case Some(true) => {
            ub.toTsType
          }
          // negative polarity takes lower bound
          case Some(false) => {
            lb.toTsType
          }
          // TODO: Yet to handle invariant types
          case None => {
            SourceCode("TODO") ++ lb.toTsType ++ ub.toTsType
          }
        }
      }
      case WithExtension(base, rcd) => Inter(Rem(base, rcd.fields.map(tup => tup._1)), rcd).toTsType
      // type variables friendly names have been pre-calculated in the context
      // look up and use it or return a NOT FOUND marker
      case t@TypeVar(_, _) => {
        ctx.existingTypeVars.get(t).map(s => SourceCode(s)).getOrElse(SourceCode("NOT FOUND"))
      }
    }
  }
}

final case class ShowCtx(vs: Map[TypeVar, Str], debug: Bool) // TODO make use of `debug` or rm
object ShowCtx {
  /**
    * Create a context from a list of types. For named variables and
    * hinted variables use what is given. For unnamed variables generate
    * completely new names. If same name exists increment counter suffix
    * in the name.
    *
    * @param tys
    * @param pre
    * @param debug
    * @return
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
    // generate names for unnamed variables
    val names = Iterator.unfold(0) { idx =>
      S(('a' + idx % ('z' - 'a')).toChar.toString, idx + 1)
    }.filterNot(used).map(assignName)
    ShowCtx(namedMap ++ unnamedVars.zip(names), debug)
  }
}

abstract class PolyTypeImpl extends Located { self: PolyType =>
  def children: List[Located] =  targs :+ body
  def show: Str = s"${targs.iterator.map(_.name).mkString("[", ", ", "] ->")} ${body.show}"
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
    case Tup(xs) => "tuple"
    case Bind(l, r) => "'as' binding"
    case Test(l, r) => "'is' test"
    case With(t, fs) =>  "`with` extension"
    case CaseOf(scrut, cases) =>  "`case` expression" 
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
      fields.iterator.map(nv => nv._1.name + ": " + nv._2).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => receiver.toString + "." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"(let${if (isRec) " rec" else ""} $name = $rhs; $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) => n.fold("")(_.name + ": ") + t + "," }.mkString("(", " ", ")")
    case Bind(l, r) => s"($l as $r)"
    case Test(l, r) => s"($l is $r)"
    case With(t, fs) =>  s"$t with $fs"
    case CaseOf(s, c) => s"case $s of $c"
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
  def baseClasses: Set[Var] = this match {
    case _: IntLit => Set.single(Var("int")) + Var("number")
    case _: StrLit => Set.single(Var("string"))
    case _: DecLit => Set.single(Var("number"))
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
        case N -> d => d
        case S(n) -> d => ???
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
                case (S(n) -> t) =>
                  val ty = t.toType match {
                    case L(d) => allDiags += d; Top
                    case R(t) => t
                  }
                  fields += n -> ty
                  n -> ty
                case _ => ???
              }) :: Nil
            case Bra(true, t) => lastWords(s"$t ${t.getClass}")
            case Tup(fs) => // TODO factor with case Bra(true, Tup(fs)) above
              Tuple(fs.map {
                case (S(n) -> t) =>
                  val ty = t.toType match {
                    case L(d) => allDiags += d; Top
                    case R(t) => t
                  }
                  fields += n -> ty
                  S(n) -> ty
                case _ => ???
              }) :: Nil
            case _ => ??? // TODO proper error
          }
          val params = args.flatMap(getFields)
          val clsNme = TypeName(v.name).withLocOf(v)
          val tps = tparams.toList
          val ctor = Def(false, v, R(PolyType(tps,
            params.foldRight(AppliedType(clsNme, tps):Type)(Function(_, _))))).withLocOf(stmt)
          val td = TypeDef(Cls, clsNme, tps, Record(fields.toList)).withLocOf(stmt)
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
    case Tup(fields) => fields.map(_._2)
    case Rcd(fields) => fields.map(_._2)
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
  }
  
  
  override def toString: String = this match {
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
