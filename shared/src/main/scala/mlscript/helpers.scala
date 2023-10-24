package mlscript

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}

import math.Ordered.orderingToOrdered

import mlscript.utils._, shorthands._


// Auxiliary definitions for types

trait SignatureImpl extends Located { self: Signature =>
  def children: List[Located] = members
}

trait TypeLikeImpl extends Located { self: TypeLike =>
  
  def showDbg2: Str = show(newDefs = true) // TODO more lightweight debug printing routine
  
  def show(newDefs: Bool): Str = showIn(ShowCtx.mk(this :: Nil, newDefs), 0)
  
  private def parensIf(str: Str, cnd: Boolean): Str = if (cnd) "(" + str + ")" else str
  private def showField(f: Field, ctx: ShowCtx): Str = f match {
    case Field(N, ub) => ub.showIn(ctx, 0)
    case Field(S(lb), ub) if lb === ub => ub.showIn(ctx, 0)
    case Field(S(Bot), ub) => s"out ${ub.showIn(ctx, 0)}"
    case Field(S(lb), Top) => s"in ${lb.showIn(ctx, 0)}"
    case Field(S(lb), ub) => s"in ${lb.showIn(ctx, 0)} out ${ub.showIn(ctx, 0)}"
  }
  private def showFields(fs: Ls[Opt[Var] -> Field], ctx: ShowCtx): Ls[Str] =
    fs.map(nt => s"${nt._2.mutStr}${nt._1.fold("")(_.name + ": ")}${showField(nt._2, ctx)}")
  def showIn(ctx: ShowCtx, outerPrec: Int): Str = this match {
  // TODO remove obsolete pretty-printing hacks
    case Top => "anything"
    case Bot => "nothing"
    case TypeName(name) => name
    // case uv: TypeVar => ctx.vs.getOrElse(uv, s"[??? $uv ???]")
    case TypeTag(name) => "#"+name
    case uv: TypeVar => ctx.vs(uv)
    case Recursive(n, b) => parensIf(s"${b.showIn(ctx, 2)} as ${ctx.vs(n)}", outerPrec > 1)
    case WithExtension(b, r) => parensIf(s"${b.showIn(ctx, 2)} with ${r.showIn(ctx, 0)}", outerPrec > 1)
    case Function(Tuple(fs), r) =>
      val innerStr = fs match {
        case Nil => "()"
        case N -> Field(N, f) :: Nil if !f.isInstanceOf[Tuple] => f.showIn(ctx, 31)
        case _ =>
          val inner = showFields(fs, ctx)
          if (ctx.newDefs) inner.mkString("(", ", ", ")") else inner.mkString("(", ", ", ",)")
      }
      parensIf(innerStr + " -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Function(l, r) if ctx.newDefs =>
      parensIf("(..." + l.showIn(ctx, 0) + ") -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Function(l, r) => parensIf(l.showIn(ctx, 31) + " -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Neg(t) => s"~${t.showIn(ctx, 100)}"
    case Record(fs) =>
      val strs = fs.map { nt =>
        val nme = nt._1.name
        if (nme.isCapitalized) nt._2 match {
          case Field(N | S(Bot), Top) => s"$nme"
          case Field(S(lb), ub) if lb === ub => s"$nme = ${ub.showIn(ctx, 0)}"
          case Field(N | S(Bot), ub) => s"$nme <: ${ub.showIn(ctx, 0)}"
          case Field(S(lb), Top) => s"$nme :> ${lb.showIn(ctx, 0)}"
          case Field(S(lb), ub) => s"$nme :> ${lb.showIn(ctx, 0)} <: ${ub.showIn(ctx, 0)}"
        }
        else s"${nt._2.mutStr}${nme}: ${showField(nt._2, ctx)}"
      }
      if (strs.foldLeft(0)(_ + _.length) > 80)
        strs.mkString("{\n" + ctx.indStr, ",\n" + ctx.indStr, "")
          .indentNewLines(ShowCtx.indentation) + "\n" + ctx.indStr + "}"
      else strs.mkString("{", ", ", "}")
    case Splice(fs) =>
      val inner = fs.map{case L(l) => s"...${l.showIn(ctx, 0)}" case R(r) => s"${showField(r, ctx)}"}
      if (ctx.newDefs) inner.mkString("[", ", ", "]") else inner.mkString("(", ", ", ")")
    case Tuple(fs) =>
      val inner = showFields(fs, ctx)
      if (ctx.newDefs) inner.mkString("[", ", ", "]")
      else inner.mkString("(", ", ", if (fs.nonEmpty) ",)" else ")")
    case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
      TypeName("bool").showIn(ctx, 0)
    // case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    // case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
    case c: Composed =>
      val prec = if (c.pol) 20 else 25
      val opStr = if (c.pol) " | " else " & "
      c.distinctComponents match {
        case Nil => (if (c.pol) Bot else Top).showIn(ctx, outerPrec)
        case x :: Nil => x.showIn(ctx, outerPrec)
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
    case AppliedType(n, args) =>
      s"${n.name}${args.map(_.showIn(ctx, 0)).mkString(ctx.<, ", ", ctx.>)}"
    case Selection(b, n) => b.showIn(ctx, 100) + "." + n.name
    case Rem(b, ns) => s"${b.showIn(ctx, 90)}${ns.map("\\"+_).mkString}"
    case Literal(IntLit(n)) => n.toString
    case Literal(DecLit(n)) => n.toString
    case Literal(StrLit(s)) => "\"" + s + "\""
    case Literal(UnitLit(b)) =>
      if (b) if (ctx.newDefs) "()" else "undefined" else "null"
    case PolyType(Nil, body) => body.showIn(ctx, outerPrec)
    case PolyType(targs, body) => parensIf(
        s"${targs.iterator.map(_.fold(_.name, _.showIn(ctx, 0)))
          .mkString("forall ", " ", ".")} ${body.showIn(ctx, 0)}",
        outerPrec > 1 // or 0?
      )
    case Constrained(b, bs, ws) =>
      val oldCtx = ctx
      val bStr = b.showIn(ctx, 0).stripSuffix("\n")
      val multiline = bStr.contains('\n')
      parensIf({
        val ctx = if (multiline) oldCtx.indent else oldCtx.indent.indent
        s"${
          bStr
        }\n${oldCtx.indStr}${if (multiline) "" else "  "}where${
              bs.map {
          case (uv, Bounds(Bot, ub)) =>
            s"\n${ctx.indStr}${ctx.vs(uv)} <: ${ub.showIn(ctx, 0)}"
          case (uv, Bounds(lb, Top)) =>
            s"\n${ctx.indStr}${ctx.vs(uv)} :> ${lb.showIn(ctx, 0)}"
          case (uv, Bounds(lb, ub)) if lb === ub =>
            s"\n${ctx.indStr}${ctx.vs(uv)} := ${lb.showIn(ctx, 0)}"
          case (uv, Bounds(lb, ub)) =>
            val vstr = ctx.vs(uv)
            s"\n${ctx.indStr}${vstr             } :> ${lb.showIn(ctx, 0)}" +
            s"\n${ctx.indStr}${" " * vstr.length} <: ${ub.showIn(ctx, 0)}"
        }.mkString
      }${ws.map{
          case Bounds(lo, hi) => s"\n${ctx.indStr}${lo.showIn(ctx, 0)} <: ${hi.showIn(ctx, 0)}" // TODO print differently from bs?
        }.mkString}"
      }, outerPrec > 0)
    case fd @ NuFunDef(isLetRec, nme, snme, targs, rhs) =>
      s"${isLetRec match {
        case S(false) => if (fd.genField) "val" else "let"
        case S(true) => if (fd.genField) die else "let rec"
        case N => "fun"
      }}${snme.fold("")(" (" + _.name + ")")
      } ${nme.name}${targs.map(_.showIn(ctx, 0)).mkStringOr(", ", "[", "]")}${rhs match {
        case L(trm) => " = ..."
        case R(ty) => ": " + ty.showIn(ctx, 0)
      }}"
    case Signature(decls, res) =>
      (decls.map(ctx.indStr + _.showIn(ctx, 0) + "\n") ::: (res match {
        case S(ty) => ctx.indStr + ty.showIn(ctx, 0) + "\n" :: Nil
        case N => Nil
      })).mkString
    case NuTypeDef(kind @ Als, nme, tparams, params, ctor, sig, parents, sup, ths, body) =>
      assert(params.isEmpty, params)
      assert(ctor.isEmpty, ctor)
      assert(parents.isEmpty, parents)
      assert(sup.isEmpty, sup)
      assert(ths.isEmpty, ths)
      assert(body.entities.isEmpty, body)
      s"type ${nme.name}${tparams.map(_._2.showIn(ctx, 0)).mkStringOr(", ", "[", "]")} = ${
        sig.getOrElse(die).showIn(ctx, 0)}"
    case td @ NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, sup, ths, body) =>
      val bodyCtx = ctx.indent
      s"${td.declareLoc.fold("")(_ => "declare ")}${td.abstractLoc.fold("")(_ => "abstract ")}${kind.str} ${
        nme.name}${tparams.map(_._2.showIn(ctx, 0)).mkStringOr(", ", "[", "]")}${params match {
        case S(Tup(fields)) => s"(${fields.map {
          case (N, Fld(_, Asc(v: Var, ty))) => v.name + ": " + ty.showIn(ctx, 0)
          case (N | S(_), _) => lastWords("ill-formed type definition parameter")
        }.mkString(", ")})"
        case _ => ""
      }}${sig.fold("")(": " + _.showIn(bodyCtx, 0))}${parents match {
        case Nil => ""
        case ps => " extends " + ps.mkString(", ") // TODO pp parent terms...
      }}${if (body.entities.isEmpty && sup.isEmpty && ths.isEmpty) "" else
        " {\n" + sup.fold("")(s"${bodyCtx.indStr}super: " + _.showIn(bodyCtx, 0) + "\n") +
        ths.fold("")(s"${bodyCtx.indStr}this: " + _.showIn(bodyCtx, 0) + "\n") +
          body.entities.collect {
            case Constructor(params, body) => s"${bodyCtx.indStr}constructor(${params.fields.map {
              case N -> Fld(FldFlags.empty, Asc(Var(nme), ty)) => 
                s"${nme}: ${ty.showIn(bodyCtx, 0)}"
              case _ => lastWords("ill-formed constructor parameter")
            }.mkString(", ")})\n"
          }.mkString +
          Signature(body.entities.collect { case d: NuDecl => d }, N).showIn(bodyCtx, 0) +
            ctx.indStr + "}"
      }"
  }
  
  def childrenTypes: List[TypeLike] = this match {
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
    case Selection(b, nme) => b :: nme :: Nil
    case Rem(b, _) => b :: Nil
    case WithExtension(b, r) => b :: r :: Nil
    case PolyType(targs, body) => targs.map(_.fold(identity, identity)) :+ body
    case Splice(fs) => fs.flatMap{ case L(l) => l :: Nil case R(r) => r.in.toList ++ (r.out :: Nil) }
    case Constrained(b, bs, ws) => b :: bs.flatMap(c => c._1 :: c._2 :: Nil) ::: ws.flatMap(c => c.lb :: c.ub :: Nil)
    case Signature(xs, res) => xs ::: res.toList
    case NuFunDef(isLetRec, nme, snme, targs, rhs) => targs ::: rhs.toOption.toList
    case NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, sup, ths, body) =>
      // TODO improve this mess
      tparams.map(_._2) ::: params.getOrElse(Tup(Nil)).fields.collect {
        case (_, Fld(_, Asc(_, ty))) => ty
      } ::: sig.toList ::: sup.toList ::: ths.toList ::: Signature(body.entities.collect {
        case d: NuDecl => d
      }, N) :: Nil // TODO parents?
  }
  
  lazy val typeVarsList: List[TypeVar] = this match {
    case uv: TypeVar => uv :: Nil
    case Recursive(n, b) => n :: b.typeVarsList
    case _ => childrenTypes.flatMap(_.typeVarsList)
  }
  
  /**
    * @return
    *  set of free type variables in type
    */
  lazy val freeTypeVariables: Set[TypeVar] = this match {
    case Recursive(uv, body) => body.freeTypeVariables - uv
    case t: TypeVar => Set.single(t)
    case _ => childrenTypes.foldRight(Set.empty[TypeVar])((ty, acc) => ty.freeTypeVariables ++ acc)
  }
  
}

trait TypeImpl extends Located { self: Type =>
  
  def children: List[Located] = childrenTypes
  
  /**
    * Collect fields recursively during code generation.
    * Note that the type checker will reject illegal cases.
    */
  lazy val collectFields: Ls[Str] = this match {
    case Record(fields) => fields.map(_._1.name)
    case Inter(ty1, ty2) => ty1.collectFields ++ ty2.collectFields
    case _: Union | _: Function | _: Tuple | _: Recursive
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName 
        | _: Constrained | _ : Splice | _: TypeTag | _: PolyType | _: Selection =>
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
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot | _: PolyType
        | _: Literal | _: TypeVar | _: Constrained | _ : Splice | _: TypeTag
        | _: Selection =>
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
        | _: Neg | _: Rem | _: Bounds | _: WithExtension | Top | Bot | _: PolyType
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName | _: Constrained | _ : Splice | _: TypeTag
        | _: Selection =>
      Nil
  }
}


final case class ShowCtx(
    vs: Map[TypeVar, Str],
    debug: Bool, // TODO make use of `debug` or rm
    indentLevel: Int,
    newDefs: Bool,
    angletards: Bool = false,
  )
{
  lazy val indStr: Str = ShowCtx.indentation * indentLevel
  def lnIndStr: Str = "\n" + indStr
  def indent: ShowCtx = copy(indentLevel = indentLevel + 1)
  def < : Str = if (angletards) "<" else "["
  def > : Str = if (angletards) ">" else "]"
}
object ShowCtx {
  def indentation: Str = "  "
  /**
    * Create a context from a list of types. For named variables and
    * hinted variables use what is given. For unnamed variables generate
    * completely new names. If same name exists increment counter suffix
    * in the name.
    */
  def mk(tys: IterableOnce[TypeLike], newDefs: Bool, _pre: Str = "'", debug: Bool = false): ShowCtx = {
    val (otherVars, namedVars) = tys.iterator.toList.flatMap(_.typeVarsList).distinct.partitionMap { tv =>
      tv.identifier match { case L(_) => L(tv.nameHint -> tv); case R(nh) => R(nh -> tv) }
    }
    val (hintedVars, unnamedVars) = otherVars.partitionMap {
      case (S(nh), tv) => L(nh -> tv)
      case (N, tv) => R(tv)
    }
    val usedNames = MutMap.empty[Str, Int]
    def assignName(n: Str): Str = {
      val pre = if (n.startsWith("'") || n.startsWith(ExtrusionPrefix)) "" else _pre
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
    }
    val namedMap = (namedVars ++ hintedVars).map { case (nh, tv) =>
      // tv -> assignName(nh.dropWhile(_ === '\''))
      tv -> assignName(nh.stripPrefix(_pre))
    }.toMap
    val used = usedNames.keySet
    
    // * Generate names for unnamed variables
    val numLetters = 'z' - 'a' + 1
    val names = Iterator.unfold(0) { idx =>
      val postfix = idx/numLetters
      S(('a' + idx % numLetters).toChar.toString + (if (postfix === 0) "" else postfix.toString), idx + 1)
    }.filterNot(used).map(assignName)
    
    ShowCtx(namedMap ++ unnamedVars.zip(names), debug, indentLevel = 0, newDefs)
  }
}

trait PolyTypeImpl  { self: PolyType => }

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

trait TypeVarImpl extends Ordered[TypeVar] { self: TypeVar =>
  def name: Opt[Str] = identifier.toOption.orElse(nameHint)
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
      case NuFunDef(isLetRec, nme, _, tys, rhs) =>
        R(Def(isLetRec.getOrElse(true), nme, rhs, isLetRec.isEmpty))
      case _: Constructor => die
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
    case Def(_, _, rhs, isByname) => rhs.fold(_.toString, _.showDbg2)
    case td: TypeDef => td.body.showDbg2
  }
  def describe: Str = this match {
    case _: Def => "definition"
    case _: TypeDef => "type declaration"
  }
  def showDbg: Str = showHead + (this match {
    case TypeDef(Als, _, _, _, _, _, _, _) => " = "; case _ => ": " }) + showBody
  def showHead: Str = this match {
    case Def(true, n, b, isByname) => s"rec def $n"
    case Def(false, n, b, isByname) => s"def $n"
    case TypeDef(k, n, tps, b, _, _, pos, _) =>
      s"${k.str} ${n.name}${if (tps.isEmpty) "" else tps.map(_.name).mkString("[", ", ", "]")}${
        if (pos.isEmpty) "" else pos.mkString("(", ", ", ")")
      }"
  }
}

trait NuDeclImpl extends Located { self: NuDecl =>
  val body: Located
  def kind: DeclKind
  val declareLoc: Opt[Loc]
  val abstractLoc: Opt[Loc]
  def isDecl: Bool = declareLoc.nonEmpty
  def isAbstract: Bool = abstractLoc.nonEmpty
  def declStr: Str = if (isDecl) "declare " else ""
  val nameVar: Var = self match {
    case td: NuTypeDef => td.nme.toVar
    case fd: NuFunDef => fd.nme
  }
  def name: Str = nameVar.name
  def showBody: Str = this match {
    case NuFunDef(_, _, _, _, rhs) => rhs.fold(_.toString, _.showDbg2)
    case td: NuTypeDef => td.body.showDbg
  }
  def describe: Str = this match {
    case _: NuFunDef => "definition"
    case _: NuTypeDef => "type declaration"
  }
  def showDbg: Str = showHead + (this match {
    case NuFunDef(_, _, _, _, L(_)) => " = "
    case NuFunDef(_, _, _, _, R(_)) => ": "
    case _: NuTypeDef => " "
  }) + showBody
  def showHead: Str = this match {
    case NuFunDef(N, n, snme, _, b) => s"fun${snme.fold("")(" ("+_+")")} $n"
    case NuFunDef(S(false), n, snme, _, b) => s"let${snme.fold("")(" "+_+")")} $n"
    case NuFunDef(S(true), n, snme, _, b) => s"let rec${snme.fold("")(" "+_+")")} $n"
    case NuTypeDef(k, n, tps, sps, ctor, sig, parents, sup, ths, bod) =>
      s"${k.str} ${n.name}${if (tps.isEmpty) "" else tps.map(_._2.name).mkString("‹", ", ", "›")}${
          sps.fold("")("(" + _.showElems + ")")
        }${sig.fold("")(": " + _.showDbg2)}${
          if (parents.isEmpty) "" else if (k === Als) " = " else ": "}${parents.mkString(", ")}"
  }
  lazy val genUnapply: Opt[NuFunDef] = this match {
    case td: NuTypeDef if td.kind is Cls => td.params.map { tup =>
      val ret = Let(false, Var("_"), Asc(Var("x"), TypeName(name)), Tup(tup.fields.map {
        case S(p) -> f => N -> Fld(FldFlags.empty, Sel(Var("x"), Var("#" + p.name).withLocOf(p)))
        case N -> Fld(flags, p: Var) => N -> Fld(FldFlags.empty, Sel(Var("x"), Var("#" + p.name).withLocOf(p)))
        case _ => die
      }))
      NuFunDef(N, Var("unapply"), N, Nil, L(Lam(
        Tup(N -> Fld(FldFlags.empty, Var("x")) :: Nil),
        ret)))(N, N, N, N, true)
    }
    case _ => N
  }
}

trait TypingUnitImpl extends Located { self: TypingUnit =>
  def showDbg: Str = entities.map {
    case t: Term => t.toString
    case d: NuDecl => d.showDbg
    case c: Constructor => c.toString
    case e => lastWords(s"Unexpected typing unit entity: $e")
  }.mkString("{", "; ", "}")
  override def toString: String = s"‹${entities.mkString("; ")}›"
  lazy val children: List[Located] = entities

  def showIn(ctx: ShowCtx): Str = {
    val newCtx = ctx.indent
    entities.map{
      case t: Term => t.showIn(newCtx, false)
      case nd: NuDecl => nd.show(newCtx.newDefs)
      case s if !ctx.newDefs => s.toString
      case _ => ???
    }.mkString("{" + newCtx.lnIndStr, newCtx.lnIndStr, ctx.lnIndStr + "}")
  }
}

trait ConstructorImpl { self: Constructor =>
  // def children: List[Located] = fields.map(_._2)
  def describe: Str = "constructor"
  // def showDbg: Str = s"constructor(${fields.map(_._1.name).mkString(", ")})"
}

trait TypeNameImpl extends Ordered[TypeName] { self: TypeName =>
  def base: TypeName = this
  def targs: Ls[Type] = Nil
  def compare(that: TypeName): Int = this.name compare that.name
  lazy val toVar: Var = Var(name).withLocOf(this)
}

trait FldImpl extends Located { self: Fld =>
  def children: Ls[Located] = self.value :: Nil
  def describe: Str =
    (if (self.flags.spec) "specialized " else "") +
    (if (self.flags.mut) "mutable " else "") +
    self.value.describe
}

trait TermImpl extends StatementImpl { self: Term =>
  val original: this.type = this
  
  /** Used by code generation when the typer desugars this term into a different term. */
  var desugaredTerm: Opt[Term] = N  
  
  private var sugaredTerm: Opt[Term] = N

  def desugaredFrom(term: Term): this.type = {
    sugaredTerm = S(term)
    withLocOf(term)
  }
  
  def describe: Str = sugaredTerm match {
    case S(t) => t.describe
    case N => this match {
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
      case Tup((N, Fld(_, x)) :: Nil) => x.describe
      case Tup((S(_), x) :: Nil) => "binding"
      case Tup(xs) => "tuple"
      case Bind(l, r) => "'as' binding"
      case Test(l, r) => "'is' test"
      case With(t, fs) =>  "`with` extension"
      case CaseOf(scrut, cases) =>  "`case` expression" 
      case Subs(arr, idx) => "array access"
      case Assign(lhs, rhs) => "assignment"
      case Splc(fs) => "splice"
      case New(h, b) => "object instantiation"
      case If(_, _) => "if-else block"
      case TyApp(_, _) => "type application"
      case Where(_, _) => s"constraint clause"
      case Forall(_, _) => s"forall clause"
      case Inst(bod) => "explicit instantiation"
      case Super() => "super"
      case Eqn(lhs, rhs) => "assign for ctor"
      case AdtMatchWith(cond, arms) => "ADT pattern matching"
      case Quoted(_) => "quasiquote"
      case Unquoted(_) => "unquote"
    }
  }
  
  override def toString: Str = print(false)

  def print(brackets: Bool): Str = {
      def bra(str: Str): Str = if (brackets) s"($str)" else str
      this match {
    case Bra(true, trm) => s"'{' $trm '}'"
    case Bra(false, trm) => s"'(' $trm ')'"
    case Blk(stmts) => stmts.mkString("{", "; ", "}")
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if (value) "undefined" else "null"
    case v @ Var(name) => name + v.uid.fold("")("::"+_.toString)
    case Asc(trm, ty) => s"$trm : ${ty.showDbg2}"  |> bra
    case Lam(pat: Tup, rhs) => s"(${pat.showElems}) => $rhs" |> bra
    case Lam(pat, rhs) => s"(...$pat) => $rhs" |> bra
    case App(lhs, rhs: Tup) => s"${lhs.print(!lhs.isInstanceOf[App])}(${rhs.showElems})" |> bra
    case App(lhs, rhs) => s"${lhs.print(!lhs.isInstanceOf[App])}(...${rhs.print(true)})" |> bra
    case Rcd(fields) =>
      fields.iterator.map(nv =>
        (if (nv._2.flags.mut) "mut " else "") + nv._1.name + ": " + nv._2.value).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => "(" + receiver.toString + ")." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"let${if (isRec) " rec" else ""} $name = $rhs in $body" |> bra
    case tup: Tup => "[" + tup.showElems + "]"
    case Splc(fields) => fields.map{
      case L(l) => s"...$l"
      case R(Fld(FldFlags(m, s, g), r)) => (
        (if (m) "mut " else "")
        + (if (g) "val " else "")
        + (if (s) "#" else "")
        + r
      )
    }.mkString("(", ", ", ")")
    case Bind(l, r) => s"$l as $r" |> bra
    case Test(l, r) => s"$l is $r" |> bra
    case With(t, fs) =>  s"$t with $fs" |> bra
    case CaseOf(s, c) =>
      s"case $s of { ${c.print(true)} }" |> bra
    case Subs(a, i) => s"($a)[$i]"
    case Assign(lhs, rhs) => s" $lhs <- $rhs" |> bra
    case New(S((at, ar)), bod) => s"new ${at.showDbg2}($ar) ${bod.showDbg}" |> bra
    case New(N, bod) => s"new ${bod.showDbg}" |> bra
    case If(body, els) => s"if $body" + els.fold("")(" else " + _) |> bra
    case TyApp(lhs, targs) => s"$lhs‹${targs.map(_.showDbg2).mkString(", ")}›"
    case Where(bod, wh) => s"${bod} where {${wh.mkString("; ")}}"
    case Forall(ps, bod) => s"forall ${ps.mkString(", ")}. ${bod}"
    case Inst(bod) => s"${bod.print(true)}!"
    case Super() => "super"
    case Eqn(lhs, rhs) => s"${lhs} = ${rhs}"
    case AdtMatchWith(cond, arms) =>
      s"match ${cond} with ${arms.map (patmat => s"${patmat.pat} -> ${patmat.rhs}").mkString (" | ") }"
    case Quoted(b) => s"code\"$b\""
    case Unquoted(b) => s"$${$b}"
  }}

  def show(newDefs: Bool): Str = showIn(ShowCtx.mk(Nil, newDefs), false)
  def showIn(ctx: ShowCtx, brackets: Bool): Str = {
    def bra(str: Str): Str = if (brackets) s"($str)" else str
    this match {
      case Bra(true, trm) => trm.showIn(ctx, false)
      case Bra(false, trm) => s"(${trm.showIn(ctx, false)})"
      case Blk(stmts) =>
        val newCtx = ctx.indent
        stmts.map {
          case t: Term => t.showIn(newCtx, false)
          case nd: NuDecl => nd.show(newCtx.newDefs)
          case s if !ctx.newDefs => s.toString
          case _ => ???
        }.mkString("{" + newCtx.lnIndStr, newCtx.lnIndStr, ctx.indStr + "\n}")
      case IntLit(value) => value.toString
      case DecLit(value) => value.toString
      case StrLit(value) => '"'.toString + value + '"'
      case UnitLit(value) => if (ctx.newDefs) "()" else if (value) "undefined" else "null"
      case Var(name) => name
      case Asc(trm, ty) => s"$trm : ${ty.show(ctx.newDefs)}" |> bra
      case Lam(pat: Tup, rhs) => s"(${pat.showIn(ctx)}) => ${rhs.showIn(ctx, false)}" |> bra
      case Lam(pat, rhs) => s"(...${pat.showIn(ctx, false)}) => ${rhs.showIn(ctx, false)}" |> bra
      case App(lhs, rhs: Tup) => s"${lhs.showIn(ctx, !lhs.isInstanceOf[App])}(${rhs.showIn(ctx)})" |> bra
      case App(lhs, rhs) => s"${lhs.showIn(ctx, !lhs.isInstanceOf[App])}(...${rhs.showIn(ctx, true)})" |> bra
      case Rcd(fields) =>
        val newCtx = ctx.indent
        fields.iterator.map(nv =>
          (if (nv._2.flags.mut) "mut " else "") + nv._1.name + ": " + nv._2.value.showIn(newCtx, false)).mkString("{" + newCtx.lnIndStr, "," + newCtx.lnIndStr, ctx.lnIndStr + "}")
      case Sel(receiver, fieldName) => receiver.showIn(ctx, !receiver.isInstanceOf[SimpleTerm]) + "." + fieldName
      case Let(isRec, name, rhs, body) =>
        s"let${if (isRec) " rec" else ""} ${name.showIn(ctx, false)} = ${rhs.showIn(ctx, false)} in ${body.showIn(ctx, false)}" |> bra
      case tup: Tup => "[" + tup.showIn(ctx) + "]"
      case Splc(fields) => fields.map{
        case L(l) => s"...${l.showIn(ctx, false)}"
        case R(Fld(FldFlags(m, s, g), r)) => (
          (if (m) "mut " else "")
          + (if (g) "val " else "")
          + (if (s) "#" else "")
          + r.showIn(ctx, false)
        )
      }.mkString("(", ", ", ")")
      case Bind(l, r) => s"${l.showIn(ctx, false)} as ${r.showIn(ctx, false)}" |> bra
      case Test(l, r) => s"${l.showIn(ctx, false)} is ${r.showIn(ctx, false)}" |> bra
      case With(t, fs) =>  s"${t.showIn(ctx, false)} with ${fs.showIn(ctx, false)}" |> bra
      case CaseOf(s, c) =>
        s"case ${s.showIn(ctx, false)} of {${c.showIn(ctx.indent)}${ctx.lnIndStr}}" |> bra
      case Subs(a, i) => s"(${a.showIn(ctx, false)})[${i.showIn(ctx, false)}]"
      case Assign(lhs, rhs) => s" ${lhs.showIn(ctx, false)} <- ${rhs.showIn(ctx, false)}" |> bra
      case New(S((at, ar)), bod) => s"new ${at.show(ctx.newDefs)}($ar) ${bod.showIn(ctx)}" |> bra
      case New(N, bod) => s"new ${bod.showIn(ctx)}" |> bra
      case If(body, els) => s"if ${body.showIn(ctx.indent)}" + els.fold("")(" else " + _.showIn(ctx.indent, false)) |> bra
      case TyApp(lhs, targs) => s"${lhs.showIn(ctx, false)}${ctx.<}${targs.map(_.show(ctx.newDefs)).mkString(", ")}${ctx.>}"
      case Where(bod, wh) => s"${bod.showIn(ctx, false)} where ${Blk(wh).showIn(ctx.indent, false)}"
      case Forall(ps, bod) => s"forall ${ps.map(_.show(ctx.newDefs)).mkString(", ")}. ${bod.showIn(ctx, false)}"
      case Inst(bod) => s"${bod.showIn(ctx, true)}!"
      case Super() => "super"
      case Eqn(lhs, rhs) => s"${lhs.showIn(ctx, false)} = ${rhs.showIn(ctx, false)}"
      case AdtMatchWith(cond, arms) =>
        s"match ${cond.showIn(ctx, false)} with ${arms.map (patmat => s"${patmat.pat.showIn(ctx, false)} -> ${patmat.rhs.showIn(ctx, false)}").mkString (" | ") }"
      case Quoted(b) => s"code\"${b.showIn(ctx, false)}\""
      case Unquoted(b) => s"$${${b.showIn(ctx, false)}}"
    }
  }
  
  def toTypeRaise(implicit raise: Raise): Type = toType match {
    case L(d) => raise(d); Bot
    case R(ty) => ty
  }
  def toType: Diagnostic \/ Type =
    try R(toType_!.withLocOf(this)) catch {
      case e: NotAType =>
        import Message._
        L(ErrorReport(msg"Not a recognized type" -> e.trm.toLoc::Nil, newDefs=true)) }
  protected def toType_! : Type = (this match {
    case Var(name) if name.startsWith("`") => TypeVar(R(name.tail), N)
    case Var(name) if name.startsWith("'") => TypeVar(R(name), N)
    case Var(name) => TypeName(name)
    case lit: Lit => Literal(lit)
    case App(Var("->"), PlainTup(lhs @ (_: Tup | Bra(false, _: Tup)), rhs)) =>
    // * ^ Note: don't think the plain _: Tup without a Bra can actually occur
      Function(lhs.toType_!, rhs.toType_!)
    case App(Var("->"), PlainTup(lhs, rhs)) =>
      Function(Tuple(N -> Field(N, lhs.toType_!) :: Nil), rhs.toType_!)
    case App(Var("|"), PlainTup(lhs, rhs)) =>
      Union(lhs.toType_!, rhs.toType_!)
    case App(Var("&"), PlainTup(lhs, rhs)) =>
      Inter(lhs.toType_!, rhs.toType_!)
    case ty @ App(v @ Var("\\"), PlainTup(lhs, rhs)) =>
      Inter(lhs.toType_!, Neg(rhs.toType_!).withLoc(Loc(v :: rhs :: Nil))).withLoc(ty.toCoveringLoc)
    case App(Var("~"), rhs) => Neg(rhs.toType_!)
    case Lam(lhs, rhs) => Function(lhs.toType_!, rhs.toType_!)
    case App(lhs, PlainTup(fs @ _*)) =>
      lhs.toType_! match {
        case tn: TypeName => AppliedType(tn, fs.iterator.map(_.toType_!).toList)
        case _ => throw new NotAType(this)
      }
    case Tup(fields) => Tuple(fields.map(fld => (fld._1, fld._2 match {
      case Fld(FldFlags(m, s, _), v) => val ty = v.toType_!; Field(Option.when(m)(ty), ty)
    })))
    case Bra(rcd, trm) => trm match {
      case _: Rcd => if (rcd) trm.toType_! else throw new NotAType(this)
      case _ => if (!rcd) trm.toType_! else throw new NotAType(this)
    }
    case TyApp(lhs, targs) => lhs.toType_! match {
      case p: TypeName => AppliedType(p, targs)
      case _ => throw new NotAType(this)
    }
    case Rcd(fields) => Record(fields.map(fld => (fld._1, fld._2 match {
      case Fld(FldFlags(m, s, _), v) => val ty = v.toType_!; Field(Option.when(m)(ty), ty)
    })))
    case Where(body, where) =>
      Constrained(body.toType_!, Nil, where.map {
        case Asc(l, r) => Bounds(l.toType_!, r)
        case s => throw new NotAType(s)
      })
    case Forall(ps, bod) =>
      PolyType(ps.map(R(_)), bod.toType_!)
    // 
    case Sel(receiver, field) =>
      Selection(receiver.toType_!, TypeName(field.name).withLocOf(field))
    // case Sel(receiver, fieldName) => receiver match {
    //   case Var(name) if !name.startsWith("`") => TypeName(s"$name.$fieldName")
    //   case _ => throw new NotAType(this)
    // }
    // TODO:
    // case Let(isRec, name, rhs, body) => ???
    // case Blk(stmts) => ???
    // case Asc(trm, ty) => ???
    // case Bind(lhs, rhs) => ???
    // case Test(trm, ty) => ???
    // case With(trm, fieldNme, fieldVal) => ???
    // case CaseOf(trm, cases) => ???
    case _ => throw new NotAType(this)
  }).withLocOf(this)
  
}
private class NotAType(val trm: Statement) extends Throwable

object PlainTup {
  def apply(fields: Term*): Term =
    Tup(fields.iterator.map(t => (N, Fld(FldFlags.empty, t))).toList)
  def unapplySeq(trm: Term): Opt[List[Term]] = trm match {
    case Tup(fields) if fields.forall(f =>
      f._1.isEmpty && f._2.flags.mut === false && f._2.flags.spec === false
    ) => S(fields.map(_._2.value))
    case _ => N
  }
}

trait LitImpl { self: Lit =>
  def baseClassesOld: Set[TypeName] = this match {
    case _: IntLit => Set.single(TypeName("int")) + TypeName("number")
    case _: StrLit => Set.single(TypeName("string"))
    case _: DecLit => Set.single(TypeName("number"))
    case _: UnitLit => Set.empty
  }
  def baseClassesNu: Set[TypeName] = this match {
    case _: IntLit => Set.single(TypeName("Int")) + TypeName("Num") + TypeName("Object")
    case _: StrLit => Set.single(TypeName("Str")) + TypeName("Object")
    case _: DecLit => Set.single(TypeName("Num")) + TypeName("Object")
    case _: UnitLit => Set.single(TypeName("Object"))
  }
}

trait VarImpl { self: Var =>
  def isPatVar: Bool =
    (name.head.isLetter && name.head.isLower || name.head === '_' || name.head === '$') && name =/= "true" && name =/= "false"
  def toVar: Var = this
  var uid: Opt[Int] = N
}

trait TupImpl { self: Tup =>
  def showElems: Str =
    fields.iterator.map { case (n, t) => (
      (if (t.flags.mut) "mut " else "")
      + (if (t.flags.genGetter) "val " else "")
      + (if (t.flags.spec) "#" else "")
      + n.fold("")(_.name + ": ") + t.value + ","
    )}.mkString(" ")

  def showIn(ctx: ShowCtx): Str =
    fields.iterator.map { case (n, t) => (
      (if (t.flags.mut) "mut " else "")
      + (if (t.flags.genGetter) "val " else "")
      + (if (t.flags.spec) "#" else "")
      + n.fold("")(_.name + ": ") + t.value.showIn(ctx, false)
    )}.mkString(", ")
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
  
  lazy val freeVars: Set[Var] = this match {
    case v: Var => Set.single(v)
    case _ => children.iterator.flatMap(_.freeVars.iterator).toSet
  }
  
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
  private[mlscript] def getLoc: Opt[Loc] = {
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
    // case ctor: Constructor =>
    //   import Message._
    //   (ErrorReport(msg"constructor must be in a class." -> ctor.toLoc :: Nil, newDefs=true) :: Nil) -> Nil
    case l @ LetS(isrec, pat, rhs) =>
      val (diags, v, args) = desugDefnPattern(pat, Nil)
      diags -> (Def(isrec, v, L(args.foldRight(rhs)(Lam(_, _))), false).withLocOf(l) :: Nil) // TODO use v, not v.name
    case d @ DataDefn(body) => desugarCases(body :: Nil, Nil)
    case d @ DatatypeDefn(hd, bod) =>
      val (diags, v, args) = desugDefnPattern(hd, Nil)
      val (diags3, targs) = args.partitionMap {
        case v @ Var(nme) => R(TypeName(nme).withLocOf(v))
        case t =>
          import Message._
          L(ErrorReport(msg"illegal datatype type parameter shape: ${t.toString}" -> t.toLoc :: Nil, newDefs=false))
      }
      val (diags2, cs) = desugarCases(bod, targs)
      val dataDefs = cs.collect{case td: TypeDef => td}
      (diags ::: diags2 ::: diags3) -> (TypeDef(Als, TypeName(v.name).withLocOf(v), targs,
          dataDefs.map(td => AppliedType(td.nme, td.tparams)).reduceOption(Union).getOrElse(Bot), Nil, Nil, Nil, N
        ).withLocOf(hd) :: cs)
    case NuTypeDef(Mod, nme, tps, tup, ctor, sig, pars, sup, ths, unit) =>
      ??? // TODO
    case NuTypeDef(Mxn, nme, tps, tup, ctor, sig, pars, sup, ths, unit) =>
      ??? // TODO
    case NuTypeDef(k @ Als, nme, tps, tup, ctor, sig, pars, sup, ths, unit) =>
      // TODO properly check:
      require(tup.forall(tup => tup.fields.isEmpty), tup)
      require(pars.size === 0, pars)
      require(sig.isDefined)
      require(ths.isEmpty, ths)
      require(unit.entities.isEmpty, unit)
      Nil -> (TypeDef(k, nme, tps.map(_._2), sig.getOrElse(die), Nil, Nil, Nil, N) :: Nil)
    case NuTypeDef(k @ (Cls | Trt), nme, tps, opt, ctor, sig, pars, sup, ths, unit) =>
      val tup = opt.getOrElse(Tup(Nil))
      val fs = tup.fields
      val diags = Buffer.empty[Diagnostic]
      def tt(trm: Term): Type = trm.toType match {
        case L(ds) => diags += ds; Top
        case R(ty) => ty
      }
      val params = fs.map {
        case (S(nme), Fld(FldFlags(mut, spec, _), trm)) =>
          val ty = tt(trm)
          nme -> Field(if (mut) S(ty) else N, ty)
        case (N, Fld(FldFlags(mut, spec, _), nme: Var)) => nme -> Field(if (mut) S(Bot) else N, Top)
        case _ => die
      }
      val pos = params.unzip._1
      val bod = pars.map(tt).foldRight(Record(params): Type)(Inter)
      val termName = Var(nme.name).withLocOf(nme)
      val ctor = Def(false, termName, L(Lam(tup, App(termName, Tup(N -> Fld(FldFlags.empty, Rcd(fs.map {
        case (S(nme), fld) => nme -> Fld(FldFlags(false, false, fld.flags.genGetter), nme)
        case (N, fld @ Fld(_, nme: Var)) => nme -> fld
        case _ => die
      })) :: Nil)))), true)
      diags.toList -> (TypeDef(k, nme, tps.map(_._2), bod, Nil, Nil, pos, N) :: ctor :: Nil)
    case d: DesugaredStatement => Nil -> (d :: Nil)
  }
  import Message._
  protected def desugDefnPattern(pat: Term, args: Ls[Term]): (Ls[Diagnostic], Var, Ls[Term]) = pat match {
    case App(l, r) => desugDefnPattern(l, r :: args)
    case v: Var => (Nil, v, args)
    case _ => (ErrorReport(msg"Unsupported pattern shape" -> pat.toLoc :: Nil, newDefs=true) :: Nil, Var("<error>"), args) // TODO
  }
  protected def desugarCases(bod: Term, baseTargs: Ls[TypeName]): (Ls[Diagnostic], Ls[Decl]) = bod match {
    case Blk(stmts) => desugarCases(stmts, baseTargs)
    case Tup(comps) =>
      val stmts = comps.map {
        case N -> Fld(_, d) => d
        case S(n) -> Fld(_, d) => ???
      }
      desugarCases(stmts, baseTargs)
    case _ => (ErrorReport(msg"Unsupported data type case shape" -> bod.toLoc :: Nil, newDefs=true) :: Nil, Nil)
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
                case (S(n) -> Fld(FldFlags(mut, _, _), t)) =>
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
                case (S(n) -> Fld(FldFlags(tmut, _, _), t)) =>
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
          val ctor = Def(false, v, R(PolyType(tps.map(L(_)),
            params.foldRight(AppliedType(clsNme, tps):Type)(Function(_, _)))), true).withLocOf(stmt)
          val td = TypeDef(Cls, clsNme, tps, Record(fields.toList.mapValues(Field(None, _))), Nil, Nil, Nil, N).withLocOf(stmt)
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
    case Tup(fields) => fields.map(_._2.value)
    case Rcd(fields) => fields.map(_._2.value)
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
    case d @ Def(_, n, b, _) => n :: d.body :: Nil
    case TypeDef(kind, nme, tparams, body, _, _, pos, _) => nme :: tparams ::: pos ::: body :: Nil
    case Subs(a, i) => a :: i :: Nil
    case Assign(lhs, rhs) => lhs :: rhs :: Nil
    case Splc(fields) => fields.map{case L(l) => l case R(r) => r.value}
    case If(body, els) => body :: els.toList
    case d @ NuFunDef(_, v, v2, ts, rhs) => v :: v2.toList ::: ts ::: d.body :: Nil
    case TyApp(lhs, targs) => lhs :: targs
    case New(base, bod) => base.toList.flatMap(ab => ab._1 :: ab._2 :: Nil) ::: bod :: Nil
    case Where(bod, wh) => bod :: wh
    case Forall(ps, bod) => ps ::: bod :: Nil
    case Inst(bod) => bod :: Nil
    case Super() => Nil
    case Constructor(params, body) => params :: body :: Nil
    case Eqn(lhs, rhs) => lhs :: rhs :: Nil
    case NuTypeDef(k, nme, tps, ps, ctor, sig, pars, sup, ths, bod) =>
      nme :: tps.map(_._2) ::: ps.toList ::: pars ::: ths.toList ::: bod :: Nil
    case AdtMatchWith(cond, _) => cond :: Nil // FIXME discards branches...
    case Quoted(body) => body :: Nil
    case Unquoted(body) => body :: Nil
  }
  
  
  override def toString: Str = this match {
    case LetS(isRec, name, rhs) => s"let${if (isRec) " rec" else ""} $name = $rhs"
    case DatatypeDefn(head, body) => s"data type $head of $body"
    case DataDefn(head) => s"data $head"
    case Constructor(params, bod) => s"constructor(${params.showElems}) $bod"
    case _: Term => super.toString
    case d: Decl => d.showDbg
    case d: NuDecl => d.showDbg
  }
}

trait BlkImpl { self: Blk =>
  def kind: Block.type = Block
  
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
  
  def print(isFirst: Bool): Str = this match {
    case Case(pat, body, rest) =>
      (if (isFirst) { "" } else { "; " }) +
      pat.print(false) + " => " + body.print(false) + rest.print(false)
    case Wildcard(body) => 
      (if (isFirst) { "" } else { "; " }) +
      "_ => " + body.print(false)
    case NoCases => ""
  }
  
  def showIn(ctx: ShowCtx): Str = this match {
    case Case(pat, body, rest) =>
      ctx.lnIndStr + pat.showIn(ctx, false) + " => " + body.showIn(ctx, false) + rest.showIn(ctx)
    case Wildcard(body) => 
      ctx.lnIndStr + "_ => " + body.showIn(ctx, false)
    case NoCases => ""
  }
}

trait AdtMatchPatImpl extends Located { self: AdtMatchPat =>
  def children: List[Located] = pat :: rhs :: Nil
  override def toString: String = s"($pat) then $rhs"
}

trait IfBodyImpl extends Located { self: IfBody =>
  
  def children: List[Located] = this match {
    case IfBlock(ts) => ts.map(_.fold(identity, identity))
    case IfThen(l, r) => l :: r :: Nil
    case IfElse(t) => t :: Nil
    case IfLet(_, v, r, b) => v :: r :: b :: Nil
    case IfOpApp(t, v, b) => t :: v :: b :: Nil
    case IfOpsApp(t, ops) => t :: ops.flatMap(x => x._1 :: x._2 :: Nil)
  }
  
  override def toString: String = this match {
    case IfThen(lhs, rhs) => s"($lhs) then $rhs"
    case IfElse(trm) => s"else $trm"
    case IfBlock(ts) => s"‹${ts.map(_.fold(identity, identity)).mkString("; ")}›"
    case IfOpApp(lhs, op, ib) => s"$lhs $op $ib"
    case IfOpsApp(lhs, ops) => s"$lhs ‹${ops.iterator.map{case(v, r) => s"· $v $r"}.mkString("; ")}›"
    case IfLet(isRec, v, r, b) => s"${if (isRec) "rec " else ""}let $v = $r in $b"
  }

  def showIn(ctx: ShowCtx): Str = this match {
    case IfThen(lhs, rhs) => s"${lhs.showIn(ctx, !lhs.isInstanceOf[SimpleTerm])} then ${rhs.showIn(ctx, false)}"
    case IfElse(trm) => s"else ${trm.showIn(ctx, false)}"
    case IfBlock(ts) => s"${ts.map(_.fold(identity, identity)).mkString(ctx.lnIndStr)}"
    case IfOpApp(lhs, op, ib) => s"${lhs.showIn(ctx, false)} ${op.showIn(ctx, false)} ${ib.showIn(ctx)}"
    case IfOpsApp(lhs, ops) => s"${lhs.showIn(ctx, false)} ${ops.iterator.map{case(v, r) => s"· $v $r"}.mkString(ctx.lnIndStr)}"
    case IfLet(isRec, v, r, b) => s"${if (isRec) "rec " else ""}let ${v.showIn(ctx, false)} = ${r.showIn(ctx, false)} in ${b.showIn(ctx)}"
  }
}

