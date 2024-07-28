package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.*


enum Term extends Statement with Located:
  case Error
  case Lit(lit: Literal)
  case Ref(sym: Symbol)(val refNum: Int)
  case App(lhs: Term, rhs: Term)(val resSym: FlowSymbol)
  case TyApp(lhs: Term, targs: Ls[Term])
  case Sel(prefix: Term, nme: Tree.Ident)
  case Tup(fields: Ls[Fld])
  case If(body: TermSplit)
  case Lam(params: Ls[Param], body: Term)
  case FunTy(lhs: Term, rhs: Term, eff: Opt[Term])
  case Forall(tvs: Ls[VarSymbol], body: Term)
  case WildcardTy(in: Opt[Term], out: Opt[Term])
  case Blk(stats: Ls[Statement], res: Term)
  case Quoted(body: Term)
  case Unquoted(body: Term)
  case New(cls: ClassSymbol, args: Ls[Term])
  case SelProj(prefix: Term, cls: Term, proj: Tree.Ident)
  case Asc(term: Term, ty: Term)
  case CompType(lhs: Term, rhs: Term, pol: Bool)
  case Region(name: VarSymbol, body: Term)
  case RegRef(reg: Term, value: Term)
  case Set(lhs: Term, rhs: Term)
  case Deref(ref: Term)
  
  var symbol: Opt[Symbol] = N
  
  // TODO how to handle cyclic defs?
  def resolveSymbol: Opt[Symbol] = symbol.orElse:
    val s = this match
      case Ref(sym) => S(sym)
      case Sel(pre, nme) =>
        pre.resolveSymbol match
          case S(mem: MemberSymbol) =>
            mem.defn match
            case S(d: ClassDef) =>
              ???
            case S(td: TermDefinition) =>
              ???
          case N => N
      case _ => N
    if s.isDefined then symbol = s
    s
  
  def describe: Str = ???
  def children: Ls[Located] = ???
import Term.*

sealed trait Statement extends Located:
  
  def subStatements: Ls[Statement] = this match
    case Blk(stats, res) => stats ::: res :: Nil
    case _ => subTerms
  def subTerms: Ls[Term] = this match
    case Error | _: Lit | _: Ref => Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case FunTy(lhs, rhs, eff) => lhs :: rhs :: eff.toList
    case TyApp(pre, tarsg) => pre :: tarsg
    case Sel(pre, _) => pre :: Nil
    case Tup(fields) => fields.map(_.value)
    case If(body) => Nil // TODO
    case Lam(params, body) => body :: Nil
    case Blk(stats, res) => stats.flatMap(_.subTerms) ::: res :: Nil
    case Quoted(term) => term :: Nil
    case Unquoted(term) => term :: Nil
    case New(_, args) => args
    case SelProj(pre, cls, _) => pre :: cls :: Nil
    case Asc(term, ty) => term :: ty :: Nil
    case Forall(_, body) => body :: Nil
    case WildcardTy(in, out) => in.toList ++ out.toList
    case CompType(lhs, rhs, _) => lhs :: rhs :: Nil
    case LetBinding(pat, rhs) => rhs :: Nil
    case Region(_, body) => body :: Nil
    case RegRef(reg, value) => reg :: value :: Nil
    case Set(lhs, rhs) => lhs :: rhs :: Nil
    case Deref(term) => term :: Nil
    case TermDefinition(k, _, ps, sign, body, res) =>
      ps.toList.flatMap(_.flatMap(_.subTerms)) ::: sign.toList ::: body.toList
    case cls: ClassDef =>
      cls.paramsOpt.toList.flatMap(_.flatMap(_.subTerms)) ::: cls.body.blk :: Nil
  
  def showDbg: Str = this match
    case r: Ref =>
      showPlain
    case trm: Term =>
      s"$showPlain‹${trm.symbol.getOrElse("")}›"
    case _ =>
      showPlain
  def showPlain: Str = this match
    case Lit(lit) => lit.idStr
    case r @ Ref(symbol) => symbol.toString+"#"+r.refNum
    case App(lhs, tup: Tup) => s"${lhs.showDbg}${tup.showDbg}"
    case App(lhs, rhs) => s"${lhs.showDbg}(...${rhs.showDbg})"
    case FunTy(lhs: Tup, rhs, eff) => s"${lhs.showDbg} ->${eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case FunTy(lhs, rhs, eff) => s"(...${lhs.showDbg}) ->${eff.map(e => s"{${e.showDbg}}").getOrElse("")} ${rhs.showDbg}"
    case TyApp(lhs, targs) => s"${lhs.showDbg}[${targs.mkString(", ")}]"
    case Forall(tvs, body) => s"forall ${tvs.mkString(", ")}: ${body.toString}"
    case WildcardTy(in, out) => s"in ${in.map(_.toString).getOrElse("⊥")} out ${out.map(_.toString).getOrElse("⊤")}"
    case Sel(pre, nme) => s"${pre.showDbg}.${nme.name}"
    case If(body) => s"if $body"
    case Lam(params, body) => s"λ${params.map(_.showDbg).mkString(", ")}. ${body.showDbg}"
    case Blk(stats, res) =>
      (stats.map(_.showDbg + "; ") :+ (res match { case Lit(Tree.UnitLit(true)) => "" case x => x.showDbg + " " }))
      .mkString("{ ", "", "}")
    case Quoted(term) => s"""code"${term.showDbg}""""
    case Unquoted(term) => s"$${${term.showDbg}}"
    case New(cls, args) => s"new ${cls.toString}(${args.mkString(", ")})"
    case SelProj(pre, cls, proj) => s"${pre.showDbg}.${cls.showDbg}#${proj.name}"
    case Asc(term, ty) => s"${term.toString}: ${ty.toString}"
    case LetBinding(pat, rhs) => s"let ${pat.showDbg} = ${rhs.showDbg}"
    case Region(name, body) => s"region ${name.nme} in ${body.showDbg}"
    case RegRef(reg, value) => s"(${reg.showDbg}).ref ${value.showDbg}"
    case Set(lhs, rhs) => s"${lhs.showDbg} := ${rhs.showDbg}"
    case Deref(term) => s"!$term"
    case CompType(lhs, rhs, pol) => s"${lhs.showDbg} ${if pol then "|" else "&"} ${rhs.showDbg}"
    case Error => "<error>"
    case Tup(fields) => fields.map(_.showDbg).mkString("(", ", ", ")")
    case TermDefinition(k, sym, ps, sign, body, res) => s"${k.str} ${sym}${
      ps.fold("")(_.map(_.showDbg).mkString("(", ", ", ")"))
    }${sign.fold("")(": "+_.showDbg)}${
      body match
        case S(x) => " = " + x.showDbg
        case N => ""
      }"
    case cls: ClassDef =>
      s"class ${cls.sym.nme}${
        cls.tparams.map(_.showDbg).mkStringOr(", ", "[", "]")}${
        cls.paramsOpt.fold("")(_.map(_.showDbg).mkString("(", ", ", ")"))} ${cls.body}"

final case class LetBinding(pat: Pattern, rhs: Term) extends Statement:
  def children: Ls[Located] = ???

final case class TermDefinition(
    k: TermDefKind,
    sym: TermSymbol,
    params: Opt[Ls[Param]],
    sign: Opt[Term],
    body: Opt[Term],
    resSym: FlowSymbol,
) extends Companion:
  def children: Ls[Located] = ???

case class ObjBody(blk: Term.Blk):
  // override def toString: String = statmts.mkString("{ ", "; ", " }")
  override def toString: String = blk.showDbg

sealed abstract class Declaration

sealed abstract class Definition extends Declaration with Statement

sealed abstract class Companion extends Definition

sealed abstract class ModuleDef extends Companion:
  val sym: ModuleSymbol

sealed abstract class ClassDef extends Definition:
  val sym: ClassSymbol
  val tparams: Ls[TyParam]
  val paramsOpt: Opt[Ls[Param]]
  val body: ObjBody
  val companion: Opt[Companion]
  def children: Ls[Located] = ???
object ClassDef:
  def apply(sym: ClassSymbol, tparams: Ls[TyParam], paramsOpt: Opt[Ls[Param]], body: ObjBody): ClassDef =
    paramsOpt match
      case S(params) => Parameterized(sym, tparams, params, body, N)
      case N => Plain(sym, tparams, body, N)
  def unapply(cls: ClassDef): Opt[(ClassSymbol, Ls[TyParam], Opt[Ls[Param]], ObjBody)] =
    S((cls.sym, cls.tparams, cls.paramsOpt, cls.body))
  case class Parameterized(sym: ClassSymbol, tparams: Ls[TyParam], params: Ls[Param], body: ObjBody, companion: Opt[ModuleDef]) extends ClassDef:
    val paramsOpt: Opt[Ls[Param]] = S(params)
  case class Plain(sym: ClassSymbol, tparams: Ls[TyParam], body: ObjBody, companion: Opt[Companion]) extends ClassDef:
    val paramsOpt: Opt[Ls[Param]] = N
end ClassDef

case class TypeDef(sym: TypeAliasSymbol, companion: Opt[Companion]) extends Statement:
  def children: Ls[Located] = ???

final case class FldFlags(mut: Bool, spec: Bool, genGetter: Bool) extends Located:
  def children: Ls[Located] = ???
  def showDbg: Str = (if mut then "mut " else "") + (if spec then "spec " else "") + (if genGetter then "val " else "")
  override def toString: String = "‹" + showDbg + "›"

final case class Fld(flags: FldFlags, value: Term, asc: Opt[Term]) extends FldImpl

final case class TyParam(flags: FldFlags, sym: VarSymbol) extends Declaration:
  
  // * For variance analysis
  var isCovariant: Bool = true
  var isContravariant: Bool = true
  
  def showDbg: Str =
    // (if isContravariant then "in " else "") +
    // (if isCovariant then "out " else "") +
    (if isCovariant then
      if isContravariant then "" else "out "
      else if isContravariant then "in " else "in out ") +
    flags.showDbg + sym
final case class Param(flags: FldFlags, sym: VarSymbol, sign: Opt[Term]):
  def subTerms: Ls[Term] = sign.toList
  // def children: Ls[Located] = self.value :: self.asc.toList ::: Nil
  // def showDbg: Str = flags.showDbg + sym.name + ": " + sign.showDbg
  def showDbg: Str = flags.showDbg + sym + sign.fold("")(": " + _.showDbg)

object FldFlags { val empty: FldFlags = FldFlags(false, false, false) }

trait FldImpl extends Located:
  self: Fld =>
  def children: Ls[Located] = self.value :: self.asc.toList ::: Nil
  def showDbg: Str = flags.showDbg + self.value.showDbg
  def describe: Str =
    (if self.flags.spec then "specialized " else "") +
    (if self.flags.mut then "mutable " else "") +
    self.value.describe


