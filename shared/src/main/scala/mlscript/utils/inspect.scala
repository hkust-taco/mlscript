package mlscript.utils

import mlscript._, shorthands._

object inspect {
  object shallow {
    def apply(term: Statement): Str = term match {
      case Var(name) => s"Var(\"$name\")"
      case literal: Lit => s"Lit(${literal.toString})"
      case fd: NuFunDef => fd.isLetRec.fold("fun")(if (_) "let rec" else "let") + " " + fd.nme.name
      case td: NuTypeDef => s"${td.kind.str} ${td.nme.name}"
      case _ =>
        val name = term.getClass.getSimpleName
        val arity = term.children.length // Imprecise
        if (arity === 0) { name } else s"${name}(${(", _" * arity).drop(2)})"
    }

    def apply(d: TypingUnit): Str = d.entities.iterator
      .map(apply)
      .mkString("{", ", ", "}")
  }

  object deep {
    def apply(t: Opt[Located]): Str = t match {
      case N => "N"
      case S(l) => s"S(${apply(l)})"
    }

    def apply(t: Ls[Located]): Str = t match {
      case Nil => "Nil"
      case head :: Nil => s"${apply(head)} :: Nil"
      case first :: second :: Nil => s"${apply(first)} :: ${apply(second)} :: Nil"
      case _ => t.iterator.map(apply).mkString("Ls(", ", ", ")")
    }

    def apply[A <: Located, B <: Located](t: Either[A, B]): Str = t match {
      case L(value) => s"L(${apply(value)})"
      case R(value) => s"R(${apply(value)})"
    }

    def apply(t: Located): Str = t match {
      case st: Statement => statement(st)
      case fl: Field => field(fl)
      case ty: TypeLike => typeLike(ty)
      case ib: IfBody => ifBody(ib)
      case tu: TypingUnit => typingUnit(tu)
      case _ => "??"
    }

    private def statement(statement: Statement): Str = statement match {
      case Def(rec, nme, rhs, isByname) => s"Def($rec, ${apply(nme)}, ${apply(rhs)}, $isByname)"
      case TypeDef(kind, nme, tparams, body, mthDecls, mthDefs, positionals, adtInfo) => s"TypeDef(...)"
      case Var(name)     => s"Var(\"$name\")"
      case Lam(lhs, rhs) => s"Lam(${apply(lhs)}, ${apply(rhs)})"
      case App(lhs, rhs) => s"App(${apply(lhs)}, ${apply(rhs)})"
      case Tup(fields) =>
        fields.iterator.map {
          case (S(name), Fld(_, value)) => s"(S(${apply(name)}), ${apply(value)})"
          case (N, Fld(_, value))       => s"(N, ${apply(value)})"
        }.mkString("Tup(", ", ", ")")
      case Rcd(fields) =>
        fields.iterator.map { case k -> Fld(_, v) => s"${apply(k)} = ${apply(v)}" }.mkString("Rcd(", ", ", ")")
      case Sel(receiver, fieldName)    => s"Sel(${apply(receiver)}, $fieldName)"
      case Let(isRec, name, rhs, body) => s"Let($isRec, $name, ${apply(rhs)}, ${apply(body)})"
      case Blk(stmts)                  => s"Blk(${stmts.iterator.map(apply).mkString(", ")})"
      case Bra(rcd, trm)               => s"Bra(rcd = $rcd, ${apply(trm)})"
      case Asc(trm, ty)                => s"Asc(${apply(trm)}, $ty)"
      case Bind(lhs, rhs)              => s"Bind(${apply(lhs)}, ${apply(rhs)})"
      case Test(trm, ty)               => s"Test(${apply(trm)}, ${apply(ty)})"
      case With(trm, fields) =>
        s"With(${apply(trm)}, ${apply(fields)})"
      case CaseOf(trm, cases) =>
        def inspectCaseBranches(br: CaseBranches): Str = br match {
          case Case(clsNme, body, rest) =>
            s"Case($clsNme, ${apply(body)}, ${inspectCaseBranches(rest)})"
          case Wildcard(body) => s"Wildcard(${apply(body)})"
          case NoCases        => "NoCases"
        }
        s"CaseOf(${apply(trm)}, ${inspectCaseBranches(cases)})"
      case IntLit(value)  => s"IntLit($value)"
      case DecLit(value)  => s"DecLit($value)"
      case StrLit(value)  => s"StrLit($value)"
      case UnitLit(value)  => s"UnitLit($value)"
      case Subs(arr, idx) => s"Subs(${apply(arr)}, ${apply(idx)})"
      case Assign(f, v)   => s"Assign(${apply(f)}, ${apply(v)})"
      case Splc(fs)       => 
        fs.iterator.map{ case L(l) => s"...${apply(l)}" case R(Fld(_, r)) => apply(r)}.mkString("Splc(", ", ", ")")
      case If(bod, els) => s"If(${apply(bod)}, ${els.map(apply)})"
      case New(base, body) => s"New(${base}, ${apply(body)})"
      case NuNew(base) => s"NuNew(${apply(base)})"
      case TyApp(base, targs) => s"TyApp(${apply(base)}, ${targs})"
      case Where(bod, sts) => s"Where(${apply(bod)}, ...)"
      case Forall(ps, bod) => s"Forall($ps, ${apply(bod)})"
      case Inst(bod) => s"Inst(${apply(bod)})"
      case Eqn(lhs, rhs) => s"Eqn(${apply(lhs)}, ${apply(rhs)})"
      case Super() => "Super()"
      case AdtMatchWith(cond, arms) =>
        s"match ${apply(cond)} with ${arms.map(patmat => s"${apply(patmat.pat)} -> ${apply(patmat.rhs)}").mkString(" | ")}"
      case Rft(bse, tu) => s"Rft(${apply(bse)}, ${apply(tu)})"
      case LetS(isRec, pat, rhs) => s"LetS($isRec, ${apply(pat)}, ${apply(rhs)})"
      case DataDefn(body) => s"DataDefn(${apply(body)})"
      case DatatypeDefn(head, body) => s"DatatypeDefn(${apply(head)}, ${apply(body)})"
      case NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, superAnnot, thisAnnot, body) =>
        s"NuTypeDef($kind, ${apply(nme)}, Ls(" +
          tparams.iterator.map {
            case (S(vi), tn) => s"S($vi) -> ${apply(tn)}"
            case (N, tn) => s"N -> ${apply(tn)}"
          }.mkString(", ") + "), " +
          apply(params) + ", " +
          apply(ctor) + ", " +
          apply(sig) + ", " +
          parents.iterator.map(apply).mkString("Ls(", ", ", ")") + ", " +
          apply(superAnnot) + ", " +
          apply(thisAnnot) + ", " +
          apply(body) + ")"
      case NuFunDef(isLetRec, nme, symbolicNme, tparams, rhs) =>
        s"NuFunDef($isLetRec, ${nme.name}, ${apply(symbolicNme)}, ${apply(tparams)}, ${apply(rhs)})"
      case Constructor(params, body) => s"Constructor"
    }

    private def field(field: Field): Str = field match {
      case Field(nme, value) => s"Fld(${apply(nme)}, ${apply(value)})"
    }

    private def typeLike(ty: TypeLike): Str = ty match {
      case Union(lhs, rhs) => s"Union(${apply(lhs)}, ${apply(rhs)})"
      case Inter(lhs, rhs) => s"Inter(${apply(lhs)}, ${apply(rhs)})"
      case Function(lhs, rhs) => s"Function(${apply(lhs)}, ${apply(rhs)})"
      case Record(fields) => s"Record(${fields.iterator.map { case (nme, ty) => s"$nme: ${apply(ty)}" }.mkString(", ")})"
      case Tuple(fields) => s"Tuple(${fields.iterator.map {
        case N -> field => s"N -> ${apply(field)}"
        case S(nme) -> field => s"S($nme) -> ${apply(field)}"
      }.mkString(", ")})"
      case Recursive(uv, body) => s"Recursive(${apply(uv)}, ${apply(body)})"
      case AppliedType(base, targs) => s"AppliedType(${apply(base)}, ${apply(targs)})"
      case Selection(base, name) => s"Selection(${apply(base)}, $name)"
      case Neg(base) => s"Neg(${apply(base)})"
      case Rem(base, names) => s"Rem(${apply(base)}, ${names.iterator.map(apply).mkString(", ")})"
      case Bounds(lb, ub) => s"Bounds(${apply(lb)}, ${apply(ub)})"
      case WithExtension(base, rcd) => s"WithExtension(${apply(base)}, ${apply(rcd)})"
      case Splice(fields) => s"Splice(${fields.iterator.map {
        case L(l) => s"L(${apply(l)})"
        case R(f) => s"R(${apply(f)})"
      }.mkString(", ")})"
      case Constrained(base, tvBounds, where) => s"Constrained(${apply(base)}, Ls(${tvBounds.iterator.map {
        case (tv, bounds) => s"${apply(tv)} -> ${apply(bounds)}"
      }}), ${apply(where)})"
      case Top => "Top"
      case Bot => "Bot"
      case Literal(lit) => s"Literal(${lit.toString})"
      case TypeName(name) => s"TypeName(\"$name\")"
      case TypeTag(name) => s"TypeTag($name)"
      case TypeVar(identifier, nameHint) => s"TypeVar(${identifier match {
        case L(i) => s"L($i)"
        case R(n) => s"R($n)"
      }}, ${nameHint.fold("N")(n => s"S($n)")})"
      case PolyType(targs, body) => s"PolyType(Ls(${targs.iterator.map(_.fold(apply, apply)).mkString(", ")}), ${apply(body)})"
      case Signature(members, result) => s"Signature(${members.iterator.map(apply(_: Statement)).mkString("Ls(", ", ", ")")}, ${apply(result)})"
      case t: NuDecl => apply(t: Statement)
    }

    private def ifBody(body: IfBody): Str = body match {
      case IfElse(expr) => s"IfElse(${apply(expr)}"
      case IfThen(expr, rhs) => s"IfThen(${apply(expr)}, ${apply(rhs)}"
      case IfBlock(lines) => s"IfBlock(${
        lines.iterator.map(_.fold(apply, apply)).mkString("Ls(", ", ", ")")
      })"
      case IfOpsApp(lhs, opsRhss) => s"IfOpsApp(${apply(lhs)}, ${
        opsRhss.iterator.map { case (op, body) =>
          s"$op -> ${apply(body)}"
        }
      }".mkString("; ")
      case IfLet(isRec, name, rhs, body) => ???
      case IfOpApp(lhs, op, rhs) =>
        s"IfOpApp(${apply(lhs)}, ${apply(op)}, ${apply(rhs)}"
    }

    private def typingUnit(t: TypingUnit): Str = t.entities.iterator
      .map(apply)
      .mkString("TypingUnit(", ", ", ")")
  }
}