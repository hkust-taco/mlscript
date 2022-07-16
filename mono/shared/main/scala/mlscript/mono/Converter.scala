package mlscript.mono

import mlscript.Term
import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import mlscript.{CaseBranches, Case, Wildcard, NoCases}

// This converts MLscript syntax trees to monomorphization syntax trees.
object Converter:
  private def unwrapTupledArguments(term: Term): List[Term] = term match
    case Tup(fields) => fields.map { case (_, (term, _)) => term }
    case other => other :: Nil

  private def convert(branch: CaseBranches): CaseBranch = ???

  private def convert(term: Term): Expr = term match
    case Var(name) => Expr.Ref(name)
    case Lam(Tup(fields), rhs) =>
      val params = fields.map[Expr.Ref] {
        case (_, (Var(param), _)) => Expr.Ref(param)
        case _ => throw MonomorphError("parameters other than `Var` are not supported")
      }
      Expr.Lambda(params, convert(rhs))
    case App(lhs, rhs) =>
      // FIXME: Handle multiple parameters.
      Expr.Apply(convert(lhs), List(convert(rhs)))
    case Tup(fields) => Expr.Tuple(fields.map {
      case (_, (term, _)) => convert(term)
    })
    case Rcd(fields) => Expr.Record(fields.map {
      case (Var(name), (term, _)) => (Expr.Ref(name), convert(term))
    })
    case Sel(receiver, Var(fieldName)) =>
      Expr.Select(convert(receiver), Expr.Ref(fieldName))
    case Let(isRec, Var(name), rhs, body) =>
      Expr.LetIn(isRec, Expr.Ref(name), convert(rhs), convert(body))
    case Blk(stmts) => ???
    case Bra(rcd, trm) => ???
    case Asc(trm, ty) => ???
    case Bind(lhs, rhs) => ???
    case Test(trm, ty) => ???
    case With(trm, fields) => ???
    case CaseOf(trm, cases) => ???
    case Subs(arr, idx) => Expr.Subscript(convert(arr), convert(idx))
    case Assign(lhs, rhs) => Expr.Assign(convert(lhs), convert(rhs))
    case New(head, body) => Expr.New(head.map {
      case (typeName, term) =>
        (typeName, unwrapTupledArguments(term).map(convert))
    }, convert(body))
    case Block(unit) => ???
    // Literals
    case IntLit(value) => Expr.Literal(value)
    case DecLit(value) => Expr.Literal(value)
    case StrLit(value) => Expr.Literal(value)
    case UnitLit(value) => ??? // Expr.Literal(value)

  private def convert(term: NuTypeDef): Item.TypeDecl = ???

  private def convert(term: NuFunDef): Item.FuncDecl | Item.FuncDefn = ???

  def convert(unit: TypingUnit): Isolation =
    Isolation(unit.entities.map {
      case Left(term) => convert(term)
      case Right(tyDef: NuTypeDef) => convert(tyDef)
      case Right(funDef: NuFunDef) => convert(funDef)
    })