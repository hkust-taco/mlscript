package mlscript.compiler

import mlscript.{App, Asc, Assign, Bind, Blk, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld, FldFlags, If, PolyType}
import mlscript.{IfBody, IfThen, IfElse, IfLet, IfOpApp, IfOpsApp, IfBlock}
import mlscript.UnitLit
import mlscript.codegen.Helpers.inspect as showStructure
import mlscript.compiler.mono.MonomorphError
import mlscript.NuTypeDef
import mlscript.NuFunDef
import scala.collection.mutable.ArrayBuffer
import mlscript.CaseBranches
import mlscript.Case
import mlscript.SimpleTerm
import mlscript.NoCases
import mlscript.Wildcard
import mlscript.DecLit
import mlscript.IntLit
import mlscript.StrLit
import mlscript.AppliedType
import mlscript.TypeName
import mlscript.TypeDefKind
import mlscript.compiler.mono.Monomorph
import mlscript.NuDecl
import mlscript.TypingUnit

object Helpers:
  /**
   * Extract parameters for monomorphization from a `Tup`.
   */
  def toFuncParams(term: Term): Iterator[Parameter] = term match
    case Tup(fields) => fields.iterator.flatMap {
      // The new parser emits `Tup(_: UnitLit(true))` from `fun f() = x`.
      case (_, Fld(FldFlags(_, _, _), UnitLit(true))) => None
      case (None, Fld(flags, Var(name))) => Some((flags, Expr.Ref(name), None))
      case (Some(Var(name)), Fld(flags, typename: Term)) => Some((flags, Expr.Ref(name), Some(typename)))
      case _ => throw new MonomorphError(
        s"only `Var` can be parameters but we meet ${showStructure(term)}"
      )
    }
    case _ => throw MonomorphError("expect the list of parameters to be a `Tup`")
  
  // FIXME: Loses tuple information in conversion
  def toFuncArgs(term: Term): IterableOnce[Term] = term match
    // The new parser generates `(undefined, )` when no arguments.
    // Let's do this temporary fix.
    case Tup((_, Fld(FldFlags(_, _, _), UnitLit(true))) :: Nil) => Iterable.empty
    case Tup(fields) => fields.iterator.map(_._2.value)
    case _ => Some(term)

  def term2Expr(term: Term): Expr = {
      term match
        case Var(name) => Expr.Ref(name)
        case Lam(lhs, rhs) => 
          val params = toFuncParams(lhs).toList
          Expr.Lambda(params, term2Expr(rhs))
        case App(App(Var("=>"), Bra(false, args: Tup)), body) =>
          val params = toFuncParams(args).toList
          Expr.Lambda(params, term2Expr(body))
        case App(App(Var("."), self), App(Var(method), args: Tup)) =>
          Expr.Apply(Expr.Select(term2Expr(self), Expr.Ref(method)), List.from(toFuncArgs(args).map(term2Expr)))
        case App(lhs, rhs) =>
          val callee = term2Expr(lhs)
          val arguments = toFuncArgs(rhs).map(term2Expr).toList
          Expr.Apply(callee, arguments)
        case Tup(fields) =>
          Expr.Tuple(fields.map {
            case (_, Fld(FldFlags(mut, spec, genGetter), value)) => term2Expr(value)
          })
        case Rcd(fields) =>
          Expr.Record(fields.map {
            case (name, Fld(FldFlags(mut, spec, genGetter), value)) => (Expr.Ref(name.name), term2Expr(value))
          })
        case Sel(receiver, fieldName) =>
          Expr.Select(term2Expr(receiver), Expr.Ref(fieldName.name))
        case Let(rec, Var(name), rhs, body) =>
          val exprRhs = term2Expr(rhs)
          val exprBody = term2Expr(body)
          Expr.LetIn(rec, Expr.Ref(name), exprRhs, exprBody)
        case Blk(stmts) => Expr.Block(stmts.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
          case term: Term => Some(term2Expr(term))
          case tyDef: NuTypeDef => throw MonomorphError(s"Unimplemented term2Expr ${term}")
          case funDef: NuFunDef => 
            val NuFunDef(isLetRec, nme, sn, targs, rhs) = funDef
            val ret: Item.FuncDecl | Item.FuncDefn = rhs match
              case Left(Lam(params, body)) =>
                Item.FuncDecl(isLetRec, Expr.Ref(nme.name), Some(toFuncParams(params).toList), term2Expr(body))
              case Left(body: Term) => Item.FuncDecl(isLetRec, Expr.Ref(nme.name), None, term2Expr(body))
              case Right(tp) => Item.FuncDefn(Expr.Ref(nme.name), targs, PolyType(Nil, tp)) 
            Some(ret)
          case mlscript.DataDefn(_) => throw MonomorphError("unsupported DataDefn")
          case mlscript.DatatypeDefn(_, _) => throw MonomorphError("unsupported DatatypeDefn")
          case mlscript.TypeDef(_, _, _, _, _, _, _, _) => throw MonomorphError("unsupported TypeDef")
          case mlscript.Def(_, _, _, _) => throw MonomorphError("unsupported Def")
          case mlscript.LetS(_, _, _) => throw MonomorphError("unsupported LetS")
          case mlscript.Constructor(_, _) => throw MonomorphError("unsupported Constructor")
        })
        case Bra(rcd, term) => term2Expr(term)
        case Asc(term, ty) => Expr.As(term2Expr(term), ty)
        case _: Bind => throw MonomorphError("cannot monomorphize `Bind`")
        case _: Test => throw MonomorphError("cannot monomorphize `Test`")
        case With(term, Rcd(fields)) =>
          Expr.With(term2Expr(term), Expr.Record(fields.map {
            case (name, Fld(flags, value)) => (Expr.Ref(name.name), term2Expr(term))
          }))
        case CaseOf(term, cases) => 
          def rec(bra: CaseBranches)(using buffer: ArrayBuffer[CaseBranch]): Unit = bra match
            case Case(pat, body, rest) => 
              val newCase = pat match
                case Var(name) => CaseBranch.Instance(Expr.Ref(name), Expr.Ref("_"), term2Expr(body))
                case DecLit(value) => CaseBranch.Constant(Expr.Literal(value), term2Expr(body))
                case IntLit(value) => CaseBranch.Constant(Expr.Literal(value), term2Expr(body))
                case StrLit(value) => CaseBranch.Constant(Expr.Literal(value), term2Expr(body))
                case UnitLit(undefinedOrNull) => CaseBranch.Constant(Expr.Literal(UnitValue.Undefined), term2Expr(body))
              buffer.addOne(newCase)
              rec(rest)
            case NoCases => ()
            case Wildcard(body) =>
              buffer.addOne(CaseBranch.Wildcard(term2Expr(body)))
          val branchBuffer = ArrayBuffer[CaseBranch]()
          rec(cases)(using branchBuffer)
          Expr.Match(term2Expr(term), branchBuffer)
          
        case Subs(array, index) =>
          Expr.Subscript(term2Expr(array), term2Expr(index))
        case Assign(lhs, rhs) =>
          Expr.Assign(term2Expr(lhs), term2Expr(rhs))
        case New(None, body) =>
          throw MonomorphError(s"Unimplemented term2Expr ${term}")
        case New(Some((constructor, args)), body) =>
          val typeName = constructor match
            case AppliedType(TypeName(name), _) => name
            case TypeName(name)                 => name
          Expr.New(TypeName(typeName), toFuncArgs(args).map(term2Expr).toList)
        // case Blk(unit) => Expr.Isolated(trans2Expr(TypingUnit(unit)))
        case If(body, alternate) => body match
          case IfThen(condition, consequent) =>
            Expr.IfThenElse(
              term2Expr(condition),
              term2Expr(consequent),
              alternate.map(term2Expr)
            )
          case term: IfElse => throw MonomorphError("unsupported IfElse")
          case term: IfLet => throw MonomorphError("unsupported IfLet")
          case term: IfOpApp => throw MonomorphError("unsupported IfOpApp")
          case term: IfOpsApp => throw MonomorphError("unsupported IfOpsApp")
          case term: IfBlock => throw MonomorphError("unsupported IfBlock")
        case IntLit(value) => Expr.Literal(value)
        case DecLit(value) => Expr.Literal(value)
        case StrLit(value) => Expr.Literal(value)
        case UnitLit(undefinedOrNull) => 
          Expr.Literal(if undefinedOrNull
                       then UnitValue.Undefined
                       else UnitValue.Null)
        case _ => throw MonomorphError("unsupported term"+ term.toString)
    }

    def exprLit2SimpleTerm(lit: Expr.Literal): SimpleTerm = lit.value match
          case i: BigInt => IntLit(i)
          case d: BigDecimal => DecLit(d)
          case s: String => StrLit(s)
          case UnitValue.Undefined => UnitLit(true)
          case UnitValue.Null => UnitLit(false)
          case b: Boolean => UnitLit(b)

    def expr2Term(expr: Expr): Term = {
      expr match
        case Expr.Ref(name) => 
          Var(name)
        case Expr.Lambda(params, body) => 
          Lam(
            Tup(params.map{
              case (flags: FldFlags, Expr.Ref(name), None) => (None, Fld(flags, Var(name)))
              case (flags: FldFlags, Expr.Ref(name), Some(typeinfo)) => (Some(Var(name)), Fld(flags, typeinfo))
            }),
            expr2Term(body)
          )
        case Expr.Apply(callee, arguments) => 
          App(expr2Term(callee),Tup(arguments.map(t => (None, Fld(FldFlags.empty, expr2Term(t))))))
        case Expr.Tuple(fields) => 
          Tup(fields.map(f => (None, Fld(FldFlags.empty, expr2Term(f)))))
        case Expr.Record(fields) =>
          Rcd(fields.map{
            case (Expr.Ref(name), expr: Expr) => (Var(name), Fld(FldFlags.empty, expr2Term(expr)))
          })
        case Expr.Select(reciever, field) => 
          Sel(expr2Term(reciever), Var(field.name))
        case Expr.LetIn(isRec, Expr.Ref(name), rhs, body) => 
          Let(isRec, Var(name), expr2Term(rhs),  expr2Term(body))
        case Expr.Block(items) => Blk(
          items.flatMap{
            case e: Expr => Some(expr2Term(e))
            case i: Item => Some(item2Term(i))
          }
        )
        case Expr.As(value, toType) => Asc(expr2Term(value), toType)
        case mlscript.compiler.Expr.Assign(assignee, value) => Assign(expr2Term(assignee), expr2Term(value))
        case mlscript.compiler.Expr.With(value, fields) => 
          With(expr2Term(value), Rcd(fields.fields.map{
            case (Expr.Ref(name), expr: Expr) => (Var(name), Fld(FldFlags.empty, expr2Term(expr)))
          }))
        case Expr.Subscript(receiver, index) => Subs(expr2Term(receiver), expr2Term(index))
        case Expr.Match(scrutinee, branches) => 
          def rec(bra: List[CaseBranch])(acc: CaseBranches): CaseBranches = bra.toList match 
            case Nil => acc
            case x :: xs => rec(xs)(
              x match
                case CaseBranch.Instance(className, alias, body) => Case(Var(className.name), expr2Term(body), acc)
                case CaseBranch.Constant(literal, body) => Case(exprLit2SimpleTerm(literal), expr2Term(body), acc)
                case mlscript.compiler.CaseBranch.Wildcard(body) => Wildcard(expr2Term(body))
            )
          CaseOf(expr2Term(scrutinee), rec(branches.toList)(NoCases))
        case lit: Expr.Literal => exprLit2SimpleTerm(lit)
        case mlscript.compiler.Expr.New(typeName, args) => 
          New(Some((TypeName(typeName.name), Tup(args.map(e => (None, Fld(FldFlags.empty, expr2Term(e))))))), TypingUnit(Nil))
        case Expr.IfThenElse(condition, consequent, alternate) => If(IfThen(expr2Term(condition), expr2Term(consequent)), alternate.map(expr2Term))
        case Expr.Isolated(isolation) => ???
    }

    def item2Term(item: Item): NuDecl = {
      item match
        case Item.TypeDecl(name, kind, typeParams, params, parents, body) => 
          NuTypeDef(
            kind,
            TypeName(name.name),
            typeParams.map(nm => (None, nm)),
            params.map(p => Tup(p.map{
              case (flags, Expr.Ref(name), None) => (None, Fld(flags, Var(name)))
              case (flags, Expr.Ref(name), Some(typeinfo)) => (Some(Var(name)), Fld(flags, typeinfo))
            })),
            None,
            None,
            Nil,
            None,
            None,
            TypingUnit(body.items.flatMap {
              case e: Expr => Some(expr2Term(e))
              case i: Item => Some(item2Term(i))
            }))
            (None, None)
        case Item.FuncDecl(isLetRec, name, params, body) => 
          NuFunDef(
            isLetRec,
            Var(name.name),
            None,
            Nil,
            Left(params match 
              case Some(p) => Lam(Tup(p.map{
                case (flags: FldFlags, Expr.Ref(name), None) => (None, Fld(flags, Var(name)))
                case (flags: FldFlags, Expr.Ref(name), Some(typeinfo)) => (Some(Var(name)), Fld(flags, typeinfo))
              }), expr2Term(body))
              case None => expr2Term(body)  
            ))
            (None, None, None, None, false)
        case Item.FuncDefn(name, typeParams, body) => 
          NuFunDef(
            None,
            Var(name.name),            
            None,
            typeParams,
            Right(body.body)
          )(None, None, None, None, false)
    }
  
  def func2Item(funDef: NuFunDef): Item.FuncDecl | Item.FuncDefn =
      val NuFunDef(isLetRec, nme, sn, targs, rhs) = funDef
      rhs match
        case Left(Lam(params, body)) =>
          Item.FuncDecl(isLetRec, Expr.Ref(nme.name), Some(toFuncParams(params).toList), term2Expr(body))
        case Left(body: Term) => 
          Item.FuncDecl(isLetRec, Expr.Ref(nme.name), None, term2Expr(body))
        case Right(tp) => Item.FuncDefn(Expr.Ref(nme.name), targs, PolyType(Nil, tp))
  
  def type2Item(tyDef: NuTypeDef): Item.TypeDecl =
    val NuTypeDef(kind, className, tparams, params, _, _, parents, _, _, body) = tyDef
    val isolation = Isolation(body.entities.flatMap {
      // Question: Will there be pure terms in class body?
      case term: Term =>
        Some(term2Expr(term))
      case subTypeDef: NuTypeDef => throw MonomorphError(s"Unimplemented func2Item ${tyDef}")
      case subFunDef: NuFunDef =>
        Some(func2Item(subFunDef))
      case term => throw MonomorphError(term.toString)
    })
    val typeDecl: Item.TypeDecl = Item.TypeDecl(
      Expr.Ref(className.name), // name
      kind, // kind
      tparams.map(_._2), // typeParams
      params.map(toFuncParams(_).toList), // params
      parents.map {
        case Var(name) => (TypeName(name), Nil)
        case App(Var(name), args) => (TypeName(name), term2Expr(args) match{
          case Expr.Tuple(fields) => fields
          case _ => Nil
        })
        case _ => throw MonomorphError("unsupported parent term")
      }, // parents
      isolation // body
    )
    typeDecl
  
  private given Conversion[TypeDefKind, TypeDeclKind] with
    import mlscript.{Als, Cls, Trt}
    def apply(kind: TypeDefKind): TypeDeclKind = kind match
      case Als => TypeDeclKind.Alias
      case Cls => TypeDeclKind.Class
      case Trt => TypeDeclKind.Trait
      case _ => throw MonomorphError(s"Unsupported TypeDefKind conversion ${kind}")

  private given Conversion[TypeDeclKind, TypeDefKind] with
    import mlscript.{Als, Cls, Trt}
    def apply(kind: TypeDeclKind): TypeDefKind = kind match
      case TypeDeclKind.Alias => Als
      case TypeDeclKind.Class => Cls
      case TypeDeclKind.Trait => Trt