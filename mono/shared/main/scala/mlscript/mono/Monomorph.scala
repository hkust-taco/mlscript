package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.TypeName
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer
import mlscript.Cls
import mlscript.CaseBranches
import mlscript.TypeDefKind

object Monomorph:
  private val debug = RainbowDebug()

  private val funProtos = MutMap[String, NuFunDef]()
  private val funImpls = MutMap[String, ArrayBuffer[NuFunDef]]()

  private val tyProtos = MutMap[String, NuTypeDef]()
  private val tyImpls = MutMap[String, ArrayBuffer[NuTypeDef]]()
  private val allTyImpls = ArrayBuffer[NuTypeDef]()

  /**
   * A global store of monomorphized lambda classes.
   */
  private val lamTyDefs = MutMap[String, Item.TypeDecl]()
  /**
   * A global store of anonymous classes. For example, `new { ... }`.
   */
  private val anonymTyDefs = MutMap[String, Item.TypeDecl]()

  def specializedTypeDefs: List[NuTypeDef] = allTyImpls.toList

  /**
   * This function monomorphizes the top-level `TypingUnit` into a `Module`.
   */
  def monomprphize(tu: TypingUnit): Module =
    debug.trace("MONO MODL", PrettyPrinter.show(tu)) {
      mlscript.mono.Module(tu.entities.flatMap[Expr | Item] {
        case Left(term) =>
          val tyDecls = ArrayBuffer[Item.TypeDecl]()
          Some(monomorphizeTerm(term)(using tyDecls)).concat(tyDecls)
        case Right(tyDef: NuTypeDef) => 
          tyProtos.addOne((tyDef.nme.name, tyDef))
          tyImpls.addOne((tyDef.nme.name, ArrayBuffer()))
          monomorphizeTypeDef(tyDef)
        case Right(funDef: NuFunDef) =>
          funProtos.addOne((funDef.nme.name, funDef))
          funImpls.addOne((funDef.nme.name, ArrayBuffer()))
          val tyDecls = ArrayBuffer[Item.TypeDecl]()
          Some(monomorphizeFunDef(funDef)(using tyDecls))
      })
    }(_.toString)

  /**
   * This function monomorphizes the top-level `TypingUnit` into a `Module`.
   */
  def monomorphizeBody(body: TypingUnit)(
      using tyDecls: ArrayBuffer[Item.TypeDecl]
  ): Isolation =
    debug.trace("MONO BODY", PrettyPrinter.show(body)) {
      Isolation(body.entities.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
        case Left(term) =>
          Some(monomorphizeTerm(term))
        case Right(tyDef: NuTypeDef) => 
          tyProtos.addOne((tyDef.nme.name, tyDef))
          tyImpls.addOne((tyDef.nme.name, ArrayBuffer()))
          tyDecls ++= monomorphizeTypeDef(tyDef)
          None
        case Right(funDef: NuFunDef) =>
          funProtos.addOne((funDef.nme.name, funDef))
          funImpls.addOne((funDef.nme.name, ArrayBuffer()))
          val tyDecls = ArrayBuffer[Item.TypeDecl]()
          Some(monomorphizeFunDef(funDef))
      })
    }(_.toString)

  /**
   * This function monomorphizes a top-level type definition and produces a
   * series of `Item.TypeDecl`.
   */
  private def monomorphizeTypeDef(tyDef: NuTypeDef): Iterable[Item.TypeDecl] =
    // Lifted classes will be put in this array buffer.
    val nestedTypeDecls = ArrayBuffer[Item.TypeDecl]()

    // The recursive function doing the real work.
    def rec(tyDef: NuTypeDef): Item.TypeDecl =
      debug.trace[Item.TypeDecl]("MONO TDEF", PrettyPrinter.show(tyDef)) {
        val NuTypeDef(kind, nme, tparams, specParams, parents, body) = tyDef
        val isolation = Isolation(body.entities.flatMap {
          // Will there be pure terms in class body?
          case Left(term) => Some(monomorphizeTerm(term)(using nestedTypeDecls))
          case Right(tyDef: NuTypeDef) =>
            nestedTypeDecls += rec(tyDef)
            None
          case Right(funDef: NuFunDef) =>
            Some(monomorphizeFunDef(funDef)(using nestedTypeDecls))
        })
        Item.TypeDecl(nme, kind, tparams, parents, isolation)
      }()

    // Returns the array buffer as an `Iterable`.
    nestedTypeDecls += rec(tyDef)

  /**
   * This function monomorphizes a function definition in smoe typing units.
   * @param tyDecls the destination of nested type declarations
   */
  private def monomorphizeFunDef(funDef: NuFunDef)(
      using tyDecls: ArrayBuffer[Item.TypeDecl]
  ): Item.FuncDecl | Item.FuncDefn =
    debug.trace[Item.FuncDecl | Item.FuncDefn]("MONO FUNC", PrettyPrinter.show(funDef)) {
      funImpls.addOne((funDef.nme.name, ArrayBuffer()))
      val NuFunDef(nme, targs, specParams, body) = funDef
      body match
        case Left(term) => Item.FuncDecl(nme, monomorphizeTerm(term))
        case Right(polyType) => Item.FuncDefn(nme, targs, polyType)
    }(_.toString)

  /**
   * This function monomophizes a `Term` into an `Expr`.
   * @param tyDecls the destination of nested type declarations
   */
  def monomorphizeTerm(term: Term)(using tyDecls: ArrayBuffer[Item.TypeDecl]): Expr =
    import Helpers._
    debug.trace[Expr]("MONO TERM", PrettyPrinter.show(term)) {
      term match
        case Var(name) => Expr.Ref(name)
        case Lam(lhs, rhs) =>
          val params = toFuncParams(lhs).toList
          // TODO: Capture variables referenced in the lambda body.
          // We should capture: closure variables and referenced type variables.
          val className = s"Lambda_${lamTyDefs.size}"
          val classBody = Isolation(Item.FuncDecl("apply", monomorphizeTerm(rhs)) :: Nil)
          val classDecl = Item.classDecl(className, classBody)
          // Add to the global store.
          lamTyDefs.addOne((className, classDecl))
          // Returns a class construction.
          Expr.New(Some((TypeName(className), Nil)), Isolation.empty)
        case App(lhs, rhs) =>
          val callee = monomorphizeTerm(lhs)
          val arguments = toFuncArgs(rhs).map(monomorphizeTerm).toList
          Expr.Apply(callee, arguments)
        case Tup(fields) =>
          Expr.Tuple(fields.map {
            case (_, (term, _)) => monomorphizeTerm(term)
          })
        case Rcd(fields) =>
          Expr.Record(fields.map {
            case (name, (term, _)) => (name, monomorphizeTerm(term))
          })
        case Sel(receiver, fieldName) =>
          Expr.Select(monomorphizeTerm(receiver), fieldName)
        case Let(isRec, name, rhs, body) =>
          Expr.LetIn(isRec, name, monomorphizeTerm(rhs), monomorphizeTerm(body))
        case _: Blk => throw MonomorphError("cannot monomorphize `Blk`")
        case _: Bra => throw MonomorphError("cannot monomorphize `Bra`")
        case Asc(term, ty) => Expr.As(monomorphizeTerm(term), ty)
        case _: Bind => throw MonomorphError("cannot monomorphize `Bind`")
        case _: Test => throw MonomorphError("cannot monomorphize `Test`")
        case With(term, Rcd(fields)) =>
          Expr.With(monomorphizeTerm(term), Expr.Record(fields.map {
            case (name, (term, _)) => (name, monomorphizeTerm(term))
          }))
        case CaseOf(term, cases) => ???
        case Subs(array, index) =>
          Expr.Subscript(monomorphizeTerm(array), monomorphizeTerm(index))
        case Assign(lhs, rhs) =>
          Expr.Assign(monomorphizeTerm(lhs), monomorphizeTerm(rhs))
        case New(None, body) =>
          val className = s"Anonym_${anonymTyDefs.size}"
          val classDecl = Item.classDecl(className, monomorphizeBody(body))
          Expr.Apply(className, Nil)
        case New(Some((TypeName(name), args)), body) =>
          specializeNew(name, toFuncArgs(args).toList, body)
        case Block(unit) => Expr.Isolated(monomorphizeBody(unit))
        case IntLit(value) => Expr.Literal(value)
        case DecLit(value) => Expr.Literal(value)
        case StrLit(value) => Expr.Literal(value)
        case UnitLit(undefinedOrNull) => 
          Expr.Literal(if undefinedOrNull
                       then UnitValue.Undefined
                       else UnitValue.Null)
    }(_.toString)

  /**
   * `new C(...) { ... }` expressions are converted into
   * `{ class CImpl extends C(...) { ... }; CImpl() }`.
   * ~~This requires you to add a `LetClass` construct to `mlscript.Term`.~~
   */
  def specializeNew(name: String, termArgs: List[Term], termBody: TypingUnit)(
      using tyDecls: ArrayBuffer[Item.TypeDecl]
  ): Expr.Apply =
    debug.trace[Expr.Apply]("SPEC NEW", {
      name + termArgs.iterator.map(_.toString).mkString("(", ", ", ")") +
        " with " + PrettyPrinter.show(termBody)
    }) {
      val args = termArgs.map(monomorphizeTerm)
      val body = monomorphizeBody(termBody)
      val (specClassRef, addedClasses) = specializeTypeDef(name, args, body)
      tyDecls ++= addedClasses
      Expr.Apply(specClassRef, Nil)
    }(_.toString)

  /**
   * This function monomorphizes the given class with given arguments.
   * @return specialized class name and all included classes
   */
  def specializeTypeDef(
      name: String,
      args: List[Expr],
      body: Isolation
  ): (Expr.Ref, IterableOnce[Item.TypeDecl]) =
    debug.trace("SPEC TDEF", name + args.mkString("(", ", ", ")")) {
      tyProtos.get(name) match {
        case Some(NuTypeDef(kind, nme, tparams, specParams, parents, body)) =>
          val tyDefImpls = tyImpls(name)
          val implClassName = s"${name}_${tyDefImpls.size}"
          // How to put args into `specParams`?
          val specTyDef = NuTypeDef(kind, TypeName(implClassName), tparams, specParams, parents, body)
          tyDefImpls += specTyDef
          allTyImpls += specTyDef
          specTyDef
        case None => throw new MonomorphError(s"undeclared type $name")
      }
      ???
    }()

  // Shorthand implicit conversions.

  private given Conversion[String, Expr.Ref] with
    def apply(name: String): Expr.Ref = Expr.Ref(name)

  private given Conversion[Var, Expr.Ref] with
    def apply(nme: Var): Expr.Ref = Expr.Ref(nme.name)

  private given Conversion[TypeName, Expr.Ref] with
    def apply(nme: TypeName): Expr.Ref = Expr.Ref(nme.name)

  private given Conversion[TypeDefKind, TypeDeclKind] with
    import mlscript.{Als, Cls, Trt}
    def apply(kind: TypeDefKind): TypeDeclKind = kind match
      case Als => TypeDeclKind.Alias
      case Cls => TypeDeclKind.Class
      case Trt => TypeDeclKind.Trait

