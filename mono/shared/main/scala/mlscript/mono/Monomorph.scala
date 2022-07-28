package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.TypeName
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var, Fld}
import mlscript.{IntLit, DecLit, StrLit, UnitLit}
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer
import mlscript.Cls
import mlscript.CaseBranches
import mlscript.TypeDefKind

class Monomorph(debugMode: Boolean):
  private val debug = if debugMode then RainbowDebug() else DummyDebug()

  /**
   * Specialized implementations of function declarations.
   */
  private val funImpls = MutMap[String, (Item.FuncDecl, ArrayBuffer[Item.FuncDecl])]()

  /**
   * Specialized implementations of each type declarations.
   */
  private val tyImpls = MutMap[String, (Item.TypeDecl, ArrayBuffer[Item.TypeDecl])]()
  /**
   * Add a prototype type declaration.
   */
  private def addPrototypeTypeDecl(typeDecl: Item.TypeDecl) =
    tyImpls.addOne(typeDecl.name.name, (typeDecl, ArrayBuffer()))
  /**
   * An iterator going through all type declarations.
   */
  private def allTypeDecls: IterableOnce[(Item.TypeDecl, Item.TypeDecl)] =
    tyImpls.iterator.flatMap { case (name, (protoClass, implClasses)) =>
      implClasses.iterator.map((protoClass, _))
    }

  /**
   * A global store of monomorphized lambda classes.
   */
  private val lamTyDefs = MutMap[String, Item.TypeDecl]()
  /**
   * A global store of anonymous classes. For example, `new { ... }`.
   */
  private val anonymTyDefs = MutMap[String, Item.TypeDecl]()

  /**
   * This function monomorphizes the top-level `TypingUnit` into a `Module`.
   */
  def monomprphize(tu: TypingUnit): Module =
    debug.trace("MONO MODL", PrettyPrinter.show(tu)) {
      mlscript.mono.Module(tu.entities.iterator.flatMap[Expr | Item] {
        case Left(term) =>
          Some(monomorphizeTerm(term))
        case Right(tyDef: NuTypeDef) => 
          monomorphizeTypeDef(tyDef)
          None
        case Right(funDef: NuFunDef) =>
          val funcItem = monomorphizeFunDef(funDef)
          funcItem match
            case funcDecl: Item.FuncDecl =>
              funImpls.addOne(funcDecl.name.name, (funcDecl, ArrayBuffer()))
            case _ => ()
          Some(funcItem)
      }.concat(allTypeDecls.map(_._2))
       .concat(lamTyDefs.values)
       .concat(anonymTyDefs.values)
       .toList)
    }(_.toString)

  /**
   * This function monomorphizes the nested `TypingUnit` into a `Isolation`.
   */
  def monomorphizeBody(body: TypingUnit): Isolation =
    debug.trace("MONO BODY", PrettyPrinter.show(body)) {
      Isolation(body.entities.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
        case Left(term) =>
          Some(monomorphizeTerm(term))
        case Right(tyDef: NuTypeDef) => 
          monomorphizeTypeDef(tyDef)
          None
        case Right(funDef: NuFunDef) =>
          Some(monomorphizeFunDef(funDef))
      })
    }(_.toString)

  /**
   * This function flattens a top-level type definition and returns the root
   * type definition. There is a simple class lifting here.
   */
  private def monomorphizeTypeDef(tyDef: NuTypeDef): Item.TypeDecl =
    debug.trace("MONO TDEF", PrettyPrinter.show(tyDef)) {
      /**
       * The recursive function doing the real work.
       * @param tyDef the type definition
       * @param namePath enclosing class names and this class name
       */
      def rec(tyDef: NuTypeDef, namePath: List[String]): Item.TypeDecl =
        debug.trace[Item.TypeDecl]("LIFT", PrettyPrinter.show(tyDef)) {
          val NuTypeDef(kind, _, tparams, params, parents, body) = tyDef
          val isolation = Isolation(body.entities.flatMap {
            // Question: Will there be pure terms in class body?
            case Left(term) =>
              Some(monomorphizeTerm(term))
            case Right(subTypeDef: NuTypeDef) =>
              rec(subTypeDef, subTypeDef.nme.name :: namePath)
              None
            case Right(subFunDef: NuFunDef) =>
              Some(monomorphizeFunDef(subFunDef))
          })
          val className = namePath.reverseIterator.mkString("_")
          val typeDecl: Item.TypeDecl = Item.TypeDecl(className, kind, tparams, parents, isolation)
          addPrototypeTypeDecl(typeDecl)
          typeDecl
        }()

      rec(tyDef, tyDef.nme.name :: Nil)
    }()
    
  /**
   * This function monomorphizes a function definition in smoe typing units.
   * @param tyDecls the destination of nested type declarations
   */
  private def monomorphizeFunDef(funDef: NuFunDef): Item.FuncDecl | Item.FuncDefn =
    debug.trace[Item.FuncDecl | Item.FuncDefn]("MONO FUNC", PrettyPrinter.show(funDef)) {
      val NuFunDef(nme, targs, rhs) = funDef
      rhs match
        case Left(term) => Item.FuncDecl(nme, monomorphizeTerm(term))
        case Right(polyType) => Item.FuncDefn(nme, targs, polyType)
    }(_.toString)

  /**
   * This function monomophizes a `Term` into an `Expr`.
   */
  def monomorphizeTerm(term: Term): Expr =
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
            case (_, Fld(mut, spec, value)) => monomorphizeTerm(value)
          })
        case Rcd(fields) =>
          Expr.Record(fields.map {
            case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(value))
          })
        case Sel(receiver, fieldName) =>
          Expr.Select(monomorphizeTerm(receiver), fieldName)
        case Let(isRec, name, rhs, body) =>
          Expr.LetIn(isRec, name, monomorphizeTerm(rhs), monomorphizeTerm(body))
        case Blk(stmts) => Expr.Block(stmts.flatMap[Expr | Item.FuncDecl | Item.FuncDefn] {
          case term: Term => Some(monomorphizeTerm(term))
          case tyDef: NuTypeDef =>
            monomorphizeTypeDef(tyDef)
            None
          case funDef: NuFunDef => Some(monomorphizeFunDef(funDef))
          case mlscript.DataDefn(_) => throw MonomorphError("unsupported DataDefn")
          case mlscript.DatatypeDefn(_, _) => throw MonomorphError("unsupported DatatypeDefn")
          case mlscript.TypeDef(_, _, _, _, _, _) => throw MonomorphError("unsupported TypeDef")
          case mlscript.Def(_, _, _) => throw MonomorphError("unsupported Def")
          case mlscript.LetS(_, _, _) => throw MonomorphError("unsupported LetS")
        })
        case _: Bra => throw MonomorphError("cannot monomorphize `Bra`")
        case Asc(term, ty) => Expr.As(monomorphizeTerm(term), ty)
        case _: Bind => throw MonomorphError("cannot monomorphize `Bind`")
        case _: Test => throw MonomorphError("cannot monomorphize `Test`")
        case With(term, Rcd(fields)) =>
          Expr.With(monomorphizeTerm(term), Expr.Record(fields.map {
            case (name, Fld(mut, spec, value)) => (name, monomorphizeTerm(term))
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
  def specializeNew(name: String, termArgs: List[Term], termBody: TypingUnit): Expr.Apply =
    debug.trace[Expr.Apply]("SPEC NEW", {
      name + termArgs.iterator.map(_.toString).mkString("(", ", ", ")") +
        " with " + PrettyPrinter.show(termBody)
    }) {
      val args = termArgs.map(monomorphizeTerm)
      val body = monomorphizeBody(termBody)
      val specTypeDecl = specializeTypeDef(name, args, body)
      Expr.Apply(specTypeDecl.name, Nil)
    }(_.toString)

  /**
   * This function monomorphizes the given class with given arguments.
   * @return specialized class name and all included classes
   */
  def specializeTypeDef(
      name: String,
      args: List[Expr],
      body: Isolation
  ): Item.TypeDecl =
    debug.trace("SPEC TDEF", name + args.mkString("(", ", ", ")") + " {\n" + body + "\n}") {
      tyImpls.get(name) match {
        case Some((Item.TypeDecl(name, kind, typeParams, parents, body), impls)) =>
          val implClassName: Expr.Ref = Expr.Ref(s"${name}_${impls.size}")
          val specTypeDecl: Item.TypeDecl = Item.TypeDecl(implClassName, kind, typeParams, parents, body)
          impls += specTypeDecl
          specTypeDecl
        case None => throw new MonomorphError(s"cannot specialize undeclared type $name")
      }
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

