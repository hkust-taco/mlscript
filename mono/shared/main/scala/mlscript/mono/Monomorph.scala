package mlscript.mono

import mlscript.{TypingUnit, NuTypeDef, NuFunDef}
import mlscript.TypeName
import mlscript.{App, Asc, Assign, Bind, Blk, Block, Bra, CaseOf, Lam, Let, Lit,
                 New, Rcd, Sel, Subs, Term, Test, Tup, With, Var}
import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet
import scala.collection.mutable.ArrayBuffer
import mlscript.Cls
import mlscript.CaseBranches

object Monomorph:
  private val debug = RainbowDebug()

  private val funProtos = MutMap[String, NuFunDef]()
  private val funImpls = MutMap[String, ArrayBuffer[NuFunDef]]()

  private val tyProtos = MutMap[String, NuTypeDef]()
  private val tyImpls = MutMap[String, ArrayBuffer[NuTypeDef]]()
  private val allTyImpls = ArrayBuffer[NuTypeDef]()

  private val lamTyDefs = MutMap[String, NuTypeDef]()

  def specializedTypeDefs: List[NuTypeDef] = allTyImpls.toList

  def monomprphize(tu: TypingUnit): TypingUnit = debug.trace("MONO", PrettyPrinter.show(tu)) {
    TypingUnit(tu.entities.map {
      case Left(term) => Left(monomorphizeTerm(term))
      case Right(tyDef: NuTypeDef) => 
        tyProtos.addOne((tyDef.nme.name, tyDef))
        tyImpls.addOne((tyDef.nme.name, ArrayBuffer()))
        Right(tyDef)
      case Right(funDef: NuFunDef) =>
        funProtos.addOne((funDef.nme.name, funDef))
        funImpls.addOne((funDef.nme.name, ArrayBuffer()))
        Right(monomorphizeFunDef(funDef))
    })
  }()

  def monomorphizeTerm(term: Term): Term =
    debug.trace[Term]("TERM", PrettyPrinter.show(term)) {
      term match
        // What's the point to monomorphize a non-class construction?
        case New(None, body) =>
          throw new MonomorphError("the head of `New` should not be `None`")
        case New(Some((TypeName(name), term)), body) =>
          // I think `term` should always be a `Tuple`.
          val args = term match
            case Tup(terms) => terms.map { case (_, (term, _)) => term }
            case term: Term => term :: Nil
          specializeNew(name, args, body)
        case Lam(Tup(fields), body) =>
          val params = fields.map {
            case (_, (Var(name), _)) => name
            case _ => throw new MonomorphError("the argument of Lam should be Var")
          }
          // TODO: Capture variables referenced in the lambda body.
          // We should capture: closure variables and referenced type variables.
          val lambdaClassName = s"Lambda$$${lamTyDefs.size}"
          val lambdaClassBody = TypingUnit(Right(NuFunDef(Var("apply"), Nil, Nil, Left(body))) :: Nil)
          val lambdaClassDef = NuTypeDef(Cls, TypeName(lambdaClassName), Nil, Nil, Nil, lambdaClassBody)
          lamTyDefs.addOne((lambdaClassName, lambdaClassDef))
          // Returns a class construction.
          New(Some((TypeName(lambdaClassName), Tup(Nil))), TypingUnit(Nil))
        case Lam(_, _) => throw new MonomorphError("the first argument of Lam should be Tup")
        case term => term.map(monomorphizeTerm)
    }(PrettyPrinter.show)

  // `new C(...) { ... }` expressions are converted into
  // `{ class CImpl extends C(...) { ... }; CImpl() }`.
  // This requires you to add a `LetClass` construct to `mlscript.Term`.
  def specializeNew(name: String, args: List[Term], body: TypingUnit): Term =
    debug.trace("NEW", name + args.iterator.map(_.toString).mkString("(", ", ", ")") + " with " + PrettyPrinter.show(body)) {
      val specTyDef = monomorphizeTypeDef(name, args)
      App(Var(specTyDef.nme.name), Tup(Nil))
    }(PrettyPrinter.show)

  // Monomorphize the given class with given arguments.
  def monomorphizeTypeDef(name: String, args: List[Term]): NuTypeDef =
    debug.trace("TYPE", name + args.map(PrettyPrinter.show(_)).mkString("(", ", ", ")")) {
      tyProtos.get(name) match {
        case Some(NuTypeDef(kind, nme, tparams, specParams, parents, body)) =>
          val tyDefImpls = tyImpls(name)
          val implClassName = s"$name$$${tyDefImpls.size}"
          // How to put args into `specParams`?
          val specTyDef = NuTypeDef(kind, TypeName(implClassName), tparams, specParams, parents, body)
          tyDefImpls += specTyDef
          allTyImpls += specTyDef
          specTyDef
        case None => throw new MonomorphError(s"undeclared type $name")
      }
    }()

  def monomorphizeFunDef(funDef: NuFunDef): NuFunDef =
    debug.trace("FUNC", PrettyPrinter.show(funDef)) {
      funImpls.addOne((funDef.nme.name, ArrayBuffer()))
      funDef
    }(PrettyPrinter.show)

  def isStatic(term: Term): Boolean =
    def go(term: Term)(using staticNames: Set[String]): Boolean =
      term match
        case With(trm, Rcd(fields)) =>
          go(trm) && fields.forall { case (_, (term, _)) => go(term) }
        case Rcd(fields) => fields.forall { case (_, (term, _)) => go(term) }
        case Tup(fields) => fields.forall { case (_, (term, _)) => go(term) }
        case Test(trm, _) => go(trm)
        case Block(TypingUnit(entities)) => false
        case Assign(lhs, rhs) => go(lhs) && go(rhs)
        case Subs(arr, idx) => go(arr) && go(idx)
        case New(head, body) => false
        case CaseOf(trm, cases) => go(trm) && goCaseBranch(cases)
        case Bind(lhs, rhs) => go(lhs) && go(rhs)
        case Sel(receiver, _) => go(receiver)
        // If a lambda captures nothing, we regard it as static.
        case Lam(Tup(fields), rhs) =>
          // Collect parameter names.
          val names = fields.map {
            case (_, (Var(name), _)) => name
            case _ => throw new MonomorphError("currently only supports `Var` as parameters")
          }
          go(rhs)(using staticNames ++ names)
        case Lam(_, rhs) =>
          throw MonomorphError("the first argument of `Lam` should be `Tup`")
        case App(lhs, rhs) => go(lhs) && go(rhs)
        case Blk(stmts) => stmts.forall {
          case term: Term => go(term)
          case _ => false
        }
        case Let(isRec, Var(name), rhs, body) =>
          go(rhs) && go(body)(using staticNames + name)
        case Asc(trm, _) => go(trm)
        case Bra(_, trm) => go(trm)
        case _: Lit => true
        case Var(name) => staticNames contains name
    def goCaseBranch(branch: CaseBranches)(using staticNames: Set[String]): Boolean =
      import mlscript.{Case, Wildcard, NoCases}
      branch match {
        case Case(_, body, rest) => go(body) && goCaseBranch(rest)
        case Wildcard(body) => go(body)
        case NoCases => true
      }
    go(term)(using Set[String]())

