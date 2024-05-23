package mlscript

import mlscript.utils._, shorthands._, algorithms._
import mlscript.codegen._
import scala.collection.mutable.{ListBuffer, HashMap, HashSet}
import mlscript.{JSField, JSLit}
import scala.collection.mutable.{Set => MutSet}
import scala.util.control.NonFatal
import scala.util.chaining._

abstract class JSBackend {
  def oldDefs: Bool

  protected implicit class TermOps(term: Term) {
    def isLam: Bool = term match {
      case _: Lam => true
      case Bra(false, inner) => inner.isLam
      case Asc(inner, _) => inner.isLam
      case _ => false
    }
  }
  
  /**
    * The root scope of the program.
    */
  protected val topLevelScope = Scope("root")

  /**
    * The prelude code manager.
    */
  protected val polyfill = Polyfill()

  /**
    * This function translates parameter destructions in `def` declarations.
    *
    * The production rules of MLscript `def` parameters are:
    *
    *     subterm ::= "(" term ")" | record | literal | identifier
    *     term ::= let | fun | ite | withsAsc | _match
    *
    * JavaScript supports following destruction patterns:
    *
    * - Array patterns: `[x, y, ...]` where `x`, `y` are patterns.
    * - Object patterns: `{x: y, z: w, ...}` where `z`, `w` are patterns.
    * - Identifiers: an identifier binds the position to a name.
    *
    * This function only translate name patterns and object patterns. I was thinking if we can
    * support literal parameter matching by merging multiple function `def`s into one.
    */
  private def translatePattern(t: Term)(implicit scope: Scope): JSPattern = t match {
    // fun x -> ... ==> function (x) { ... }
    // should returns ("x", ["x"])
    case Var(name) =>
      val runtimeName = scope.declareParameter(name)
      JSNamePattern(runtimeName)
    // fun { x, y } -> ... ==> function ({ x, y }) { ... }
    // should returns ("{ x, y }", ["x", "y"])
    case Rcd(fields) =>
      JSObjectPattern(fields map {
        case (Var(nme), Fld(_, Var(als))) =>
          val runtimeName = scope.declareParameter(als)
          val fieldName = JSField.emitValidFieldName(nme)
          if (runtimeName === fieldName) fieldName -> N
          else fieldName -> S(JSNamePattern(runtimeName))
        case (Var(nme), Fld(_, subTrm)) => 
          JSField.emitValidFieldName(nme) -> S(translatePattern(subTrm))
      })
    // This branch supports `def f (x: int) = x`.
    case Asc(trm, _) => translatePattern(trm)
    // Replace literals with wildcards.
    case _: Lit      => JSWildcardPattern()
    case Bra(_, trm) => translatePattern(trm)
    case Tup(fields) => JSArrayPattern(fields map { case (_, Fld(_, t)) => translatePattern(t) })
    // Others are not supported yet.
    case TyApp(base, _) =>
      translatePattern(base)
    case Inst(bod) => translatePattern(bod)
    case Ann(ann, receiver) => translatePattern(receiver)
    case _: Lam | _: App | _: Sel | _: Let | _: Blk | _: Bind | _: Test | _: With | _: CaseOf | _: Subs | _: Assign
        | _: If | _: New  | _: NuNew | _: Splc | _: Forall | _: Where | _: Super | _: Eqn | _: AdtMatchWith
        | _: Rft | _: While | _: Quoted | _: Unquoted =>
      throw CodeGenError(s"term $t is not a valid pattern")
  }

  private def translateParams(t: Term)(implicit scope: Scope): Ls[JSPattern] = t match {
    case Tup(params) => params map {
      case N -> Fld(_, p) => translatePattern(p)
      case S(nme) -> Fld(_, p) => translatePattern(nme)
    }
    case _           => throw CodeGenError(s"term $t is not a valid parameter list")
  }

  // Set `requireActualCls` to true if we need the actual class rather than the constrcutor function (if the class has)
  private def translateNuTypeSymbol(sym: NuTypeSymbol, requireActualCls: Bool)(implicit scope: Scope): JSExpr = {
    val trm = sym.qualifier.fold[JSExpr](JSIdent(sym.name))(qualifier => {
      scope.resolveQualifier(qualifier).visited = true
      JSIdent(qualifier).member(sym.name)
    })
    if (requireActualCls && !sym.isPlainJSClass) trm.member("class") else trm
  }

  protected def translateVar(name: Str, isCallee: Bool)(implicit scope: Scope): JSExpr =
    translateVarImpl(name, isCallee).fold(throw _, identity)
  
  /** Try to retrieve a name from the scope, returning a Left value if the name is not found,
    * a Right value if it is found, and throwing an exception in case of unrecoverable error. */
  protected def translateVarImpl(name: Str, isCallee: Bool)(implicit scope: Scope): Either[CodeGenError, JSExpr] =
    Right(scope.resolveValue(name) match {
      case S(sym: BuiltinSymbol) =>
        sym.accessed = true
        if (!polyfill.used(sym.feature))
          polyfill.use(sym.feature, sym.runtimeName)
        val ident = JSIdent(sym.runtimeName)
        if (sym.feature === "error") ident() else ident
      case S(sym: StubValueSymbol) =>
        if (sym.accessible)
          JSIdent(sym.runtimeName)
        else
          throw new UnimplementedError(sym)
      case S(sym: ValueSymbol) =>
        if (sym.isByvalueRec.getOrElse(false) && !sym.isLam) throw CodeGenError(s"unguarded recursive use of by-value binding $name")
        sym.visited = true
        val ident = JSIdent(sym.runtimeName)
        if (sym.isByvalueRec.isEmpty && !sym.isLam) ident() else ident
      case S(sym: NuTypeSymbol) =>
        translateNuTypeSymbol(sym, isCallee) // `isCallee` is true in a `new` expression, which requires the actual class
      case S(sym: NewClassMemberSymbol) =>
        if (sym.isByvalueRec.getOrElse(false) && !sym.isLam) throw CodeGenError(s"unguarded recursive use of by-value binding $name")
        sym.qualifier.fold[JSExpr](throw CodeGenError(s"unqualified member symbol $sym"))(qualifier => {
          sym.visited = true
          scope.resolveQualifier(qualifier).visited = true
          val ident = if (sym.isPrivate) JSIdent(s"${qualifier}.#${sym.name}")
                      else JSIdent(qualifier).member(sym.name)
          if (sym.isByvalueRec.isEmpty && !sym.isLam) ident() else ident
        })
      case S(sym: ClassSymbol) =>
        if (isCallee || !oldDefs)
          JSNew(JSIdent(sym.runtimeName))
        else
          JSArrowFn(JSNamePattern("x") :: Nil, L(JSNew(JSIdent(sym.runtimeName))(JSIdent("x"))))
      case S(sym: TraitSymbol) =>
        if (oldDefs) JSIdent(sym.lexicalName)("build")
        else return Left(CodeGenError(s"trait used in term position"))
      case N => scope.getType(name) match {
        case S(sym: TypeAliasSymbol) =>
          return Left(CodeGenError(s"type alias ${name} is not a valid expression"))
        case S(_) => lastWords("register mismatch in scope")
        case N =>
          return Left(CodeGenError(s"unresolved symbol ${name}"))
      }
    })

  /**
    * Handle all possible cases of MLscript function applications. We extract
    * this method to prevent exhaustivity check from reaching recursion limit.
    */
  protected def translateApp(term: App)(implicit scope: Scope): JSExpr = term match {
    // Binary expressions
    case App(App(Var(op), Tup((N -> Fld(_, lhs)) :: Nil)), Tup((N -> Fld(_, rhs)) :: Nil))
        if oldDefs && (JSBinary.operators contains op) =>
      JSBinary(op, translateTerm(lhs), translateTerm(rhs))
    // Binary expressions with new-definitions
    case App(Var(op), Tup(N -> Fld(_, lhs) :: N -> Fld(_, rhs) :: Nil)) // JS doesn't support operators like `+.` so we need to map them before testing
        if JSBinary.operators.contains(mapFloatingOperator(op)) && (!translateVarImpl(op, isCallee = true).isRight || op =/= mapFloatingOperator(op)) =>
      JSBinary(mapFloatingOperator(op), translateTerm(lhs), translateTerm(rhs))
    // If-expressions
    case App(App(App(Var("if"), Tup((_, Fld(_, tst)) :: Nil)), Tup((_, Fld(_, con)) :: Nil)), Tup((_, Fld(_, alt)) :: Nil)) =>
      JSTenary(translateTerm(tst), translateTerm(con), translateTerm(alt))
    case App(App(App(Var("if"), tst), con), alt) => die
    // Function invocation
    case App(trm, Tup(args)) =>
      val callee = trm match {
        case Var(nme) if oldDefs => scope.resolveValue(nme) match {
          case S(sym: NuTypeSymbol) =>
            translateNuTypeSymbol(sym, false) // ClassName(params)
          case _ => translateVar(nme, true) // Keep this case for the legacy test cases
        }
        case _ => translateTerm(trm)
      }
      callee(args map { case (_, Fld(_, arg)) => translateTerm(arg) }: _*)
    case App(trm, splice) => ??? // TODO represents `trm(...splice)`
    case _ => throw CodeGenError(s"ill-formed application $term")
  }

  // * Generate an `App` node for AST constructors
  private def createASTCall(tp: Str, args: Ls[Term]): App =
    App(Var(tp), Tup(args.map(a => N -> Fld(FldFlags.empty, a))))

  // * Bound free variables appearing in quasiquotes
  class FreeVars(val vs: Set[Str])

  // * Left: the branch is quoted and it has been desugared
  // * Right: the branch is not quoted and quoted subterms have been desugared
  private def desugarQuotedBranch(branch: CaseBranches)(
    implicit scope: Scope, isQuoted: Bool, freeVars: FreeVars
  ): Either[Term, CaseBranches] = branch match {
    case cse @ Case(pat, body, rest) =>
      val dp = desugarQuote(pat)
      val db = desugarQuote(body)
      desugarQuotedBranch(rest) match {
        case L(t) => L(createASTCall("Case", dp :: db :: t :: Nil))
        case R(b) => dp match {
          case dp: SimpleTerm => R(Case(dp, db, b)(cse.refined))
          case _ => die
        }
      }
    case Wildcard(body) =>
      if (isQuoted) L(createASTCall("Wildcard", desugarQuote(body) :: Nil)) else R(Wildcard(desugarQuote(body)))
    case NoCases => if (isQuoted) L(createASTCall("NoCases", Nil)) else R(NoCases)
  }

  // * Operators `+`, `-`, and `*` will not be available for floating numbers until we have the correct overloading.
  // * Currently, we use OCaml-style floating operators temporarily and translate them into normal JS operators.
  private def mapFloatingOperator(op: Str) = op match {
    case "+." => "+"
    case "-." => "-"
    case "*." => "*"
    case _ => op
  }

  // * Desugar `Quoted` into AST constructor invocations.
  // * example 1: `` `42 `` is desugared into `IntLit(42)`
  // * example 2: `` x `=> id(x) `+ `1 `` is desugared into `let x1 = freshName("x") in Lam(Var(x1), App(Var("+"), id(Var(x1)), IntLit(1)))`
  private def desugarQuote(term: Term)(implicit scope: Scope, isQuoted: Bool, freeVars: FreeVars): Term = term match {
    case Var(name) =>
      val isFreeVar = freeVars.vs(name)
      if (isQuoted || isFreeVar) {
        val runtimeName = scope.resolveValue(name).fold[Str](
          throw CodeGenError(s"unbound free variable $name is not supported yet.")
        )(_.runtimeName)
        if (isFreeVar) createASTCall("Var", Var(runtimeName) :: Nil) // quoted variables
        else createASTCall("Var", StrLit(runtimeName) :: Nil) // built-in symbols (e.g., true, error)
      }
      else term
    case lit: IntLit => if (isQuoted) createASTCall("IntLit", lit :: Nil) else lit
    case lit: DecLit => if (isQuoted) createASTCall("DecLit", lit :: Nil) else lit
    case lit: StrLit => if (isQuoted) createASTCall("StrLit", lit :: Nil) else lit
    case lit: UnitLit => if (isQuoted) createASTCall("UnitLit", lit :: Nil) else lit
    case Lam(params, body) =>
      if (isQuoted) {
        val lamScope = scope.derive("Lam")
        params match {
          case Tup(params) =>
            val newfreeVars = params.map {
              case N -> Fld(_, Var(nme)) =>
                lamScope.declareParameter(nme)
                nme -> lamScope.declareValue(nme, S(false), false, N).runtimeName
              case S(Var(nme)) -> _ =>
                lamScope.declareParameter(nme)
                nme -> lamScope.declareValue(nme, S(false), false, N).runtimeName
              case p => throw CodeGenError(s"parameter $p is not supported in quasiquote")
            }
            newfreeVars.foldRight(desugarQuote(body)(lamScope, isQuoted, new FreeVars(freeVars.vs ++ newfreeVars.map(_._1))))((p, res) =>
              Let(false, Var(p._2), createASTCall("freshName", StrLit(p._1) :: Nil), createASTCall("Lam", createASTCall("Var", Var(p._2) :: Nil) :: res :: Nil)))
          case _  => throw CodeGenError(s"term $params is not a valid parameter list")
        }
      }
      else Lam(params, desugarQuote(body))
    case Unquoted(body) =>
      if (isQuoted) {
        val unquoteScope = scope.derive("unquote")
        desugarQuote(body)(unquoteScope, false, freeVars)
      }
      else throw CodeGenError("unquoted term should be wrapped by quotes.")
    case Quoted(body) =>
      val quoteScope = scope.derive("quote")
      val res = desugarQuote(body)(quoteScope, true, freeVars)
      if (isQuoted) throw CodeGenError("nested quotation is not allowed.")
      else res
    case App(Var(op), Tup(N -> Fld(f1, lhs) :: N -> Fld(f2, rhs) :: Nil))
        if JSBinary.operators.contains(mapFloatingOperator(op)) && (!translateVarImpl(op, isCallee = true).isRight || op =/= mapFloatingOperator(op)) =>
      if (isQuoted)
        createASTCall("App", createASTCall("Var", StrLit(mapFloatingOperator(op)) :: Nil) :: desugarQuote(lhs) :: desugarQuote(rhs) :: Nil)
      else
        App(Var(op), Tup(N -> Fld(f1, desugarQuote(lhs)) :: N -> Fld(f2, desugarQuote(rhs)) :: Nil))
    case App(lhs, rhs) =>
      if (isQuoted) createASTCall("App", desugarQuote(lhs) :: desugarQuote(rhs) :: Nil)
      else App(desugarQuote(lhs), desugarQuote(rhs))
    case Rcd(fields) =>
      if (isQuoted) createASTCall("Rcd", fields.flatMap(f => createASTCall("Var", StrLit(f._1.name) :: Nil) :: desugarQuote(f._2.value) :: Nil))
      else Rcd(fields.map(f => (f._1, Fld(f._2.flags, desugarQuote(f._2.value)))))
    case Bra(rcd, trm) =>
      if (isQuoted) createASTCall("Bra", desugarQuote(trm) :: Nil)
      else Bra(rcd, desugarQuote(trm))
    case Sel(receiver, f @ Var(name)) =>
      if (isQuoted) createASTCall("Sel", desugarQuote(receiver) :: createASTCall("Var", StrLit(name) :: Nil) :: Nil)
      else Sel(desugarQuote(receiver), f)
    case Let(rec, Var(name), value, body) =>
      val letScope = scope.derive("Let")
      if (isQuoted) {
        letScope.declareParameter(name)
        val freshedName = letScope.declareValue(name, S(false), false, N).runtimeName
        Let(false, Var(freshedName), createASTCall("freshName", StrLit(name) :: Nil),
          createASTCall("Let", createASTCall("Var", Var(freshedName) :: Nil) :: desugarQuote(value)
            :: desugarQuote(body)(letScope, isQuoted, new FreeVars(freeVars.vs ++ (name :: Nil))) :: Nil
        ))
      }
      else Let(rec, Var(name), desugarQuote(value), desugarQuote(body)(letScope, isQuoted, freeVars))
    case Blk(stmts) =>
      val blkScope = scope.derive("blk")
      if (isQuoted) createASTCall("Blk", stmts.map {
        case t: Term =>
          desugarQuote(t)(blkScope, isQuoted, freeVars)
        case s => throw CodeGenError(s"statement $s is not supported in quasiquotes")
      })
      else Blk(stmts.map {
        case t: Term =>
          desugarQuote(t)(blkScope, isQuoted, freeVars)
        case s => desugarStatementInUnquote(s)(blkScope, freeVars)
      })
    case Tup(eles) =>
      def toVar(b: Bool) = if (b) Var("true") else Var("false")
      def toVars(flg: FldFlags) = toVar(flg.mut) :: toVar(flg.spec) :: toVar(flg.genGetter) :: Nil
      if (isQuoted) createASTCall("Tup", eles flatMap {
        case S(Var(name)) -> Fld(flags, t) =>
          createASTCall("Var", Var(name) :: Nil) :: createASTCall("Fld", desugarQuote(t) :: toVars(flags)) :: Nil
        case N -> Fld(flags, t) => createASTCall("Fld", desugarQuote(t) :: toVars(flags)) :: Nil
      })
      else Tup(eles.map {
        case v -> Fld(flags, t) => v -> Fld(flags, desugarQuote(t))
      })
    case Subs(arr, idx) =>
      if (isQuoted) createASTCall("Subs", desugarQuote(arr) :: desugarQuote(idx) :: Nil)
      else Subs(desugarQuote(arr), desugarQuote(idx))
    case Asc(trm, ty) =>
      if (isQuoted) desugarQuote(trm)
      else Asc(desugarQuote(trm), ty)
    case With(lhs, rhs @ Rcd(fields)) =>
      if (isQuoted) createASTCall("With", desugarQuote(lhs) :: desugarQuote(rhs) :: Nil)
      else With(desugarQuote(lhs), Rcd(fields.map(f => (f._1, Fld(f._2.flags, desugarQuote(f._2.value))))))
    case CaseOf(trm, cases) =>
      desugarQuotedBranch(cases) match {
        case L(t) => createASTCall("CaseOf", desugarQuote(trm) :: t :: Nil)
        case R(b) => CaseOf(desugarQuote(trm), b)
      }
    case _ if term.desugaredTerm.isDefined => desugarQuote(term.desugaredTerm.getOrElse(die))
    case Assign(lhs, rhs) if !isQuoted => Assign(desugarQuote(lhs), desugarQuote(rhs))
    case NuNew(cls) if !isQuoted => NuNew(desugarQuote(cls))
    case TyApp(lhs, targs) if !isQuoted => TyApp(desugarQuote(lhs), targs)
    case Forall(p, body) if !isQuoted => Forall(p, desugarQuote(body))
    case Inst(body) if !isQuoted => Inst(desugarQuote(body))
    case _: Super if !isQuoted => term
    case Eqn(lhs, rhs) if !isQuoted => Eqn(lhs, desugarQuote(rhs))
    case Ann(ann, receiver) => Ann(desugarQuote(ann), desugarQuote(receiver))
    case While(cond, body) if !isQuoted => While(desugarQuote(cond), desugarQuote(body))
    case _: Bind | _: Test | _: If  | _: Splc | _: Where | _: AdtMatchWith | _: Rft | _: New
        | _: Assign | _: NuNew | _: TyApp | _: Forall | _: Inst | _: Super | _: Eqn | _: While =>
      throw CodeGenError("this quote syntax is not supported yet.")
  }

  // * Statements inside **Unquote** can refer to quoted code fragments.
  // * Desugar them recursively.
  private def desugarStatementInUnquote(s: Statement)(implicit scope: Scope, freeVars: FreeVars): Statement = {
    implicit val isQuoted: Bool = false
    s match {
      case nd @ NuFunDef(isLetRec, nme, symbol, tparams, rhs) =>
        NuFunDef(isLetRec, nme, symbol, tparams, rhs match {
          case L(t) => L(desugarQuote(t))
          case R(t) => R(t)
        })(nd.declareLoc, nd.virtualLoc, nd.mutLoc, nd.signature, nd.outer, nd.genField, nd.annotations)
      case nt @ NuTypeDef(kind, nme, tparams, params, ctor, sig, parents, superAnnot, thisAnnot, TypingUnit(body)) =>
        NuTypeDef(kind, nme, tparams, params, ctor.map(c => desugarStatementInUnquote(c) match {
          case c: Constructor => c
          case _ => die
        }), sig, parents.map(p => desugarQuote(p)), superAnnot, thisAnnot, TypingUnit(body.map(s => desugarStatementInUnquote(s))))(nt.declareLoc, nt.abstractLoc, nt.annotations)
      case Constructor(ps, body) => Constructor(ps, desugarQuote(body) match {
        case b: Blk => b
        case _ => die
      })
      case t: Term => desugarQuote(t)
      case _: LetS | _: DataDefn | _: DatatypeDefn | _: TypeDef | _: Def => die // * Impossible. newDef is true
    }
  }

  /**
    * Translate MLscript terms into JavaScript expressions.
    */
  protected def translateTerm(term: Term)(implicit scope: Scope): JSExpr = term match {
    case _ if term.desugaredTerm.isDefined => translateTerm(term.desugaredTerm.getOrElse(die))
    case Var(name) => translateVar(name, false)
    case Super() => JSIdent("super")
    case Lam(params, body) =>
      val lamScope = scope.derive("Lam")
      val patterns = translateParams(params)(lamScope)
      JSArrowFn(patterns, lamScope.tempVars `with` translateTerm(body)(lamScope))
    case t: App => translateApp(t)
    case Rcd(fields) =>
      JSRecord(fields map { case (key, Fld(_, value)) =>
        key.name -> translateTerm(value)
      })
    case Sel(receiver, fieldName) =>
      JSField(translateTerm(receiver), fieldName.name)
    // Turn let into an IIFE.
    case Let(true, Var(name), Lam(args, body), expr) =>
      val letScope = scope.derive("Let")
      val runtimeName = letScope.declareParameter(name)
      val fn = {
        val fnScope = letScope.derive("Function")
        val params = translateParams(args)(fnScope)
        val fnBody = fnScope.tempVars.`with`(translateTerm(body)(fnScope))
        JSFuncExpr(S(runtimeName), params, fnBody.fold(_.`return` :: Nil, identity))
      }
      JSImmEvalFn(
        N,
        JSNamePattern(runtimeName) :: Nil,
        letScope.tempVars.`with`(translateTerm(expr)(letScope)),
        fn :: Nil
      )
    case Let(true, Var(name), _, _) =>
      throw new CodeGenError(s"recursive non-function definition $name is not supported")
    case Let(_, Var(name), value, body) =>
      val letScope = scope.derive("Let")
      val runtimeName = letScope.declareParameter(name)
      JSImmEvalFn(
        N,
        JSNamePattern(runtimeName) :: Nil,
        letScope.tempVars `with` translateTerm(body)(letScope),
        translateTerm(value) :: Nil
      )
    case Blk(stmts) =>
      val blkScope = scope.derive("Blk")
      val flattened = stmts.iterator.flatMap {
        case nt: NuTypeDef => nt :: Nil
        case nf @ NuFunDef(_, Var(nme), symNme, _, _) =>
          val symb = symNme.map(_.name)
          blkScope.declareStubValue(nme, symb)(true)
          nf.desugared._2
        case other => other.desugared._2
      }.toList
      JSImmEvalFn(
        N,
        Nil,
        R(blkScope.tempVars `with` (flattened.iterator.zipWithIndex.map {
          case (t: Term, index) if index + 1 == flattened.length => translateTerm(t)(blkScope).`return`
          case (t: Term, index)                                  => JSExprStmt(translateTerm(t)(blkScope))
          case (NuFunDef(isLetRec, Var(nme), symNme, _, L(rhs)), _) =>
            val symb = symNme.map(_.name)
            val isLocalFunction = isLetRec.isEmpty || rhs.isLam
            val pat = blkScope.declareValue(nme, isLetRec, isLocalFunction, symb)
            JSLetDecl(Ls(pat.runtimeName -> S(translateTerm(rhs)(blkScope))))
          case (nt: NuTypeDef, _) => translateLocalNewType(nt)(blkScope)
          // TODO: find out if we need to support this.
          case (_: Def | _: TypeDef | _: NuFunDef | _: DataDefn | _: DatatypeDefn | _: LetS | _: Constructor, _) =>
            throw CodeGenError("unsupported definitions in blocks")
        }.toList)),
        Nil
      )
    // Pattern match with only one branch -> comma expression
    case CaseOf(trm, Wildcard(default)) =>
      JSCommaExpr(translateTerm(trm) :: translateTerm(default) :: Nil)
    // Pattern match with two branches -> tenary operator
    case CaseOf(trm, cs @ Case(tst, csq, Wildcard(alt))) =>
      translateCase(translateTerm(trm), tst)(scope)(translateTerm(csq), translateTerm(alt))
    // Pattern match with more branches -> chain of ternary expressions with cache
    case CaseOf(trm, cases) =>
      val arg = translateTerm(trm)
      if (arg.isSimple) {
        translateCaseBranch(arg, cases)
      } else {
        val name = scope.declareRuntimeSymbol()
        scope.tempVars += name
        val ident = JSIdent(name)
        JSCommaExpr(JSAssignExpr(ident, arg) :: translateCaseBranch(ident, cases) :: Nil)
      }
    case IntLit(value) => JSLit(value.toString + (if (JSBackend isSafeInteger value) "" else "n"))
    case DecLit(value) => JSLit(value.toString)
    case StrLit(value) => JSExpr(value)
    case UnitLit(value) => JSLit(if (value) "undefined" else "null")
    // `Asc(x, ty)` <== `x: Type`
    case Asc(trm, _) => translateTerm(trm)
    // `c with { x = "hi"; y = 2 }`
    case With(trm, Rcd(fields)) =>
      JSInvoke(
        JSIdent(polyfill get "withConstruct" match {
          case S(fnName) => fnName
          case N         => polyfill.use("withConstruct", topLevelScope.declareRuntimeSymbol("withConstruct"))
        }),
        translateTerm(trm) :: JSRecord(fields map { case (Var(name), Fld(_, value)) =>
          name -> translateTerm(value)
        }) :: Nil
      )
    // Only parenthesize binary operators
    // Custom operators do not need special handling since they are desugared to plain methods
    case Bra(false, trm) => trm match { 
      case App(Var(op), _) if JSBinary.operators.contains(op) => JSParenthesis(translateTerm(trm)) 
      case trm => translateTerm(trm)
    }
    case Bra(_, trm) => translateTerm(trm)
    case Tup(terms) =>
      JSArray(terms map { case (_, Fld(_, term)) => translateTerm(term) })
    case Subs(arr, idx) =>
      JSMember(translateTerm(arr), translateTerm(idx))
    case While(cond, body) =>
      JSImmEvalFn(N, Nil, R(JSWhileStmt(translateTerm(cond), translateTerm(body)) :: Nil), Nil)
    case Assign(lhs, value) =>
      lhs match {
        case _: Subs | _: Sel | _: Var =>
          JSUnary("void", JSAssignExpr(translateTerm(lhs), translateTerm(value)))
        case _ =>
          throw CodeGenError(s"illegal assignemnt left-hand side: $lhs")
      }
    case Inst(bod) => translateTerm(bod)
    case iff: If =>
      throw CodeGenError(s"if expression was not desugared")
    case NuNew(cls) =>
      // * The following logic handles the case when `new C(123)` needs to be translated to `new C.class(123)`
      cls match {
        case Var(className) =>
          translateVar(className, isCallee = true) match {
            case n: JSNew => n
            case t => JSNew(t)
          }
        case _ => throw CodeGenError(s"Unsupported `new` class term: $cls")
      }
      // * Would not be quite correct:
      // JSNew(translateTerm(cls))
    case New(N, TypingUnit(Nil)) => JSRecord(Nil)
    case New(S(TypeName(className) -> Tup(args)), TypingUnit(Nil)) =>
      val callee = translateVar(className, true) match {
        case n: JSNew => n
        case t => JSNew(t)
      }
      callee(args.map { case (_, Fld(_, arg)) => translateTerm(arg) }: _*)
    case New(_, TypingUnit(_)) =>
      throw CodeGenError("custom class body is not supported yet")
    case Forall(_, bod) => translateTerm(bod)
    case TyApp(base, _) => translateTerm(base)
    case Eqn(Var(name), _) =>
      throw CodeGenError(s"assignment of $name is not supported outside a constructor")
    case Quoted(body) =>
      val quotedScope = scope.derive("quote")
      translateTerm(desugarQuote(body)(quotedScope, true, new FreeVars(Set.empty)))(quotedScope)
    case Ann(ann, receiver) => translateTerm(receiver)
    case _: Bind | _: Test | _: If  | _: Splc | _: Where | _: AdtMatchWith | _: Rft | _: Unquoted =>
      throw CodeGenError(s"cannot generate code for term $term")
  }

  private def translateCaseBranch(scrut: JSExpr, branch: CaseBranches)(implicit
      scope: Scope
  ): JSExpr = branch match {
    case Case(pat, body, rest) =>
      translateCase(scrut, pat)(scope)(translateTerm(body), translateCaseBranch(scrut, rest))
    case Wildcard(body) =>
      translateTerm(body)
    case NoCases        => JSImmEvalFn(N, Nil, R(JSInvoke(
      JSNew(JSIdent("Error")),
      JSExpr("non-exhaustive case expression") :: Nil
    ).`throw` :: Nil), Nil)
  }

  private def translateCase(scrut: JSExpr, pat: SimpleTerm)(implicit scope: Scope) = {
    JSTenary(
      pat match {
        case Var("int") =>
          JSInvoke(JSField(JSIdent("Number"), "isInteger"), scrut :: Nil)
        case Var("Int") if !oldDefs =>
          JSInvoke(JSField(JSIdent("Number"), "isInteger"), scrut :: Nil)
        case Var("Num") if !oldDefs =>
          JSBinary("===", scrut.typeof(), JSLit(JSLit.makeStringLiteral("number")))
        case Var("Bool") if !oldDefs =>
          JSBinary("===", scrut.typeof(), JSLit(JSLit.makeStringLiteral("boolean")))
        case Var("Str") if !oldDefs =>
          JSBinary("===", scrut.typeof(), JSLit(JSLit.makeStringLiteral("string")))
        case Var("bool") =>
          JSBinary("===", scrut.member("constructor"), JSLit("Boolean"))
        case Var(s @ ("true" | "false")) =>
          JSBinary("===", scrut, JSLit(s))
        case Var("string") =>
          // JS is dumb so `instanceof String` won't actually work on "primitive" strings...
          JSBinary("===", scrut.member("constructor"), JSLit("String"))
        case Var(name) => scope.resolveValue(name) match {
          case S(sym: NewClassSymbol) =>
            JSInstanceOf(scrut, translateNuTypeSymbol(sym, true)) // a is case ClassName(params) -> a instanceof ClassName.class
          case S(sym: ModuleSymbol) =>
            JSInstanceOf(scrut, translateNuTypeSymbol(sym, true))
          case _ => topLevelScope.getType(name) match {
            case S(ClassSymbol(_, runtimeName, _, _, _)) => JSInstanceOf(scrut, JSIdent(runtimeName))
            case S(TraitSymbol(_, runtimeName, _, _, _)) => JSIdent(runtimeName)("is")(scrut)
            case S(_: TypeAliasSymbol) => throw new CodeGenError(s"cannot match type alias $name")
            case _ => throw new CodeGenError(s"unknown match case: $name")
          }
        }
        case lit: Lit => JSBinary("===", scrut, translateTerm(lit))
      },
      _,
      _
    )
  }

  protected def translateTraitDeclaration(
      traitSymbol: TraitSymbol
  )(implicit scope: Scope): JSConstDecl = {
    import JSCodeHelpers._
    val instance = id("instance")
    val bases = traitSymbol.body.collectTypeNames.flatMap { name =>
      topLevelScope.getType(name) match {
        case S(t: TraitSymbol) => S(id(t.runtimeName)("implement")(instance).stmt)
        case S(_: ClassSymbol) | S(_: TypeSymbol) | N => N
      }
    }
    val members = traitSymbol.methods.map { method =>
      val name = method.nme.name
      val define = method.rhs.value match {
        // Define methods for functions.
        case Lam(params, body) =>
          val methodScope = scope.derive(s"Method $name")
          val methodParams = translateParams(params)(methodScope)
          methodScope.declareValue("this", Some(false), false, N)
          instance(name) := JSFuncExpr(
            N,
            methodParams,
            `return`(translateTerm(body)(methodScope)) :: Nil
          )
        // Define getters for pure expressions.
        case term =>
          val getterScope = scope.derive(s"Getter $name")
          getterScope.declareValue("this", Some(false), false, N)
          id("Object")("defineProperty")(
            instance,
            JSExpr(name),
            JSRecord(
              "get" -> JSFuncExpr(
                N,
                Nil,
                `return`(translateTerm(term)(getterScope)) :: Nil
              ) :: Nil
            )
          ).stmt
      }
      JSIfStmt(
        JSExpr(name).binary("in", instance).unary("!"),
        define :: Nil,
      )
    }
    val implement = JSFuncExpr(
      S("implement"),
      param("instance") :: Nil,
      JSIfStmt(
        id("tag").binary("in", instance),
        `return`() :: Nil,
      )
        :: id("Object")("defineProperty")(
          instance,
          id("tag"),
          JSRecord("value" -> JSRecord(Nil) :: Nil)
        ).stmt
        :: members
        ::: bases
    )
    // function build(instance) {
    //   if (typeof instance !== "object") {
    //     instance = Object.assign(instance, {});
    //   }
    //   this.implement(instance);
    //   return instance;
    // }
    val build = JSFuncExpr(
      S("build"),
      param("instance") :: Nil,
      JSIfStmt(
        instance.typeof().binary("!==", JSExpr("object")),
        (instance := id("Object")("assign")(instance, JSRecord(Nil))) :: Nil
      ) 
        :: id("this")("implement")(instance).stmt
        :: `return`(instance)
        :: Nil
    )
    val is = JSFuncExpr(
      S("is"),
      param("x") :: Nil,
      `return`(
        id("x").typeof()
          .binary("===", JSExpr("object"))
          .binary("&&", id("x").binary("!==", JSLit("null")))
          .binary("&&", id("tag").binary("in", id("x")))
      ) :: Nil
    )
    const(
      traitSymbol.runtimeName,
      JSFuncExpr(
        N,
        Nil,
        Ls(
          const("tag", id("Symbol")()),
          `return` {
            JSRecord("implement" -> implement :: "build" -> build :: "is" -> is :: Nil)
          }
        )
      )()
    )
  }
  /**
    * Translate MLscript class declaration to JavaScript class declaration.
    * First, we will analyze its fields and base class name.
    * Then, we will check if the base class exists.
    */
  protected def translateClassDeclaration(
      classSymbol: ClassSymbol,
      baseClassSymbol: Opt[ClassSymbol]
  )(implicit scope: Scope): JSClassDecl = {
    // Translate class methods and getters.
    val classScope = scope.derive(s"class ${classSymbol.lexicalName}")
    val members = classSymbol.methods.flatMap {
      translateClassMember(_)(classScope)
    }
    // Collect class fields.
    val fields = classSymbol.body.collectFields ++
      classSymbol.body.collectTypeNames.flatMap(resolveTraitFields)
    val base = baseClassSymbol.map { sym => JSIdent(sym.runtimeName) }
    val traits = classSymbol.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }
    JSClassDecl(classSymbol.runtimeName, fields, base, members, traits)
  }

  protected def translateQualifierDeclaration(qualifier: ValueSymbol): Ls[JSStmt] =
    if (qualifier.visited)
      JSConstDecl(qualifier.runtimeName, JSIdent("this")) :: Nil
    else Nil
  
  protected def addNuTypeToGlobalThis(typeDef: NuTypeDef, moduleName: Str) = {
    import JSCodeHelpers._
    typeDef match {
      case NuTypeDef(Mxn, TypeName(nme), _, _, _, _, _, _, _, _) =>
        JSAssignExpr(id("globalThis").member(nme), JSArrowFn(param("base") :: Nil, L(
          JSInvoke(id(moduleName).member(nme), id("base") :: Nil)
        ))).stmt
      case NuTypeDef(_, TypeName(nme), _, _, _, _, _, _, _, _) =>
        JSAssignExpr(id("globalThis").member(nme), id(moduleName).member(nme)).stmt
    }
  }

  protected def translateLocalNewType(typeDef: NuTypeDef)(implicit scope: Scope): JSConstDecl = {
    // TODO: support traitSymbols
    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols) = declareNewTypeDefs(typeDef :: Nil, N)

    val sym = classSymbols match {
      case s :: _ => S(s)
      case Nil => mixinSymbols match {
        case s :: _ => S(s)
        case Nil => moduleSymbols match {
          case s :: _ => S(s)
          case _ => N
        }
      }
    }
    sym match {
      case S(sym: NewClassSymbol) =>
        val localScope = scope.derive(s"local ${sym.name}")
        val nd = translateNewTypeDefinition(sym, N, false)(localScope)
        val ctorMth = localScope.declareValue("ctor", Some(false), false, N).runtimeName
        val (constructor, params) = translateNewClassParameters(nd)
        val initList =
          if (sym.isPlainJSClass)
            Ls(JSReturnStmt(S(JSIdent(sym.name))))
          else
            Ls(
              JSLetDecl.from(Ls(ctorMth)),
              JSAssignExpr(JSIdent(ctorMth), JSArrowFn(constructor, L(JSInvoke(JSNew(JSIdent(sym.name)), params)))).stmt,
              JSExprStmt(JSAssignExpr(JSIdent(ctorMth).member("class"), JSIdent(sym.name))),
              JSReturnStmt(S(JSIdent(ctorMth)))
            )
        JSConstDecl(sym.name, JSImmEvalFn(
          N, Nil, R(nd :: initList), Nil
        ))
      case S(sym: MixinSymbol) =>
        val localScope = scope.derive(s"local ${sym.name}")
        val base = localScope.declareValue("base", Some(false), false, N)
        val nd = translateNewTypeDefinition(sym, S(base), false)(localScope)
        JSConstDecl(sym.name, JSArrowFn(
          Ls(JSNamePattern(base.runtimeName)), R(Ls(
            JSReturnStmt(S(JSClassExpr(nd)))
          ))
        ))
      case S(sym: ModuleSymbol) =>
        val localScope = scope.derive(s"local ${sym.name}")
        val nd = translateNewTypeDefinition(sym, N, false)(localScope)
        val ins = localScope.declareValue("ins", Some(false), false, N).runtimeName
        JSConstDecl(sym.name, JSImmEvalFn(
          N, Nil, R(Ls(
            nd, JSLetDecl.from(Ls(ins)),
            JSAssignExpr(JSIdent(ins), JSInvoke(JSNew(JSIdent(sym.name)), Nil)).stmt,
            JSExprStmt(JSAssignExpr(JSIdent(ins).member("class"), JSIdent(sym.name))),
            JSReturnStmt(S(JSIdent(ins)))
          )), Nil
        ))
      case _ => throw CodeGenError(s"unsupported NuTypeDef in local blocks: $typeDef")
    }
  }

  protected def translateMixinDeclaration(
      mixinSymbol: MixinSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit getterScope: Scope): JSClassMethod = {
    val base = getterScope.declareValue("base", Some(false), false, N)

    val classBody = translateNewTypeDefinition(mixinSymbol, S(base), false)(getterScope)
    val qualifierStmt = mixinSymbol.qualifier.fold[JSConstDecl](die)(qualifier => JSConstDecl(qualifier, JSIdent("this")))
    JSClassMethod(mixinSymbol.name, Ls(JSNamePattern(base.runtimeName)),
      R((qualifierStmt :: Nil) ::: Ls(JSReturnStmt(S(JSClassExpr(classBody)))
      ))
    )
  }

  private def translateParents(superFields: Ls[Term], constructorScope: Scope)(implicit scope: Scope): Opt[JSExpr] = {
    def translateParent(current: Term, base: JSExpr, mixinOnly: Bool): JSExpr = {
      def resolveName(term: Term): Str = term match {
        case App(lhs, _) => resolveName(lhs)
        case Var(name) => name
        case Sel(_, Var(fieldName)) => fieldName
        case TyApp(lhs, _) => resolveName(lhs)
        case _ => throw CodeGenError("unsupported parents.")
      }

      val name = resolveName(current)

      scope.resolveValue(name) match {
        case Some(_: TraitSymbol) => base // TODO:
        case Some(sym: MixinSymbol) =>
          JSInvoke(translateNuTypeSymbol(sym, true), Ls(base)) // class D() extends B -> class D extends B.class
        case Some(sym: NuTypeSymbol) if !mixinOnly =>
          translateNuTypeSymbol(sym, true)
        case Some(t) => throw CodeGenError(s"unexpected parent symbol $t.")
        case N => throw CodeGenError(s"unresolved parent $name.")
      }
    }

    // for non-first parent classes, they must be mixins or we would get more than one parent classes,
    // which is not allowed in JS
    superFields match {
      case head :: tail => S(tail.foldLeft(
        translateParent(head, JSIdent("Object"), false)
      )((res, next) => translateParent(next, res, true)))
      case Nil => N
    }
  }

  protected def translateTopModuleDeclaration(
    moduleSymbol: ModuleSymbol,
    keepTopLevelScope: Bool
  )(implicit scope: Scope): JSClassNewDecl =
    translateNewTypeDefinition(moduleSymbol, N, keepTopLevelScope)

  protected def translateModuleDeclaration(
      moduleSymbol: ModuleSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit getterScope: Scope): JSClassGetter = {
    val decl = translateNewTypeDefinition(moduleSymbol, N, false)(getterScope)
    val privateIdent = JSIdent(s"this.#${moduleSymbol.name}")
    val qualifierStmt = moduleSymbol.qualifier.fold[JSConstDecl](die)(qualifier => JSConstDecl(qualifier, JSIdent("this")))
    JSClassGetter(moduleSymbol.name, R((qualifierStmt :: Nil) :::
      Ls(
        JSIfStmt(JSBinary("===", privateIdent, JSIdent("undefined")), Ls(
          decl,
          JSExprStmt(JSAssignExpr(privateIdent,
            JSNew(JSInvoke(JSIdent(moduleSymbol.name), Nil)))),
          JSExprStmt(JSAssignExpr(privateIdent.member("class"), JSIdent(moduleSymbol.name))),
        )),
        JSReturnStmt(S(privateIdent))
      )))
  }

  protected def translateNewClassParameters(classBody: JSClassNewDecl) = {
    val constructor = classBody.ctorParams.map(JSNamePattern(_))
    val params = classBody.ctorParams.map(JSIdent(_))
    (constructor, params)
  }

  protected def translateNewClassDeclaration(
      classSymbol: NewClassSymbol,
      siblingsMembers: Ls[RuntimeSymbol]
  )(implicit getterScope: Scope): JSClassGetter = {
    val classBody =
      translateNewTypeDefinition(classSymbol, N, false)(getterScope)
    val (constructor, params) = translateNewClassParameters(classBody)

    val privateIdent = JSIdent(s"this.#${classSymbol.name}")
    val qualifierStmt = classSymbol.qualifier.fold[JSConstDecl](die)(qualifier => JSConstDecl(qualifier, JSIdent("this")))
    val initList =
      if (classSymbol.isPlainJSClass)
        Ls(JSExprStmt(JSAssignExpr(privateIdent, JSIdent(classSymbol.name))))
      else
        Ls(
          JSExprStmt(JSAssignExpr(privateIdent,
            JSArrowFn(constructor, L(
              JSInvoke(JSIdent("Object").member("freeze"), Ls(JSInvoke(JSNew(JSIdent(classSymbol.name)), params)))
            )))),
          JSExprStmt(JSAssignExpr(privateIdent.member("class"), JSIdent(classSymbol.name))),
          JSExprStmt(JSAssignExpr(privateIdent.member("unapply"), JSIdent(classSymbol.name).member("unapply")))
        )
    JSClassGetter(classSymbol.name, R(qualifierStmt :: Ls(
      JSIfStmt(JSBinary("===", privateIdent, JSIdent("undefined")),
        JSExprStmt(JSClassExpr(classBody)) :: initList),
      JSReturnStmt(S(privateIdent))
    )))
  }

  protected def translateNewTypeDefinition(
    sym: TypeSymbol with NuTypeSymbol,
    baseSym: Opt[ValueSymbol],
    keepTopLevelScope: Bool
  )(implicit scope: Scope): JSClassNewDecl = {
    // * nuTypeScope: root scope
    // ** inheritanceScope: contains specialized parameters for `super(...)`
    // ** bodyScope: contains the part of the class between the `{...}`
    // *** constructorScope: contains variables in the ctor statements
    // *** memberScopes: contains member methods and variables
    val nuTypeScope = scope.derive(sym.toString)
    val inheritanceScope = nuTypeScope.derive(s"${sym.name} inheritance")
    val bodyScope = nuTypeScope.derive(s"${sym.name} body")
    val constructorScope = bodyScope.derive(s"${sym.name} constructor")

    val memberList = ListBuffer[RuntimeSymbol]() // pass to the getter of nested types
    val typeList = ListBuffer[Str]()

    // Store the scope for each member and the qualifier's name in the corresponding scope
    // Avoid `m._1` or `m._2` in the following code
    final case class QualifierPack(memberScope: Scope, qualifier: Str)

    val qualifierName = "qualifier"
    val memberScopes = (sym.nested.map(nd => {
      val memberScope = bodyScope.derive(s"member ${nd.name}")
      val sym = memberScope.declareQualifierSymbol(qualifierName)
      nd.name -> QualifierPack(memberScope, sym)
    }) ++ sym.methods.map(m => {
      val memberScope = bodyScope.derive(s"member ${m.nme.name}")
      val sym = memberScope.declareQualifierSymbol(qualifierName)
      m.nme.name -> QualifierPack(memberScope, sym)
    })).toMap

    // `qualifier` should always be the first value in the getter scope so all qualifiers should have the same name!
    val qualifier = memberScopes.values.headOption.fold(S(constructorScope.declareQualifierSymbol(qualifierName)))(mh => {
      memberScopes.values.foreach(m =>
        assert(m.qualifier === mh.qualifier, s"the expected qualifier's runtime name should be ${mh.qualifier}, ${m.qualifier} found")
      )
      assert(constructorScope.declareQualifierSymbol(mh.qualifier) === mh.qualifier)
      S(mh.qualifier)
    })

    val fields = sym.matchingFields ++
      sym.body.collectTypeNames.flatMap(resolveTraitFields)

    val getters = new ListBuffer[Bool -> Str]() // mut -> name

    val ctorParams = sym.ctorParams.fold(
      fields.map { f =>
          memberList += NewClassMemberSymbol(f, Some(false), false, !sym.publicCtors.contains(f), qualifier).tap(bodyScope.register)
          inheritanceScope.declareValue(f, Some(false), false, N).runtimeName
          constructorScope.declareValue(f, Some(false), false, N).runtimeName
        }
      )(lst => lst.map { p =>
          if (p._2) { // `constructor(val name)` will also generate a field and a getter
            memberList += NewClassMemberSymbol(p._1, Some(false), false, false, qualifier).tap(bodyScope.register)
            getters += false -> p._1
          }
          constructorScope.declareValue(p._1, Some(false), false, N).runtimeName // Otherwise, it is only available in the constructor
        })
    
    val initFields = getters.toList.map { case (mut, name) =>
      JSAssignExpr(JSIdent(s"this.#$name"), JSIdent(name)).stmt }

    sym.methods.foreach(
      md => memberList += NewClassMemberSymbol(md.nme.name, N, true, false, qualifier).tap(bodyScope.register)
    )
    sym.signatures.foreach(
      md => memberList += bodyScope.declareStubValue(md.nme.name, N)(true)
    )
    sym.ctor.foreach {
      case nd @ NuFunDef(rec, Var(nme), _, _, _) =>
        memberList += NewClassMemberSymbol(nme, rec, false, !nd.genField, qualifier).tap(bodyScope.register)
      case _ => ()
    }

    // TODO: support traitSymbols
    val (traitSymbols, classSymbols, mixinSymbols, moduleSymbols) = declareNewTypeDefs(sym.nested, qualifier)(bodyScope)

    if (keepTopLevelScope) // also declare in the top level for diff tests
      declareNewTypeDefs(sym.nested, N)(topLevelScope)
    classSymbols.foreach(s => {memberList += s; typeList += s.name})
    mixinSymbols.foreach(s => {memberList += s;})
    moduleSymbols.foreach(s => {memberList += s; typeList += s.name})
    val members = sym.methods.map(m => translateNewClassMember(m, fields, qualifier)(memberScopes.getOrElse(m.nme.name, die).memberScope)) ++
      mixinSymbols.map(s => translateMixinDeclaration(s, memberList.toList)(memberScopes.getOrElse(s.name, die).memberScope)) ++
      moduleSymbols.map(s => translateModuleDeclaration(s, memberList.toList)(memberScopes.getOrElse(s.name, die).memberScope)) ++
      classSymbols.map(s => translateNewClassDeclaration(s, memberList.toList)(memberScopes.getOrElse(s.name, die).memberScope))

    val base: Opt[JSExpr] = baseSym match {
      case Some(base) => S(JSIdent(base.runtimeName))
      case _ => translateParents(sym.superParameters, inheritanceScope)
    }

    val traits = sym.body.collectTypeNames.flatMap {
      name => scope.getType(name) match {
        case S(TraitSymbol(_, runtimeName, _, _, _)) => S(runtimeName)
        case S(_: ClassSymbol) => N
        case S(_: TypeSymbol) => N
        case N => N
      }
    }

    val (superParameters, rest) = if (baseSym.isDefined) {
      val rest = constructorScope.declareValue("rest", Some(false), false, N)
      (Ls(JSIdent(s"...${rest.runtimeName}")), S(rest.runtimeName))
    }
    else
      (sym.superParameters.map {
        case App(lhs, Tup(rhs)) => rhs map {
          case (_, Fld(_, trm)) => translateTerm(trm)(inheritanceScope)
        }
        case _ => Nil
      }.flatMap(_.reverse).reverse, N)

    val privateMems = new ListBuffer[Str]()
    val stmts = sym.ctor.flatMap {
      case Eqn(Var(name), rhs) => Ls(
        JSAssignExpr(JSIdent(s"this.#$name"), translateTerm(rhs)(constructorScope)).stmt,
        JSConstDecl(constructorScope.declareValue(name, S(false), false, N).runtimeName, JSIdent(s"this.#$name"))
      )
      case s: Term => JSExprStmt(translateTerm(s)(constructorScope)) :: Nil
      case nd @ NuFunDef(_, Var(nme), _, _, Left(rhs)) =>
        if (nd.genField) {
          getters += nd.isMut -> nme
          Ls[JSStmt](
            JSExprStmt(JSAssignExpr(JSIdent(s"this.#$nme"), translateTerm(rhs)(constructorScope))),
            JSConstDecl(constructorScope.declareValue(nme, S(false), false, N).runtimeName, JSIdent(s"this.#$nme"))
          )
        }
        else {
          val sym = bodyScope.resolveValue(nme) match {
            case Some(sym: NewClassMemberSymbol) => sym
            case _ => throw new AssertionError(s"error when handling $nme")
          }
          if (sym.visited || ctorParams.contains(nme)) { // This field is used in other methods, or it overrides the ctor parameter
            privateMems += nme
            Ls[JSStmt](
              JSExprStmt(JSAssignExpr(JSIdent(s"this.#$nme"), translateTerm(rhs)(constructorScope))),
              JSConstDecl(constructorScope.declareValue(nme, S(false), false, N).runtimeName, JSIdent(s"this.#$nme"))
            )
          }
          else
            JSConstDecl(constructorScope.declareValue(nme, S(false), false, N).runtimeName,
              translateTerm(rhs)(constructorScope)) :: Nil
        }
      case _ => Nil
    }

    val tempDecs = constructorScope.tempVars.emit() match {
      case S(decs) => decs :: Nil
      case _ => Nil
    }

    val staticMethods = sym.unapplyMtd match {
      // * Note: this code is a bad temporary hack until we have proper `unapply` desugaring
      case S(unapplyMtd) => unapplyMtd.rhs match {
        case Left(Lam(Tup(_ -> Fld(_, Var(nme)) :: Nil), Let(_, _, _, Tup(fields)))) =>
          val unapplyScope = nuTypeScope.derive(s"unapply ${sym.name}")
          val ins = unapplyScope.declareParameter(nme)
          JSClassMethod("unapply", JSNamePattern(ins) :: Nil, L(JSArray(fields.map {
            case _ -> Fld(_, trm) => trm match {
              case Sel(Var(ins), Var(f)) => JSIdent(s"$ins.$f")
              case _ => translateTerm(trm)
            } 
          }))) :: Nil
        case _ => throw CodeGenError(s"invalid unapply method in ${sym.name}")
      }
      case _ => Nil
    }

    val qualifierStmt = qualifier.fold[Ls[JSStmt]](Nil)(qualifier =>
      translateQualifierDeclaration(constructorScope.resolveQualifier(qualifier)))
    JSClassNewDecl(
      sym.name,
      fields,
      fields.filter(sym.publicCtors.contains(_)).map(false -> _) ++ getters.toList,
      privateMems.toList ++ fields,
      base,
      superParameters,
      ctorParams,
      rest,
      members,
      traits,
      qualifierStmt ++ tempDecs ++ initFields ++ stmts,
      typeList.toList,
      sym.ctorParams.isDefined,
      staticMethods
    )
  }

  /**
   * Translate class methods and getters.
   */
  private def translateClassMember(
      method: MethodDef[Left[Term, Type]],
  )(implicit scope: Scope): Ls[JSClassMemberDecl] = {
    val name = method.nme.name
    // Create the method/getter scope.
    val memberScope = method.rhs.value match {
      case _: Lam => scope.derive(s"method $name")
      case _ => scope.derive(s"getter $name")
    }
    // Declare the alias for `this` before declaring parameters.
    val selfSymbol = memberScope.declareThisAlias()
    // Declare parameters.
    val (memberParams, body) = method.rhs.value match {
      case Lam(params, body) =>
        val methodParams = translateParams(params)(memberScope)
        (S(methodParams), body)
      case term =>
        (N, term)
    }
    // Translate class member body.
    val bodyResult = translateTerm(body)(memberScope).`return`
    // If `this` is accessed, add `const self = this`.
    val bodyStmts = if (selfSymbol.visited) {
      val thisDecl = JSConstDecl(selfSymbol.runtimeName, JSIdent("this"))
      R(thisDecl :: bodyResult :: Nil)
    } else {
      R(bodyResult :: Nil)
    }
    // Returns members depending on what it is.
    memberParams match {
      case S(memberParams) => JSClassMethod(name, memberParams, bodyStmts) :: Nil
      case N => JSClassGetter(name, bodyStmts) :: Nil
    }
  }

  private def translateNewClassMember(
    method: MethodDef[Left[Term, Type]],
    props: Ls[Str], // for overriding
    qualifier: Opt[Str]
  )(implicit memberScope: Scope): JSClassMemberDecl = {
    val name = method.nme.name
    val preDecs = props.map(p => {
      val runtime = memberScope.declareValue(p, Some(false), false, N)
      JSConstDecl(runtime.runtimeName, JSIdent(s"this.#$p"))
    })
    // Declare parameters.
    val (memberParams, body) = method.rhs.value match {
      case Lam(params, body) =>
        val methodParams = translateParams(params)(memberScope)
        (S(methodParams), body)
      case term =>
        (N, term)
    }
    // Translate class member body.
    val bodyResult = translateTerm(body)(memberScope).`return`
    val tempDecs = memberScope.tempVars.emit() match {
      case S(decs) => decs :: Nil
      case _ => Nil
    }

    val qualifierStmts = qualifier.fold[Ls[JSStmt]](Nil)(qualifier =>
      translateQualifierDeclaration(memberScope.resolveQualifier(qualifier)))

    val bodyStmts = R(preDecs ++ tempDecs ++ qualifierStmts ++ (bodyResult :: Nil))
    // Returns members depending on what it is.
    memberParams match {
      case S(memberParams) => JSClassMethod(name, memberParams, bodyStmts)
      case N => JSClassGetter(name, bodyStmts)
    }
  }

  /**
    * Declare symbols for types, traits and classes.
    * Call this before the code generation.
    * 
    * @return defined class symbols
    */
  protected def declareTypeDefs(typeDefs: Ls[TypeDef]): (Ls[TraitSymbol], Ls[ClassSymbol]) = {
    val traits = new ListBuffer[TraitSymbol]()
    val classes = new ListBuffer[ClassSymbol]()
    typeDefs.foreach {
      case TypeDef(Als, TypeName(name), tparams, body, _, _, _, _) =>
        topLevelScope.declareTypeAlias(name, tparams map { _.name }, body)
      case TypeDef(Trt, TypeName(name), tparams, body, _, methods, _, _) =>
        traits += topLevelScope.declareTrait(name, tparams map { _.name }, body, methods)
      case TypeDef(Cls, TypeName(name), tparams, baseType, _, members, _, _) =>
        classes += topLevelScope.declareClass(name, tparams map { _.name }, baseType, members)
      case TypeDef(Mxn, _, _, _, _, _, _, _) => throw CodeGenError("Mixins are not supported yet.")
      case TypeDef(Mod, _, _, _, _, _, _, _) => throw CodeGenError("Namespaces are not supported yet.")
    }
    (traits.toList, classes.toList)
  }

  protected def declareNewTypeDefs(typeDefs: Ls[NuTypeDef], qualifier: Opt[Str])(implicit scope: Scope):
      (Ls[TraitSymbol], Ls[NewClassSymbol], Ls[MixinSymbol], Ls[ModuleSymbol]) = {
    
    val traits = new ListBuffer[TraitSymbol]()
    val classes = new ListBuffer[NewClassSymbol]()
    val mixins = new ListBuffer[MixinSymbol]()
    val modules = new ListBuffer[ModuleSymbol]()
    
    def tt(trm: Term): Type = trm.toType match {
      case L(ds) => Top
      case R(ty) => ty
    }

    def prepare(nme: Str, fs: Ls[Opt[Var] -> Fld], pars: Ls[Term], unit: TypingUnit) = {
      val params = fs.map {
        case (S(nme), Fld(FldFlags(mut, spec, _), trm)) =>
          val ty = tt(trm)
          nme -> Field(if (mut) S(ty) else N, ty)
        case (N, Fld(FldFlags(mut, spec, _), nme: Var)) => nme -> Field(if (mut) S(Bot) else N, Top)
        case _ => die
      }
      val publicCtors = fs.filter {
        case (_, Fld(flags, _)) => flags.genGetter
        case _ => false
      }.map {
        case (S(name), _) => name.name
        case (N, Fld(_, nme: Var)) => nme.name
        case _ => die
      }

      val body = pars.map(tt).foldRight(Record(params): Type)(Inter)
      val implemented = new HashSet[Str]()
      val members = unit.entities.collect {
        case NuFunDef(isLetRec, mnme, _, tys, Left(rhs)) if (isLetRec.isEmpty || isLetRec.getOrElse(false)) =>
          implemented.add(mnme.name)
          MethodDef[Left[Term, Type]](isLetRec.getOrElse(false), TypeName(nme), mnme, tys, Left(rhs))
      }

      val signatures = unit.entities.collect {
        case nd @ NuFunDef(isLetRec, mnme, _, tys, Right(rhs)) if nd.genField && !implemented.contains(mnme.name) =>
          MethodDef[Right[Term, Type]](isLetRec.getOrElse(false), TypeName(nme), mnme, tys, Right(rhs))
      }

      val stmts = unit.entities.filter {
        case Asc(Var("this"), _) => false
        case Asc(Super(), _) => false
        case NuFunDef(S(false), _, _, _, Left(rhs)) => true
        case _: Term => true
        case _ => false
      }

      val nested = unit.entities.collect {
        case nd: NuTypeDef => nd
      }
      
      (body, members, signatures, stmts, nested, publicCtors)
    }

    typeDefs.foreach {
      case td @ NuTypeDef(Mxn, TypeName(mxName), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, signatures, stmts, nested, publicCtors) = prepare(mxName, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = MixinSymbol(mxName, tps map { _._2.name }, body, members, signatures, stmts, publicCtors, nested, qualifier).tap(scope.register)
        if (!td.isDecl) mixins += sym
      }
      case td @ NuTypeDef(Mod, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, signatures, stmts, nested, _) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = ModuleSymbol(nme, tps map { _._2.name }, body, members, signatures, stmts, pars, nested, qualifier).tap(scope.register)
        if (!td.isDecl) modules += sym
      }
      case td @ NuTypeDef(Als, TypeName(nme), tps, _, ctor, sig, pars, _, _, _) => {
        scope.declareTypeAlias(nme, tps map { _._2.name }, sig.getOrElse(Top))
      }
      case td @ NuTypeDef(Cls, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (params, preStmts) = ctor match {
          case S(Constructor(Tup(ls), Blk(stmts))) => (S(ls.map {
            case (S(Var(nme)), Fld(flags, _)) => (nme, flags.genGetter)
            case (N, Fld(flags, Var(nme))) => (nme, flags.genGetter)
            case _ => throw CodeGenError(s"Unexpected constructor parameters in $nme.")
          }), stmts)
          case _ => (N, Nil)
        }
        val (body, members, signatures, stmts, nested, publicCtors) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym =
          NewClassSymbol(nme, tps map { _._2.name }, params, body, members, td.genUnapply match {
            case S(NuFunDef(isLetRec, mnme, _, tys, Left(rhs))) =>
              S(MethodDef[Left[Term, Type]](isLetRec.getOrElse(false), TypeName(nme), mnme, tys, Left(rhs)))
            case _ => N
          }, signatures, preStmts ++ stmts, pars, publicCtors, nested, qualifier, td.isPlainJSClass).tap(scope.register)
        if (!td.isDecl) classes += sym
      }
      case td @ NuTypeDef(Trt, TypeName(nme), tps, tup, ctor, sig, pars, sup, ths, unit) => {
        val (body, members, _, _, _, _) = prepare(nme, tup.getOrElse(Tup(Nil)).fields, pars, unit)
        val sym = scope.declareTrait(nme, tps map { _._2.name }, body, members)
        if (!td.isDecl) traits += sym
      }
    }
    (traits.toList, classes.toList, mixins.toList, modules.toList)
  }

  /**
    * Recursively collect fields from trait definitions.
    * Caveat: this might cause stack overflow if cyclic inheritance exists.
    */
  private def resolveTraitFields(name: Str): Ls[Str] =
    topLevelScope.getType(name) match {
      case S(sym: TraitSymbol) => sym.body.collectFields ++ resolveTraitFields(sym)
      case S(_: TypeSymbol) | S(_: ClassSymbol) | N => Nil
    }

  /**
    * Recursively collect fields from trait definitions.
    * Caveat: this might cause stack overflow if cyclic inheritance exists.
    */
  private def resolveTraitFields(sym: TraitSymbol): Ls[Str] =
    sym.body.collectTypeNames.flatMap(resolveTraitFields)

  /**
    * Find the base class for a specific class.
    */
  private def resolveBaseClass(ty: Type): Opt[ClassSymbol] = {
    val baseClasses = ty.collectTypeNames.flatMap { name =>
      topLevelScope.getType(name) match {
        case S(sym: ClassSymbol) => S(sym)
        case S(sym: TraitSymbol) => N // TODO: inherit from traits
        case S(sym: TypeAliasSymbol) =>
          throw new CodeGenError(s"cannot inherit from type alias $name" )
        case S(_: NuTypeSymbol) =>
          throw new CodeGenError(s"NuType symbol $name is not supported when resolving base classes")
        case N =>
          throw new CodeGenError(s"undeclared type name $name when resolving base classes")
      }
    }
    if (baseClasses.lengthIs > 1)
      throw CodeGenError(
        s"cannot have ${baseClasses.length} base classes: " +
        baseClasses.map { _.lexicalName }.mkString(", ")
      )
    else
      baseClasses.headOption
  }

  /**
    * Resolve inheritance of all declared classes.
    * 
    * @return sorted class symbols with their base classes
    */
  protected def sortClassSymbols(classSymbols: Ls[ClassSymbol]): Iterable[(ClassSymbol, Opt[ClassSymbol])] = {
    // Cache base classes for class symbols.
    val baseClasses = Map.from(classSymbols.iterator.flatMap { derivedClass =>
      topLevelScope.resolveBaseClass(derivedClass.body).map(derivedClass -> _)
    })
    val sorted = try topologicalSort(baseClasses, classSymbols) catch {
      case e: CyclicGraphError => throw CodeGenError("cyclic inheritance detected")
    }
    // Their base classes might be class symbols defined in previous translation
    // units. So we filter them out here.
    sorted.flatMap(sym => if (classSymbols.contains(sym)) S(sym -> baseClasses.get(sym)) else N)
  }
  
}

class JSWebBackend extends JSBackend {
  override def oldDefs: Bool = false
  
  // Name of the array that contains execution results
  val resultsName: Str = topLevelScope declareRuntimeSymbol "results"

  val prettyPrinterName: Str = topLevelScope declareRuntimeSymbol "prettyPrint"

  polyfill.use("prettyPrint", prettyPrinterName)

  private def generate(pgrm: Pgrm): (Ls[Str], Ls[Str]) = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val (traitSymbols, classSymbols) = declareTypeDefs(typeDefs)
    val defStmts = 
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      sortClassSymbols(classSymbols).map { case (derived, base) =>
        translateClassDeclaration(derived, base)(topLevelScope)
      }.toList

    val resultsIdent = JSIdent(resultsName)
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        defStmts
        // Generate something like:
        // ```js
        // const <name> = <expr>;
        // <results>.push(<name>);
        // ```
        .concat(otherStmts.flatMap {
          case Def(recursive, Var(name), L(body), isByname) =>
            val (originalExpr, sym) = if (recursive) {
              val isByvalueRecIn = if (isByname) None else Some(true)
              val sym = topLevelScope.declareValue(name, isByvalueRecIn, body.isLam, N)
              val translated = translateTerm(body)(topLevelScope)
              topLevelScope.unregisterSymbol(sym)
              val isByvalueRecOut = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRecOut, body.isLam, N))
            } else {
              val translatedBody = translateTerm(body)(topLevelScope)
              val isByvalueRec = if (isByname) None else Some(false)
              (translatedBody, topLevelScope.declareValue(name, isByvalueRec, body.isLam, N))
            }
            val translatedBody = if (sym.isByvalueRec.isEmpty && !sym.isLam) JSArrowFn(Nil, L(originalExpr)) else originalExpr
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          // Ignore type declarations.
          case Def(_, _, R(_), isByname) => Nil
          // `exprs.push(<expr>)`.
          case term: Term =>
            topLevelScope.tempVars `with` JSInvoke(
              resultsIdent("push"),
              translateTerm(term)(topLevelScope) :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    (JSImmEvalFn(N, Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines, Nil)
  }

  private def generateNewDef(pgrm: Pgrm): (Ls[Str], Ls[Str]) = {
    
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
   }

    // don't pass `otherStmts` to the top-level module, because we need to execute them one by one later
    val topModule = topLevelScope.declareTopModule("TypingUnit", Nil, typeDefs, true)
    val moduleIns = topLevelScope.declareValue("typing_unit", Some(false), false, N)
    val moduleDecl = translateTopModuleDeclaration(topModule, true)(topLevelScope)
    val insDecl =
      JSConstDecl(moduleIns.runtimeName, JSNew(JSIdent(topModule.name)))

    val includes = typeDefs.filter(!_.isDecl).map(addNuTypeToGlobalThis(_, moduleIns.runtimeName))

    val resultsIdent = JSIdent(resultsName)
    val resultNames = ListBuffer[Str]()
    val stmts: Ls[JSStmt] =
      JSConstDecl(resultsName, JSArray(Nil)) ::
        (moduleDecl :: insDecl :: includes)
        // Generate something like:
        // ```js
        // const <name> = <expr>;
        // <results>.push(<name>);
        // ```
        .concat(otherStmts.flatMap {
          case NuFunDef(isLetRec, nme @ Var(name), symNme, tys, rhs @ L(body)) =>
            val recursive = isLetRec.getOrElse(true)
            val isByname = isLetRec.isEmpty
            val symb = symNme.map(_.name)
            val (originalExpr, sym) = (if (recursive) {
              val isByvalueRecIn = if (isByname) None else Some(true)
              
              // TODO Improve: (Lionel) what?!
              val sym = topLevelScope.declareValue(name, isByvalueRecIn, body.isLam, N)
              val translated = translateTerm(body)(topLevelScope)
              topLevelScope.unregisterSymbol(sym)
              
              val isByvalueRecOut = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRecOut, body.isLam, symb))
            } else {
              val translated = translateTerm(body)(topLevelScope)
              val isByvalueRec = if (isByname) None else Some(false)
              (translated, topLevelScope.declareValue(name, isByvalueRec, body.isLam, symb))
            })
            val translatedBody = if (sym.isByvalueRec.isEmpty && !sym.isLam) JSArrowFn(Nil, L(originalExpr)) else originalExpr
            resultNames += sym.runtimeName
            topLevelScope.tempVars `with` JSConstDecl(sym.runtimeName, translatedBody) ::
              JSInvoke(resultsIdent("push"), JSIdent(sym.runtimeName) :: Nil).stmt :: Nil
          case fd @ NuFunDef(isLetRec, Var(name), _, tys, R(ty)) =>
            Nil
          case _: Def | _: TypeDef | _: Constructor =>
            throw CodeGenError("Def and TypeDef are not supported in NewDef files.")
          case term: Term =>
            val res = translateTerm(term)(topLevelScope)
            resultNames += term.show(true)
            topLevelScope.tempVars `with` JSInvoke(
              resultsIdent("push"),
              res :: Nil
            ).stmt :: Nil
        })
    val epilogue = resultsIdent.member("map")(JSIdent(prettyPrinterName)).`return` :: Nil
    (JSImmEvalFn(N, Nil, R(polyfill.emit() ::: stmts ::: epilogue), Nil).toSourceCode.toLines, resultNames.toList)
  }

  def apply(pgrm: Pgrm): (Ls[Str], Ls[Str]) =
    if (!oldDefs) generateNewDef(pgrm) else generate(pgrm)
}

abstract class JSTestBackend extends JSBackend {
  
  private val lastResultSymbol = topLevelScope.declareValue("res", Some(false), false, N)
  private val resultIdent = JSIdent(lastResultSymbol.runtimeName)

  private var numRun = 0

  /**
    * Generate a piece of code for test purpose. It can be invoked repeatedly.
    * `prettyPrintQQ` is a temporary hack due to lack of runtime support and should be removed later.
    */
  def apply(pgrm: Pgrm, allowEscape: Bool, isNewDef: Bool, prettyPrintQQ: Bool): JSTestBackend.Result =
    if (!isNewDef)
      try generate(pgrm)(topLevelScope, allowEscape) catch {
        case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
        case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
        // case NonFatal(e) => JSTestBackend.UnexpectedCrash(e.getClass().getName, e.getMessage())
      }
    else
      try generateNewDef(pgrm, prettyPrintQQ)(topLevelScope, allowEscape) catch {
        case e: CodeGenError => JSTestBackend.IllFormedCode(e.getMessage())
        case e: UnimplementedError => JSTestBackend.Unimplemented(e.getMessage())
        // case NonFatal(e) => JSTestBackend.UnexpectedCrash(e.getClass().getName, e.getMessage())
      }
    // generate(pgrm)(topLevelScope, allowEscape)

  /**
    * Generate JavaScript code which targets MLscript test from the given block.
    *
    * @param pgrm the program to translate
    * @param scope the top-level scope
    * @param allowEscape whether to try executing code even if it refers to unimplemented definitions
    * @return
    */
  private def generate(pgrm: Pgrm)(implicit scope: Scope, allowEscape: Bool): JSTestBackend.TestCode = {
    val (diags, (typeDefs, otherStmts)) = pgrm.desugared

    val (traitSymbols, classSymbols) = declareTypeDefs(typeDefs)
    val defStmts = 
      traitSymbols.map { translateTraitDeclaration(_)(topLevelScope) } ++
      sortClassSymbols(classSymbols).map { case (derived, base) =>
        translateClassDeclaration(derived, base)(topLevelScope)
      }.toList

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    // Generate statements.
    val queries = otherStmts.map {
      case Def(recursive, Var(name), L(body), isByname) =>
        (if (recursive) {
          val isByvalueRecIn = if (isByname) None else Some(true)
          val sym = scope.declareValue(name, isByvalueRecIn, body.isLam, N)
          try {
            val translated = translateTerm(body)
            scope.unregisterSymbol(sym)
            val isByvalueRecOut = if (isByname) None else Some(false)
            R((translated, scope.declareValue(name, isByvalueRecOut, body.isLam, N)))
          } catch {
            case e: UnimplementedError =>
              scope.stubize(sym, e.symbol)
              L(e.getMessage())
            case NonFatal(e) =>
              scope.unregisterSymbol(sym)
              val isByvalueRecOut = if (isByname) None else Some(false)
              scope.declareValue(name, isByvalueRecOut, body.isLam, N)
              throw e
          }
        } else {
          (try R(translateTerm(body)) catch {
            case e: UnimplementedError =>
              scope.declareStubValue(name, e.symbol, N)
              L(e.getMessage())
          }) map {
            val isByvalueRec = if (isByname) None else Some(false)
            expr => (expr, scope.declareValue(name, isByvalueRec, body.isLam, N))
          }
        }) match {
          case R((originalExpr, sym)) =>
            val expr = 
              if (sym.isByvalueRec.isEmpty && !sym.isLam)
                JSArrowFn(Nil, L(originalExpr))
              else
                originalExpr
            JSTestBackend.CodeQuery(
              scope.tempVars.emit(),
              ((JSIdent("globalThis").member(sym.runtimeName) := (expr match {
                case t: JSArrowFn => t.toFuncExpr(S(sym.runtimeName))
                case t            => t
              })) :: Nil),
              sym.runtimeName
            )
          case L(reason) => JSTestBackend.AbortedQuery(reason)
        }
      case Def(_, Var(name), _, _) =>
        scope.declareStubValue(name, N)
        JSTestBackend.EmptyQuery
      case term: Term =>
        try {
          val body = translateTerm(term)(scope)
          val res = JSTestBackend.CodeQuery(scope.tempVars.emit(), (resultIdent := body) :: Nil)
          scope.refreshRes()
          res
        } catch {
          case e: UnimplementedError => JSTestBackend.AbortedQuery(e.getMessage())
        }
    }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = defStmts
    if (numRun === 0)
      prelude = JSLetDecl(lastResultSymbol.runtimeName -> N :: Nil) :: prelude

    // Increase the run number.
    numRun = numRun + 1

    JSTestBackend.TestCode(SourceCode.fromStmts(polyfill.emit() ::: prelude).toLines, queries)
  }

  private def generateNewDef(pgrm: Pgrm, prettyPrintQQ: Bool)(implicit scope: Scope, allowEscape: Bool): JSTestBackend.TestCode = {
  
    val (typeDefs, otherStmts) = pgrm.tops.partitionMap {
      case _: Constructor => throw CodeGenError("unexpected constructor.")
      case ot: Terms => R(ot)
      case fd: NuFunDef => R(fd)
      case nd: NuTypeDef => L(nd)
      case _ => die
    }

    otherStmts.foreach {
      case fd @ NuFunDef(isLetRec, Var(nme), symNme, _, L(body)) =>
        val isByname = isLetRec.isEmpty
        val isByvalueRecIn = if (isByname) None else Some(true)
        val symb = symNme.map(_.name)
        scope.declareValue(nme, isByvalueRecIn, body.isLam, symb, true)
      case _ => ()
    }
    
    // don't pass `otherStmts` to the top-level module, because we need to execute them one by one later
    val topModule = topLevelScope.declareTopModule("TypingUnit", Nil, typeDefs, true)
    val moduleIns = topLevelScope.declareValue("typing_unit", Some(false), false, N)
    val moduleDecl = translateTopModuleDeclaration(topModule, true)
    val insDecl =
      JSConstDecl(moduleIns.runtimeName, JSNew(JSIdent(topModule.runtimeName)))

    val includes = typeDefs.filter(!_.isDecl).map(addNuTypeToGlobalThis(_, moduleIns.runtimeName))

    val zeroWidthSpace = JSLit("\"\\u200B\"")
    val catchClause = JSCatchClause(
      JSIdent("e"),
      (zeroWidthSpace + JSIdent("e") + zeroWidthSpace).log() :: Nil
    )

    // TODO Improve: (Lionel) I find this logic very strange! What's going on here?
    //  Why are we declaring some things above AND below?
    //  Why does the fact that a binding is recursive affect its declaration in the OUTER scope?
    
    // Generate statements.
    val queries = otherStmts.map {
      case NuFunDef(isLetRec, nme @ Var(name), symNme, tys, rhs @ L(body)) =>
        val recursive = isLetRec.getOrElse(true)
        val isByname = isLetRec.isEmpty
        val symb = symNme.map(_.name)
        (if (recursive) {
          val isByvalueRecIn = if (isByname) None else Some(true)
          val sym = scope.resolveValue(name) match {
            case Some(s: ValueSymbol) => s
            case _ => scope.declareValue(name, isByvalueRecIn, body.isLam, symb)
          }
          val isByvalueRecOut = if (isByname) None else Some(false)
          try {
            val translated = translateTerm(body) // TODO Improve: (Lionel) Why are the bodies translated in the SAME scope?!
            scope.unregisterSymbol(sym) // TODO Improve: (Lionel) ???
            R((translated, scope.declareValue(name, isByvalueRecOut, body.isLam, symb)))
          } catch {
            case e: UnimplementedError =>
              scope.stubize(sym, e.symbol)
              L(e.getMessage())
            case NonFatal(e) =>
              scope.unregisterSymbol(sym) // TODO Improve: (Lionel) You should only try/catch around the part that may actually fail, and if `unregisterSymbol` should always be called, that should be done in `finally`... but the very logic of calling `unregisterSymbol` is very fishy, to say the least
              scope.declareValue(name, isByvalueRecOut, body.isLam, symb)
              throw e
          }
        } else {
          (try R(translateTerm(body)) catch { // TODO Improve: Why are the bodies translated in the SAME scope?!
            case e: UnimplementedError =>
              scope.declareStubValue(name, e.symbol, symb)
              L(e.getMessage())
          }) map {
            val isByvalueRec = if (isByname) None else Some(false)
            expr => (expr, scope.declareValue(name, isByvalueRec, body.isLam, symb))
          }
        }) match {
          case R((originalExpr, sym)) =>
            val expr = 
              if (sym.isByvalueRec.isEmpty && !sym.isLam)
                JSArrowFn(Nil, L(originalExpr))
              else
                originalExpr
            JSTestBackend.CodeQuery(
              scope.tempVars.emit(),
              ((JSIdent("globalThis").member(sym.runtimeName) := (expr match {
                case t: JSArrowFn => t.toFuncExpr(S(sym.runtimeName))
                case t            => t
              })) :: Nil),
              sym.runtimeName
            )
          case L(reason) => JSTestBackend.AbortedQuery(reason)
        }
      case fd @ NuFunDef(isLetRec, Var(name), symNme, tys, R(ty)) =>
        val symb = symNme.map(_.name)
        scope.declareStubValue(name, symb)(allowEscape || fd.isDecl)
        JSTestBackend.EmptyQuery
      case term: Term =>
        try {
          val body = translateTerm(term)(scope)
          val res = JSTestBackend.CodeQuery(scope.tempVars.emit(), (resultIdent := body) :: Nil)
          scope.refreshRes()
          res
        } catch {
          case e: UnimplementedError => JSTestBackend.AbortedQuery(e.getMessage())
        }
      case _: Def | _: TypeDef | _: Constructor =>
        throw CodeGenError("Def and TypeDef are not supported in NewDef files.")
    }

    // If this is the first time, insert the declaration of `res`.
    var prelude: Ls[JSStmt] = Ls(moduleDecl, insDecl) ::: includes
    val isFirst = numRun === 0
    if (isFirst)
      prelude = JSLetDecl(lastResultSymbol.runtimeName -> N :: Nil) :: prelude

    // Increase the run number.
    numRun = numRun + 1

    val qqPredefs =
      SourceCode(if (isFirst && prettyPrintQQ) QQHelper.prettyPrinter else "")
    JSTestBackend.TestCode((qqPredefs ++ SourceCode.fromStmts(polyfill.emit() ::: prelude)).toLines, queries)
  }
}

object JSTestBackend {
  sealed abstract class Query

  /**
    * The generation was aborted due to some reason.
    */
  final case class AbortedQuery(reason: Str) extends Query

  /**
    * The entry generates nothing.
    */
  final object EmptyQuery extends Query

  /**
    * The entry generates meaningful code.
    */
  final case class CodeQuery(prelude: Ls[Str], code: Ls[Str], res: Str) extends Query {
    
  }

  object CodeQuery {
    def apply(decls: Opt[JSLetDecl], stmts: Ls[JSStmt], res: Str = "res"): CodeQuery =
      CodeQuery(
        decls match {
          case S(stmt) => stmt.toSourceCode.toLines
          case N       => Nil
        },
        SourceCode.fromStmts(stmts).toLines,
        res
      )
  }

  /**
    * Represents the result of code generation.
    */
  abstract class Result {
    def showFirstResult(prefixLength: Int): Unit = ()
  }

  /**
    * Emitted code.
    */
  final case class TestCode(prelude: Ls[Str], queries: Ls[Query]) extends Result

  sealed abstract class ErrorMessage(val content: Str) extends Result

  /**
    * The input MLscript is ill-formed (e.g. impossible inheritance).
    */
  final case class IllFormedCode(override val content: Str) extends ErrorMessage(content)

  /**
    * Some referenced symbols are not implemented.
    */
  final case class Unimplemented(override val content: Str) extends ErrorMessage(content)

  /**
    * Code generation crashed.
    */
  // final case class UnexpectedCrash(val name: Str, override val content: Str) extends ErrorMessage(content)

  /**
    * The result is not executed for some reasons. E.g. `:NoJS` flag.
    */
  final object ResultNotExecuted extends JSTestBackend.Result
}

object JSBackend {
  // For integers larger than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER
  val MaximalSafeInteger: BigInt = BigInt("9007199254740991")

  // For integers less than this value, use BigInt notation.
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MIN_SAFE_INTEGER
  val MinimalSafeInteger: BigInt = BigInt("-9007199254740991")

  def isSafeInteger(value: BigInt): Boolean =
    MinimalSafeInteger <= value && value <= MaximalSafeInteger
}
