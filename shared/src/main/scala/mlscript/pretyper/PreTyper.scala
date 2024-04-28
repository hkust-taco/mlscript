package mlscript
package pretyper

import annotation.tailrec, collection.mutable.{Set => MutSet}, collection.immutable.SortedMap, util.chaining._
import utils._, shorthands._, Diagnostic.PreTyping, Message.MessageContext, symbol._, ucs.Desugarer

class PreTyper extends Traceable with Diagnosable with Desugarer {
  /** A shorthand function to raise errors without specifying the source. */
  protected def raiseError(messages: (Message -> Opt[Loc])*): Unit =
    raiseError(PreTyping, messages: _*)

  /** A shorthand function to raise warnings without specifying the source. */
  protected def raiseWarning(messages: (Message -> Opt[Loc])*): Unit =
    raiseWarning(PreTyping, messages: _*)

  private def extractParameters(fields: Term): Ls[LocalTermSymbol] = {
    def rec(term: Term): Iterator[LocalTermSymbol] = term match {
      case nme: Var => Iterator.single(new LocalTermSymbol(nme))
      case Bra(false, term) => rec(term)
      case Bra(true, Rcd(fields)) =>
        fields.iterator.flatMap { case (_, Fld(_, pat)) => rec(pat) }
      case Asc(term, _) => rec(term)
      case literal: Lit =>
        raiseWarning(msg"literal patterns are ignored" -> literal.toLoc)
        Iterator.empty
      case App(Var(name), parameters) if name.isCapitalized => rec(parameters)
      case Tup(arguments) =>
        arguments.iterator.flatMap {
          case (S(nme: Var), Fld(_, _)) => Iterator.single(new LocalTermSymbol(nme))
          case (N, Fld(_, term)) => rec(term)
        }
      case PlainTup(arguments @ _*) => arguments.iterator.flatMap(extractParameters)
      case other =>
        raiseError(msg"unsupported pattern shape" -> other.toLoc)
        Iterator.empty
    }
    rec(fields).tap { rs =>
      println(s"extractParameters ${fields.showDbg} ==> ${rs.map(_.name).mkString(", ")}")
    }.toList
  }

  protected def resolveVar(v: Var)(implicit scope: Scope): Unit =
    scope.getTermSymbol(v.name) match {
      case S(sym: LocalTermSymbol) =>
        println(s"resolveVar `${v.name}` ==> local term")
        v.symbol = sym
      case S(sym: DefinedTermSymbol) =>
        println(s"resolveVar `${v.name}` ==> defined term")
        v.symbol = sym
      case S(sym: ModuleSymbol) =>
        println(s"resolveVar `${v.name}` ==> module")
        v.symbol = sym
      case N => 
        scope.getTypeSymbol(v.name) match {
          case S(sym: ClassSymbol) =>
            println(s"resolveVar `${v.name}` ==> class")
            v.symbol = sym
          case S(_) =>
            raiseError(msg"identifier `${v.name}` is resolved to a type" -> v.toLoc)
          case N =>
            raiseError(msg"identifier `${v.name}` not found" -> v.toLoc)
        }
    }

  protected def traverseVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"traverseVar(name = \"${v.name}\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.getSymbols(v.name) match {
          case Nil => raiseError(msg"identifier `${v.name}` not found" -> v.toLoc)
          case symbols if symbols.contains(symbol) => ()
          case symbols =>
            def toNameLoc(symbol: Symbol): (Str, Opt[Loc]) = symbol match {
              case ds: DummyClassSymbol => s"`${ds.name}`" -> N
              case ts: TypeSymbol => s"`${ts.name}`" -> ts.defn.toLoc
              case ls: LocalTermSymbol => s"local `${ls.name}`" -> ls.nme.toLoc
              case dt: DefinedTermSymbol => s"`${dt.name}`" -> dt.defn.toLoc
            }
            val (name, loc) = toNameLoc(symbol)
            raiseError(
              (msg"identifier ${v.name} refers to different symbols." -> v.toLoc ::
                msg"it is resolved to $name" -> loc ::
                symbols.map { s =>
                  val (name, loc) = toNameLoc(s)
                  msg"it was previously resolved to $name" -> loc
                }): _*
            )
        }
      }
    }()

  protected def traverseTerm(term: Term)(implicit scope: Scope): Unit =
    trace(s"traverseTerm <== ${term.showDbg}") {
      term match {
        case Assign(lhs, rhs) => traverseTerm(lhs); traverseTerm(rhs)
        case Bra(_, trm) => traverseTerm(trm)
        case Lam(lhs, rhs) =>
          traverseTerm(rhs)(scope ++ extractParameters(lhs))
        case Sel(receiver, fieldName) => traverseTerm(receiver)
        case Let(isRec, nme, rhs, body) =>
          traverseTerm(rhs)
          traverseTerm(body)(scope + new LocalTermSymbol(nme))
        case New(head, body) =>
          // `new C(...)` or `new C(){...}` or `new{...}`
        case Tup(fields) => fields.foreach {
          case (S(t), Fld(_, _)) => traverseTerm(t)
          case (N, Fld(_, t)) => traverseTerm(t)
        }
        case Asc(trm, ty) => traverseTerm(trm)
        case ef @ If(_, _) => traverseIf(ef)(scope)
        case TyApp(lhs, targs) =>
          // Be consistent with the error message from `Typer`.
          raiseError(msg"type application syntax is not yet supported" -> term.toLoc)
        case Eqn(lhs, rhs) =>
          raiseWarning(msg"unsupported `Eqn`: ${term.showDbg}" -> term.toLoc)
        case Blk(stmts) =>
          traverseStatements(stmts, "block", scope)
          ()
        case Subs(arr, idx) => traverseTerm(arr); traverseTerm(idx)
        case Bind(lhs, rhs) => traverseTerm(lhs); traverseTerm(rhs)
        case Splc(fields) => fields.foreach {
          case L(t) => traverseTerm(t)
          case R(Fld(_, t)) => traverseTerm(t)
        }
        case Forall(params, body) => traverseTerm(body)
        case Rcd(fields) => fields.foreach { case (_, Fld(_, t)) => traverseTerm(t) }
        case CaseOf(trm, cases) => 
        case With(trm, fields) => traverseTerm(trm); traverseTerm(fields)
        case Where(body, where) =>
          raiseWarning(msg"unsupported `Where`: ${term.showDbg}" -> term.toLoc)
        // begin UCS shorthands ================================================
        //  * Old-style operators
        case App(App(Var("is"), _), _) =>
          println(s"found UCS shorthand: ${term.showDbg}")
          val desugared = If(IfThen(term, Var("true")), S(Var("false")))
          traverseIf(desugared)
          term.desugaredTerm = desugared.desugaredTerm
        case App(Var("is"), _) =>
          println(s"found UCS shorthand: ${term.showDbg}")
          val desugared = If(IfThen(term, Var("true")), S(Var("false")))
          traverseIf(desugared)
          term.desugaredTerm = desugared.desugaredTerm
        //  * Old-style operators
        case App(App(Var("and"), PlainTup(lhs)), PlainTup(rhs)) =>
          println(s"found UCS shorthand: ${term.showDbg}")
          val desugared = If(IfThen(lhs, rhs), S(Var("false")))
          traverseIf(desugared)
          term.desugaredTerm = desugared.desugaredTerm
        case App(Var("and"), PlainTup(lhs, rhs)) =>
          println(s"found UCS shorthand: ${term.showDbg}")
          val desugared = If(IfThen(lhs, rhs), S(Var("false")))
          traverseIf(desugared)
          term.desugaredTerm = desugared.desugaredTerm
        // end UCS shorthands ==================================================
        case App(lhs, Tup(fields)) =>
          traverseTerm(lhs)
          fields.foreach { _._2.value |> traverseTerm }
        case App(lhs, rhs) => traverseTerm(lhs); traverseTerm(rhs)
        case Test(trm, ty) => traverseTerm(trm)
        case _: Lit | _: Super => ()
        case v: Var => traverseVar(v)
        case AdtMatchWith(cond, arms) =>
          raiseWarning(msg"unsupported `AdtMatchWith`: ${term.showDbg}" -> term.toLoc)
        case Inst(body) => traverseTerm(body)
        case NuNew(cls) => traverseTerm(cls)
        case Rft(base, decls) => // For object refinement
          traverseTerm(base)
          traverseStatements(decls.entities, "Rft", scope)
          ()
        case While(cond, body) =>
          traverseTerm(cond)
          traverseTerm(body)
        case Ann(ann, receiver) => traverseTerm(receiver)
        case Quoted(body) => traverseTerm(body)
        case Unquoted(body) => traverseTerm(body)
      }
    }(_ => s"traverseTerm ==> ${term.showDbg}")

  private def traverseTypeDefinition(symbol: TypeSymbol, defn: NuTypeDef)(implicit scope: Scope): Unit =
    trace(s"traverseTypeDefinition <== ${defn.describe}") {
      traverseStatements(defn.body.entities, defn.nme.name, scope)
      ()
    }(_ => s"traverseTypeDefinition <== ${defn.describe}")

  private def traverseStatements(statements: Ls[Statement], name: Str, parentScope: Scope): Scope =
    trace(s"traverseStatements <== $name: ${"statement".pluralize(statements.size, true)}") {
      // Pass 1: Build a scope with type symbols only.
      val typeSymbols = statements.collect { case t: NuTypeDef => TypeSymbol(t) }
      val scopeWithTypes = parentScope.derive ++ typeSymbols
      println(typeSymbols.iterator.map(_.name).mkString("type symbols: {", ", ", "}"))
      // Pass 1.1: Resolve parent type symbols.
      typeSymbols.foreach {
        case s: ClassLikeSymbol => s.parentTypeNames.foreach { nme =>
          scopeWithTypes.getTypeSymbol(nme.name) match {
            case S(symbol) => nme.symbol = symbol
            case N => raiseError(msg"could not find definition `${nme.name}`" -> nme.toLoc)
          }
        }
        case _ => ()
      }
      // Pass 2: Build a complete scope and collect definitional terms and terms to be traversed.
      val (completeScope, thingsToTraverse) = statements.foldLeft[(Scope, Ls[(Term \/ DefinedTermSymbol, Scope)])](scopeWithTypes, Nil) {
        case ((scope, acc), term: Term) => (scope, (L(term), scope) :: acc)
        case ((scope, acc), defn: NuFunDef) =>
          val termSymbol = new DefinedTermSymbol(defn)
          val scopeWithSymbol = scope + termSymbol
          (scopeWithSymbol, (R(termSymbol), if (termSymbol.isRecursive) scopeWithSymbol else scope) :: acc)
        case (acc, _: NuTypeDef) => acc // Ignore type definitions.
        case (acc, other @ (_: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef)) =>
          println(s"unknown statement: ${other.getClass.getSimpleName}")
          acc
      }
      // Pass 2.5: Traverse type definitions
      statements.iterator.flatMap { case defn: NuTypeDef => S(defn); case _ => N }.foreach { defn =>
        val parameters = defn.params.map(extractParameters).getOrElse(Nil)
        val thisSymbol = new LocalTermSymbol(Var("this"))
        traverseTypeDefinition(TypeSymbol(defn), defn)(completeScope ++ (thisSymbol :: parameters))
      }
      println(thingsToTraverse.iterator.map {
        case (L(term), _) => term.showDbg
        case (R(symbol), _) => symbol.name
      }.mkString("to be traversed: {", ", ", "}"))
      // Pass 3: Traverse terms collected from the last pass.
      println("Pass 3")
      thingsToTraverse.foreach {
        case (L(term), scope) =>
          println("traverseTerm: " + term.showDbg)
          println("scope: " + scope.showLocalSymbols)
          traverseTerm(term)(scope)
        case (R(symbol), scope) => symbol.body match {
          case L(term) =>
            if (symbol.isFunction) {
              traverseTerm(term)(completeScope)
            } else {
              traverseTerm(term)(scope)
            }
          case R(_) => ()
        }
      }
      completeScope
    }({ scope => s"traverseStatements ==> Scope {${scope.showLocalSymbols}}" })

  def apply(typingUnit: TypingUnit, scope: Scope, name: Str): Scope =
    trace(s"PreTyper <== $name: ${typingUnit.describe}") {
      traverseStatements(typingUnit.entities, name, scope)
    }({ scope => s"PreTyper ==> ${scope.showLocalSymbols}" })
}
