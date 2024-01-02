package mlscript.pretyper

import collection.mutable.{Set => MutSet}
import symbol._
import mlscript._, utils._, shorthands._, Diagnostic.PreTyping, Message.MessageContext, ucs.DesugarUCS
import scala.annotation.tailrec

class PreTyper(override val debugTopics: Opt[Set[Str]]) extends Traceable with Diagnosable with DesugarUCS {
  import PreTyper._

  private def extractParameters(fields: Term): Ls[LocalTermSymbol] =
    trace(s"extractParameters <== ${inspect.deep(fields)}") {
      fields match {
        case Tup(arguments) =>
          arguments.flatMap {
            case (S(nme: Var), Fld(_, _)) => new LocalTermSymbol(nme) :: Nil
            case (_, Fld(_, nme: Var)) => new LocalTermSymbol(nme) :: Nil
            case (_, Fld(_, Bra(false, nme: Var))) => new LocalTermSymbol(nme) :: Nil
            case (_, Fld(_, tuple @ Tup(_))) => extractParameters(tuple)
            case (_, Fld(_, Asc(term, _))) => extractParameters(term)
            case (_, Fld(_, parameter)) =>
              println(s"unknown parameter: ${inspect.deep(parameter)}")
              ???
          }
        case PlainTup(arguments @ _*) =>
          arguments.map {
            case nme: Var => new LocalTermSymbol(nme)
            case other => println("Unknown parameters: " + inspect.deep(other)); ??? // TODO: bad
          }.toList
        case other => println("Unknown parameters: " + inspect.deep(other)); ??? // TODO: bad
      }
    }(rs => s"extractParameters ==> ${rs.iterator.map(_.name).mkString(", ")}")

  // `traverseIf` is meaningless because it represents patterns with terms.

  protected def resolveVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"resolveVar(name = \"$v\")") {
      scope.getTermSymbol(v.name) match {
        case S(sym: LocalTermSymbol) =>
          println(s"Resolve variable $v to a local term.")
          v.symbol = sym
        case S(sym: DefinedTermSymbol) =>
          println(s"Resolve variable $v to a defined term.")
          v.symbol = sym
        case S(sym: ModuleSymbol) =>
          println(s"Resolve variable $v to a module.")
          v.symbol = sym
        case N => 
          scope.getTypeSymbol(v.name) match {
            case S(sym: ClassSymbol) =>
              println(s"Resolve variable $v to a class.")
              v.symbol = sym
            case S(_) =>
              raiseError(PreTyping, msg"Name ${v.name} refers to a type" -> v.toLoc)
            case N =>
              raiseError(PreTyping, msg"Variable ${v.name} not found in scope" -> v.toLoc)
          }
      }
    }()

  protected def traverseVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"traverseVar(name = \"$v\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.getSymbols(v.name) match {
          case Nil => raiseError(PreTyping, msg"Variable ${v.name} not found in scope. It is possibly a free variable." -> v.toLoc)
          case symbols if symbols.contains(symbol) => ()
          case _ =>
            raiseError(PreTyping, msg"Variable ${v.name} refers to different symbols." -> v.toLoc)
        }
      }
    }()

  protected def traverseTerm(term: Term)(implicit scope: Scope): Unit =
    trace(s"traverseTerm <== ${inspect.shallow(term)}") {
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
        case Tup(fields) => fields.foreach { case (_, Fld(_, t)) => traverseTerm(t) }
        case Asc(trm, ty) => traverseTerm(trm)
        case ef @ If(_, _) => traverseIf(ef)(scope)
        case TyApp(lhs, targs) => // TODO: When?
        case Eqn(lhs, rhs) => ??? // TODO: How?
        case Blk(stmts) =>
          traverseStatements(stmts, "block", scope)
          ()
        case Subs(arr, idx) => traverseTerm(arr); traverseTerm(idx)
        case Bind(lhs, rhs) => traverseTerm(lhs); traverseTerm(rhs)
        case Splc(fields) => fields.foreach {
          case L(t) => traverseTerm(t)
          case R(Fld(_, t)) => traverseTerm(t)
        }
        case Forall(params, body) => ??? // TODO: When?
        case Rcd(fields) => fields.foreach { case (_, Fld(_, t)) => traverseTerm(t) }
        case CaseOf(trm, cases) => 
        case With(trm, fields) => traverseTerm(trm); traverseTerm(fields)
        case Where(body, where) => ??? // TODO: When?
        case App(lhs, rhs) => traverseTerm(lhs); traverseTerm(rhs)
        case Test(trm, ty) => traverseTerm(trm)
        case _: Lit | _: Super => ()
        case v: Var => traverseVar(v)
        case AdtMatchWith(cond, arms) => ??? // TODO: How?
        case Inst(body) => traverseTerm(body)
        case NuNew(cls) => traverseTerm(cls)
        case Rft(base, decls) => // For object refinement
          traverseTerm(base)
          traverseStatements(decls.entities, "Rft", scope)
          ()
      }
    }(_ => s"traverseTerm ==> ${inspect.shallow(term)}")

  private def traverseTypeDefinition(symbol: TypeSymbol, defn: NuTypeDef)(implicit scope: Scope): Unit =
    trace(s"traverseTypeDefinition <== ${defn.describe}") {
      traverseStatements(defn.body.entities, defn.nme.name, scope)
      ()
    }(_ => s"traverseTypeDefinition <== ${defn.describe}")

  private def traverseStatements(statements: Ls[Statement], name: Str, parentScope: Scope): (Scope, TypeContents) =
    trace(s"traverseStatements <== $name: ${"statement".pluralize(statements.size, true)}") {
      // Pass 1: Build a scope with type symbols only.
      val filterNuTypeDef = { (_: Statement) match { case t: NuTypeDef => S(t); case _ => N } }
      val typeSymbols = statements.iterator.flatMap(filterNuTypeDef).map(TypeSymbol(_)).toList
      val scopeWithTypes = parentScope.derive ++ typeSymbols
      println(typeSymbols.iterator.map(_.name).mkString("type symbols: {", ", ", "}"))
      // val scopeWithTypes = statements.iterator.flatMap(filterNuTypeDef).foldLeft(parentScope.derive)(_ + TypeSymbol(_))
      // Pass 1.1: Resolve subtyping relations. Build a graph and compute base types of each type.
      val edges = typeSymbols.foldLeft(Map.empty[TypeSymbol, Ls[TypeSymbol]]) { case (acc, self) =>
        acc + (self -> extractSuperTypes(self.defn.parents).map { nme =>
          scopeWithTypes.getTypeSymbol(nme.name).getOrElse(???) })
      }
      printGraph(edges, println, "inheritance relations", "->")
      transitiveClosure(edges).foreachEntry { (self, bases) =>
        self.baseTypes = bases
        println(s"base types of `${self.name}`: ${bases.iterator.map(_.name).mkString(", ")}")
      }
      // Pass 1.2: Resolve signature types for collecting sealed derived types.
      println("Resolve sealed signature types")
      typeSymbols.foreach {
        case _: MixinSymbol | _: TypeAliasSymbol | _: ModuleSymbol => ()
        case symbol => symbol.defn.sig.foreach { unions =>
          val derivedTypes = try extractSignatureTypes(unions) catch { case _: NotImplementedError => Nil }
          symbol.sealedDerivedTypes = derivedTypes.flatMap { derivedType =>
            val maybeSymbol = scopeWithTypes.getTypeSymbol(derivedType.name)
            if (maybeSymbol.isEmpty) raise(ErrorReport(
              msg"Undefined type $derivedType" -> derivedType.toLoc :: Nil,
              true,
              Diagnostic.PreTyping
            ))
            maybeSymbol
          }
          println(s">>> $name: ${symbol.sealedDerivedTypes.iterator.map(_.name).mkString(", ")}")
        }
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
      println(thingsToTraverse.iterator.map {
        case (L(term), _) => inspect.shallow(term)
        case (R(symbol), _) => symbol.name
      }.mkString("to be traversed: {", ", ", "}"))
      // Pass 3: Traverse terms collected from the last pass.
      println("Pass 3")
      thingsToTraverse.foreach {
        case (L(term), scope) =>
          println("traverseTerm: " + inspect.shallow(term))
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
      (completeScope, new TypeContents)
    }({ case (scope, contents) => s"traverseStatements ==> Scope {${scope.showLocalSymbols}}" })

  def process(typingUnit: TypingUnit, scope: Scope, name: Str): (Scope, TypeContents) =
    trace(s"process <== $name: ${typingUnit.describe}") {
      traverseStatements(typingUnit.entities, name, scope)
    }({ case (scope, contents) => s"process ==> ${scope.showLocalSymbols}" })
}

object PreTyper {

  def extractSuperTypes(parents: Ls[Term]): Ls[Var] = {
    @tailrec
    def rec(results: Ls[Var], waitlist: Ls[Term]): Ls[Var] =
      waitlist match {
        case Nil => results.reverse
        case (nme: Var) :: tail => rec(nme :: results, tail)
        case (TyApp(ty, _)) :: tail => rec(results, ty :: tail)
        case (App(nme @ Var(_), Tup(_))) :: tail => rec(nme :: results, tail)
        case other :: _ => println(s"Unknown parent type: ${inspect.deep(other)}"); ???
      }
    rec(Nil, parents)
  }

  /**
    * Extract types in class signatures. For example, for this piece of code
    * ```mls
    * abstract class Option[A]: Some[A] | None
    * ```
    * this function returns, `Some` and `None`.
    *
    * @param ty a type obtained from `NuTypeDef.sig`
    * @return a list of type names, without any p
    */
  def extractSignatureTypes(ty: Type): Ls[TypeName] = {
    @tailrec
    def rec(acc: Ls[TypeName], ty: Type): Ls[TypeName] = ty match {
      case tn: TypeName => tn :: acc
      case AppliedType(tn: TypeName, _) => tn :: acc
      case Union(lhs, tn: TypeName) => rec(tn :: acc, lhs)
      case Union(lhs, AppliedType(tn: TypeName, _)) => rec(tn :: acc, lhs)
      case other => println(s"Unknown type in signature: $other"); ???
    }
    rec(Nil, ty).reverse
  }

  def transitiveClosure[A](graph: Map[A, List[A]]): Map[A, List[A]] = {
    def dfs(vertex: A, visited: Set[A]): Set[A] = {
      if (visited.contains(vertex)) visited
      else graph.getOrElse(vertex, List())
        .foldLeft(visited + vertex)((acc, v) => dfs(v, acc))
    }
    graph.keys.map { vertex =>
      val closure = dfs(vertex, Set())
      vertex -> (closure - vertex).toList
    }.toMap
  }

  def printGraph(graph: Map[TypeSymbol, List[TypeSymbol]], print: (=> Any) => Unit, title: String, arrow: String): Unit = {
    print(s"• $title")
    if (graph.isEmpty)
      print("  + <Empty>")
    else
      graph.foreachEntry { (source, targets) =>
        print(s"  + ${source.name} $arrow " + {
          if (targets.isEmpty) s"{}"
          else targets.iterator.map(_.name).mkString("{ ", ", ", " }")
        })
      }
  }
}