package mlscript.pretyper

import collection.mutable.{Set => MutSet}
import collection.immutable.SortedMap
import symbol._
import mlscript._, utils._, shorthands._, Diagnostic.PreTyping, Message.MessageContext, ucs.DesugarUCS
import scala.annotation.tailrec

class PreTyper(override val debugTopics: Opt[Set[Str]]) extends Traceable with Diagnosable with DesugarUCS {
  import PreTyper._

  /** A shorthand function to raise errors without specifying the source. */
  protected override def raiseError(messages: (Message -> Opt[Loc])*): Unit =
    raiseError(PreTyping, messages: _*)

  /** A shorthand function to raise warnings without specifying the source. */
  protected override def raiseWarning(messages: (Message -> Opt[Loc])*): Unit =
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
    val rs = rec(fields).toList
    println(s"extractParameters ${fields.showDbg} ==> ${rs.iterator.map(_.name).mkString(", ")}")
    rs
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
            raiseError(PreTyping, msg"identifier `${v.name}` is resolved to a type" -> v.toLoc)
          case N =>
            raiseError(PreTyping, msg"identifier `${v.name}` not found" -> v.toLoc)
        }
    }

  protected def traverseVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"traverseVar(name = \"${v.name}\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.getSymbols(v.name) match {
          case Nil => raiseError(PreTyping, msg"identifier `${v.name}` not found" -> v.toLoc)
          case symbols if symbols.contains(symbol) => ()
          case symbols =>
            def toNameLoc(symbol: Symbol): (Str, Opt[Loc]) = symbol match {
              case ds: DummyClassSymbol => s"`${ds.name}`" -> N
              case ts: TypeSymbol => s"`${ts.name}`" -> ts.defn.toLoc
              case ls: LocalTermSymbol => s"local `${ls.name}`" -> ls.nme.toLoc
              case dt: DefinedTermSymbol => s"`${dt.name}`" -> dt.defn.toLoc
            }
            val (name, loc) = toNameLoc(symbol)
            raiseError(PreTyping,
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
        case Forall(params, body) => traverseTerm(body)
        case Rcd(fields) => fields.foreach { case (_, Fld(_, t)) => traverseTerm(t) }
        case CaseOf(trm, cases) => 
        case With(trm, fields) => traverseTerm(trm); traverseTerm(fields)
        case Where(body, where) => ??? // TODO: When?
        // begin UCS shorthands
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
        // end UCS shorthands
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
    }(_ => s"traverseTerm ==> ${term.showDbg}")

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
      // Keep a stable ordering of type symbols when printing the graph.
      implicit val ord: Ordering[TypeSymbol] = new Ordering[TypeSymbol] {
        override def compare(x: TypeSymbol, y: TypeSymbol): Int =
          x.name.compareTo(y.name)
      }
      // Collect inheritance relations, represented by a map from a type symbol
      // to its base types. If a type symbol is not found, we will ignore it
      // and report the error (but not fatal).
      val edges = typeSymbols.foldLeft(SortedMap.empty[TypeSymbol, Ls[TypeSymbol]]) { case (acc, self) =>
        acc + (self -> extractSuperTypes(self.defn.parents).flatMap { nme =>
          val maybeSymbol = scopeWithTypes.getTypeSymbol(nme.name)
          if (maybeSymbol.isEmpty) {
            raiseError(PreTyping, msg"could not find definition `${nme.name}`" -> nme.toLoc)
          }
          maybeSymbol
        })
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
      (completeScope, new TypeContents)
    }({ case (scope, contents) => s"traverseStatements ==> Scope {${scope.showLocalSymbols}}" })

  def process(typingUnit: TypingUnit, scope: Scope, name: Str): (Scope, TypeContents) =
    trace(s"process <== $name: ${typingUnit.describe}") {
      traverseStatements(typingUnit.entities, name, scope)
    }({ case (scope, contents) => s"process ==> ${scope.showLocalSymbols}" })
  
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
  private def extractSignatureTypes(ty: Type): Ls[TypeName] = {
    @tailrec
    def rec(acc: Ls[TypeName], ty: Type): Ls[TypeName] = ty match {
      case tn: TypeName => tn :: acc
      case AppliedType(tn: TypeName, _) => tn :: acc
      case Union(lhs, tn: TypeName) => rec(tn :: acc, lhs)
      case Union(lhs, AppliedType(tn: TypeName, _)) => rec(tn :: acc, lhs)
      case other =>
        // Let's not raise warning for now.
        // raiseWarning(msg"unknown type in signature" -> other.toLoc)
        Nil
    }
    rec(Nil, ty).reverse
  }
}

object PreTyper {

  def extractSuperTypes(parents: Ls[Term]): Ls[Var] = {
    @tailrec
    def rec(results: Ls[Var], waitlist: Ls[Term]): Ls[Var] =
      waitlist match {
        case Nil => results.reverse
        case (nme: Var) :: tail => rec(nme :: results, tail)
        case (TyApp(ty, _)) :: tail => rec(results, ty :: tail)
        case (App(term, Tup(_))) :: tail => rec(results, term :: tail)
        case other :: _ => println(s"Unknown parent type: $other"); ???
      }
    rec(Nil, parents)
  }

  def transitiveClosure[A](graph: Map[A, List[A]])(implicit ord: Ordering[A]): SortedMap[A, List[A]] = {
    def dfs(vertex: A, visited: Set[A]): Set[A] = {
      if (visited.contains(vertex)) visited
      else graph.getOrElse(vertex, List())
        .foldLeft(visited + vertex)((acc, v) => dfs(v, acc))
    }
    graph.keys.map { vertex =>
      val closure = dfs(vertex, Set())
      vertex -> (closure - vertex).toList
    }.toSortedMap
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