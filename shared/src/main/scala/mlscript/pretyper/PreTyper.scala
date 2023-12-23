package mlscript.pretyper

import collection.mutable.{Set => MutSet}
import mlscript.ucs.DesugarUCS
import symbol._
import mlscript._, utils._, shorthands._
import scala.annotation.tailrec
import mlscript.Message, Message.MessageContext

class PreTyper(override val debugTopics: Opt[Set[Str]]) extends Traceable with DesugarUCS {
  import PreTyper._

  protected def raise(diagnostics: Diagnostic): Unit = ()
  protected def raise(diagnostics: Ls[Diagnostic]): Unit = ()

  private def extractParameters(fields: Term): Ls[ValueSymbol] =
    trace(s"extractParameters <== ${inspect.deep(fields)}") {
      fields match {
        case Tup(arguments) =>
          arguments.map {
            case (S(nme: Var), Fld(_, _)) => new ValueSymbol(nme, false)
            case (_, Fld(_, nme: Var)) => new ValueSymbol(nme, false)
            case (_, Fld(_, Bra(false, nme: Var))) => new ValueSymbol(nme, false)
            case (_, _) => ???
          }
        case PlainTup(arguments @ _*) =>
          arguments.map {
            case nme: Var => new ValueSymbol(nme, false)
            case other => println("Unknown parameters: " + inspect.deep(other)); ??? // TODO: bad
          }.toList
        case other => println("Unknown parameters: " + inspect.deep(other)); ??? // TODO: bad
      }
    }(rs => s"extractParameters ==> ${rs.iterator.map(_.name).mkString(", ")}")

  // `traverseIf` is meaningless because it represents patterns with terms.

  protected def resolveVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"resolveVar(name = \"$v\")") {
      scope.getTermSymbol(v.name) match {
        case S(sym: ValueSymbol) =>
          println(s"Resolve variable $v to a value.")
          v.symbol = sym
        case S(sym: SubValueSymbol) =>
          println(s"Resolve variable $v to a value.")
          v.symbol = sym
        case S(sym: FunctionSymbol) =>
          println(s"Resolve variable $v to a function.")
          v.symbol = sym
        case N => 
          scope.getTypeSymbol(v.name) match {
            case S(sym: ClassSymbol) =>
              if (sym.defn.kind == Cls) {
                println(s"Resolve variable $v to a class.")
                v.symbol = sym
              } else {
                throw new Exception(s"Name $v refers to a type")
              }
            case S(_) => throw new Exception(s"Name $v refers to a type")
            case N => throw new Exception(s"Variable $v not found in scope")
          }
      }
    }()

  protected def traverseVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"traverseVar(name = \"$v\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.getSymbols(v.name) match {
          case Nil => throw new Exception(s"Variable $v not found in scope. It is possibly a free variable.")
          case symbols if symbols.contains(symbol) => ()
          case _ => throw new Exception(s"Variable $v refers to a different symbol")
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
          traverseTerm(body)(scope + new ValueSymbol(nme, false))
        case New(head, body) =>
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

  private def traverseFunction(symbol: FunctionSymbol, defn: NuFunDef)(implicit scope: Scope): Unit =
    trace(s"traverseFunction <== ${defn.nme.name}") {
      require(defn.isLetRec.isEmpty) // Make sure it's defined via `fun`.
      defn.rhs match {
        case Left(term) => 
          val subScope = if (defn.isLetRec === S(false)) scope else scope + symbol
          traverseTerm(term)(subScope)
        case Right(ty) => println(s"found a pure declaration: $ty")
      }
    }(_ => s"traverseFunction ==> ${defn.nme.name}")

  private def traverseLetBinding(symbol: ValueSymbol, rec: Bool, rhs: Term)(implicit scope: Scope): Unit =
    trace(s"traverseLetBinding(rec = $rec, ${symbol.name})") {

    }()

  private def traverseStatements(statements: Ls[Statement], name: Str, parentScope: Scope): (Scope, TypeContents) =
    trace(s"traverseStatements <== $name: ${"statement".pluralize(statements.size, true)}") {
      import mlscript.{Cls, Trt, Mxn, Als, Mod}
      // Pass 1: Build a scope with hoisted symbols.
      val hoistedScope = statements.foldLeft(parentScope.derive) {
        case (acc, _: Term) => acc // Skip
        case (acc, defn: NuTypeDef) =>
          val `var` = Var(defn.nme.name).withLoc(defn.nme.toLoc)
          // Create a type symbol but do not visit its inner members
          val symbol = defn.kind match {
            case Cls => new ClassSymbol(defn)
            case Als => new TypeAliasSymbol(defn)
            case Mxn => new MixinSymbol(defn)
            case Trt => new TraitSymbol(defn)
            case Mod => new ModuleSymbol(defn)
          }
          println("parent types: " + defn.parents.iterator.map(inspect.deep(_)).mkString("; "))
          acc ++ (symbol ::
            (defn.kind match {
              case Mod => new ValueSymbol(`var`, true) :: Nil
              case Als | Cls | Mxn | Trt => Nil
            }))
        case (acc, defn: NuFunDef) if defn.isLetRec.isEmpty => acc + new FunctionSymbol(defn)
        case (acc, _: NuFunDef) => acc
        case (acc, _: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef) => ??? // TODO: When?
      }
      // Resolve base types.
      val subtypingRelations = statements.foldLeft(Map.empty[Var, Ls[Var]]) {
        case (acc, defn: NuTypeDef) =>
          val thisType = Var(defn.nme.name).withLoc(defn.nme.toLoc)
          val superTypes = extractSuperTypes(defn.parents)
          acc + (thisType -> superTypes)
        case (acc, _: Term | _: NuFunDef) => acc
        case (acc, _: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef) => ??? // TODO: When?
      }
      val superTypes = transitiveClosure(subtypingRelations)
      printGraph(subtypingRelations, println, "Subtyping relations", "->")
      superTypes.foreachEntry { case (thisType, baseTypes) =>
        hoistedScope.getTypeSymbol(thisType.name) match {
          case S(symbol) => symbol.baseTypes =
            baseTypes.map(baseType => hoistedScope.getTypeSymbol(baseType.name).getOrElse(???))
          case N => ???
        } // FIXME: Generate proper diagnostics.
      }
      // Resolve sealed types.
      println("Resolve sealed signature types")
      hoistedScope.types.foreachEntry {
        case _ -> (_: MixinSymbol | _: TypeAliasSymbol) => ()
        case (name, symbol) => symbol.defn.sig.foreach { unions =>
          def rec(acc: Ls[TypeName], ty: Type): Ls[TypeName] = ty match {
            case tn: TypeName => tn :: acc
            case AppliedType(tn: TypeName, _) => tn :: acc
            case Union(lhs, tn: TypeName) => rec(tn :: acc, lhs)
            case Union(lhs, AppliedType(tn: TypeName, _)) => rec(tn :: acc, lhs)
            case other => println(s"Unknown type: $other"); ???
          }
          val derivedTypes = try rec(Nil, unions) catch { case _: NotImplementedError => Nil }
          symbol.sealedDerivedTypes = derivedTypes.flatMap { derivedType =>
            val maybeSymbol = hoistedScope.getTypeSymbol(derivedType.name)
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
      println(hoistedScope.symbols.map(_.name).mkString("(hoisted) scope = {", ", ", "}"))
      // 
      // Pass 2: Visit non-hoisted and build a complete scope.
      val completeScope = statements.foldLeft[Scope](hoistedScope) {
        case (acc, term: Term) => traverseTerm(term)(acc); acc
        case (acc, defn: NuTypeDef) => acc
        case (acc, defn @ NuFunDef(Some(rec), nme, _, _, L(rhs))) =>
          val symbol = new ValueSymbol(defn.nme, true)
          val scopeWithVar = acc + symbol
          traverseLetBinding(symbol, rec, rhs)(if (rec) { scopeWithVar } else { acc })
          scopeWithVar
        case (acc, defn @ NuFunDef(Some(rec), nme, _, _, R(ty))) =>
          val symbol = new ValueSymbol(defn.nme, true)
          acc + symbol
        case (acc, _: NuFunDef) => acc
        case (acc, _: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef) => ??? // TODO: When?
      }
      println(hoistedScope.symbols.map(_.name).mkString("(complete) scope = {", ", ", "}"))
      // Pass 3: Visit hoisted symbols.
      val visitedSymbol = MutSet.empty[FunctionSymbol]
      completeScope.symbols.foreach {
        case symbol: TypeSymbol =>
          val innerScope = symbol.defn.kind match {
            case Cls =>
              completeScope.derive(
                new ValueSymbol(Var("this"), false) ::
                  (symbol.defn.params match {
                    case N => Nil
                    case S(fields) => extractParameters(fields)
                  })
              )
            case Als | Mod | Mxn | Trt => completeScope
          }
          traverseTypeDefinition(symbol, symbol.defn)(innerScope)
        case symbol: FunctionSymbol if !visitedSymbol(symbol) =>
          visitedSymbol += symbol
          traverseFunction(symbol, symbol.defn)(completeScope)
        case _: FunctionSymbol | _: ValueSymbol | _: SubValueSymbol => ()
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

  def transitiveClosure(graph: Map[Var, List[Var]]): Map[Var, List[Var]] = {
    def dfs(vertex: Var, visited: Set[Var]): Set[Var] = {
      if (visited.contains(vertex)) visited
      else graph.getOrElse(vertex, List())
        .foldLeft(visited + vertex)((acc, v) => dfs(v, acc))
    }

    graph.keys.map { vertex =>
      val closure = dfs(vertex, Set())
      vertex -> (closure - vertex).toList
    }.toMap
  }

  def printGraph(graph: Map[Var, List[Var]], print: (=> Any) => Unit, title: String, arrow: String): Unit = {
    print(s"• $title")
    if (graph.isEmpty)
      print("  + <Empty>")
    else
      graph.foreachEntry { (source, targets) =>
        print(s"  + $source $arrow " + {
          if (targets.isEmpty) s"{}"
          else targets.mkString("{ ", ", ", " }")
        })
      }
  }
}