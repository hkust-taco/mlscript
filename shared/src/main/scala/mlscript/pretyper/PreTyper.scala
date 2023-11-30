package mlscript.pretyper

import mlscript.ucs.DesugarUCS
import mlscript._, utils._, shorthands._
import mlscript.codegen.Helpers.inspect

class PreTyper(override val debugLevel: Opt[Int], useNewDefs: Bool) extends Traceable with DesugarUCS {
  protected def raise(diagnostics: Ls[Diagnostic]): Unit = ()

  private def extractParameters(fields: Term): Ls[ValueSymbol] = fields match {
    case Tup(arguments) =>
      if (useNewDefs) {
        arguments.map {
          case (S(nme: Var), Fld(_, _)) => new ValueSymbol(nme, false)
          case (_, Fld(_, nme: Var)) => new ValueSymbol(nme, false)
          case (_, Fld(_, x)) => println(x.toString); ???
        }
      } else {
        arguments.map {
          case (_, Fld(_, nme: Var)) => new ValueSymbol(nme, false)
          case (_, Fld(_, x)) => println(x.toString); ???
        }
      }
    case PlainTup(arguments @ _*) =>
      arguments.map {
        case nme: Var => new ValueSymbol(nme, false)
        case other => println("Unknown parameters: " + inspect(other)); ??? // TODO: bad
      }.toList
    case other => println("Unknown parameters: " + inspect(other)); ??? // TODO: bad
  }

  // `traverseIf` is meaningless because it represents patterns with terms.

  protected def resolveVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"resolveVar(name = \"$v\")") {
      scope.get(v.name) match {
        case Some(sym: ValueSymbol) =>
          println(s"Resolve variable $v to a value.", 2)
          v.symbol = sym
        case Some(sym: SubValueSymbol) =>
          println(s"Resolve variable $v to a value.", 2)
          v.symbol = sym
        case Some(sym: FunctionSymbol) =>
          println(s"Resolve variable $v to a function.", 2)
          v.symbol = sym
        case Some(sym: TypeSymbol) =>
          if (sym.defn.kind == Cls) {
            println(s"Resolve variable $v to a class.", 2)
            v.symbol = sym
          } else {
            throw new Exception(s"Name $v refers to a type")
          }
        case None => throw new Exception(s"Variable $v not found in scope")
      }
    }()

  protected def traverseVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"traverseVar(name = \"$v\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.get(v.name) match {
          case S(other) if other === symbol => ()
          case S(other) => throw new Exception(s"Variable $v refers to a different symbol")
          case N => throw new Exception(s"Variable $v not found in scope. It is possibly a free variable.")
        }
      }
    }()

  protected def traverseTerm(term: Term)(implicit scope: Scope): Unit =
    trace(s"traverseTerm <== ${shortName(term)}") {
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
        case Blk(stmts) => stmts.foreach {
          case t: Term => traverseTerm(t)
          case _ => ??? // TODO: When?
        }
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
      }
    }(_ => s"traverseTerm ==> ${shortName(term)}")

  private def traverseNuTypeDef(symbol: TypeSymbol, defn: NuTypeDef)(implicit scope: Scope): Unit =
    trace(s"traverseNuTypeDef <== ${defn.kind} ${defn.nme.name}") {
      traverseTypingUnit(defn.body, defn.nme.name, scope)
      ()
    }(_ => s"traverseNuTypeDef <== ${defn.kind} ${defn.nme.name}")

  private def traverseFunction(symbol: FunctionSymbol, defn: NuFunDef)(implicit scope: Scope): Unit =
    trace(s"traverseFunction <== ${defn.nme.name}") {
      defn.rhs match {
        case Left(term) => 
          val subScope = if (defn.isLetRec === S(false)) scope else scope + symbol
          traverseTerm(term)(subScope)
        case Right(value) => ()
      }
    }(_ => s"traverseFunction ==> ${defn.nme.name}")

  private def traverseLetBinding(symbol: ValueSymbol, rec: Bool, rhs: Term)(implicit scope: Scope): Unit =
    trace(s"traverseLetBinding(rec = $rec, ${symbol.name})") {

    }()

  private def traverseTypingUnit(typingUnit: TypingUnit, name: Str, parentScope: Scope): (Scope, TypeContents) =
    trace(s"traverseTypingUnit <== $name: ${typingUnit.describe}") {
      import mlscript.{Cls, Trt, Mxn, Als, Mod}
      // Pass 1: Build a scope with hoisted symbols.
      val hoistedScope = typingUnit.entities.foldLeft(parentScope.derive) {
        case (acc, _: Term) => acc // Skip
        case (acc, defn: NuTypeDef) =>
          val `var` = Var(defn.nme.name).withLoc(defn.nme.toLoc)
          // Create a type symbol but do not visit its inner members
          acc ++ (new TypeSymbol(defn.nme, defn) ::
            (defn.kind match {
              case Mod => new ValueSymbol(`var`, true) :: Nil
              case Als | Cls | Mxn | Trt => Nil
            }))
        case (acc, defn: NuFunDef) if defn.isLetRec.isEmpty =>
          acc + new FunctionSymbol(defn.nme, defn)
        case (acc, _: NuFunDef) => acc
        case (acc, _: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef) => ??? // TODO: When?
      }
      println(hoistedScope.symbols.map(_.name).mkString("1. scope = {", ", ", "}"))
      // Pass 2: Visit non-hoisted and build a complete scope.
      val completeScope = typingUnit.entities.foldLeft[Scope](hoistedScope) {
        case (acc, term: Term) => traverseTerm(term)(acc); acc
        case (acc, defn: NuTypeDef) => acc
        case (acc, defn @ NuFunDef(Some(rec), nme, _, _, L(rhs))) =>
          val symbol = new ValueSymbol(defn.nme, true)
          val scopeWithVar = acc + symbol
          traverseLetBinding(symbol, rec, rhs)(if (rec) { scopeWithVar } else { acc })
          scopeWithVar
        case (acc, _: NuFunDef) => acc
        case (acc, _: Constructor | _: DataDefn | _: DatatypeDefn | _: Def | _: LetS | _: TypeDef) => ??? // TODO: When?
      }
      println(hoistedScope.symbols.map(_.name).mkString("2. scope = {", ", ", "}"))
      import pretyper.TypeSymbol
      // Pass 3: Visit hoisted symbols.
      completeScope.symbols.foreach {
        case symbol: TypeSymbol =>
          val innerScope = symbol.defn.kind match {
            case Cls =>
              completeScope.derive ++ (symbol.defn.params match {
                case N => Nil
                case S(fields) => extractParameters(fields)
              })
            case Als | Mod | Mxn | Trt => completeScope
          }
          traverseNuTypeDef(symbol, symbol.defn)(innerScope)
        case symbol: FunctionSymbol => traverseFunction(symbol, symbol.defn)(completeScope)
        case _: ValueSymbol => ()
        case _: SubValueSymbol => ()
      }
      (completeScope, new TypeContents)
    }({ case (scope, contents) => s"traverseTypingUnit ==> ${scope.showLocalSymbols}" })

  def process(typingUnit: TypingUnit, scope: Scope, name: Str): (Scope, TypeContents) =
    trace(s"process <== $name: ${typingUnit.describe}") {
      traverseTypingUnit(typingUnit, name, scope)
    }({ case (scope, contents) => s"process ==> ${scope.showLocalSymbols}" })
}
