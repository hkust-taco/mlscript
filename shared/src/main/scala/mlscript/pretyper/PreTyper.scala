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

  // `visitIf` is meaningless because it represents patterns with terms.

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

  protected def visitVar(v: Var)(implicit scope: Scope): Unit =
    trace(s"visitVar(name = \"$v\")") {
      v.symbolOption match {
        case N => resolveVar(v)
        case S(symbol) => scope.get(v.name) match {
          case S(other) if other === symbol => ()
          case S(other) => throw new Exception(s"Variable $v refers to a different symbol")
          case N => throw new Exception(s"Variable $v not found in scope. It is possibly a free variable.")
        }
      }
    }()

  protected def visitTerm(term: Term)(implicit scope: Scope): Unit =
    trace(s"visitTerm <== ${shortName(term)}") {
      term match {
        case Assign(lhs, rhs) => visitTerm(lhs); visitTerm(rhs)
        case Bra(_, trm) => visitTerm(trm)
        case Lam(lhs, rhs) =>
          visitTerm(rhs)(scope ++ extractParameters(lhs))
        case Sel(receiver, fieldName) => visitTerm(receiver)
        case Let(isRec, nme, rhs, body) =>
          visitTerm(rhs)
          visitTerm(body)(scope + new ValueSymbol(nme, false))
        case New(head, body) =>
        case Tup(fields) => fields.foreach { case (_, Fld(_, t)) => visitTerm(t) }
        case Asc(trm, ty) => visitTerm(trm)
        case ef @ If(_, _) => visitIf(ef)(scope)
        case TyApp(lhs, targs) => // TODO: When?
        case Eqn(lhs, rhs) => ??? // TODO: How?
        case Blk(stmts) => stmts.foreach {
          case t: Term => visitTerm(t)
          case _ => ??? // TODO: When?
        }
        case Subs(arr, idx) => visitTerm(arr); visitTerm(idx)
        case Bind(lhs, rhs) => visitTerm(lhs); visitTerm(rhs)
        case Splc(fields) => fields.foreach {
          case L(t) => visitTerm(t)
          case R(Fld(_, t)) => visitTerm(t)
        }
        case Forall(params, body) => ??? // TODO: When?
        case Rcd(fields) => fields.foreach { case (_, Fld(_, t)) => visitTerm(t) }
        case CaseOf(trm, cases) => 
        case With(trm, fields) => visitTerm(trm); visitTerm(fields)
        case Where(body, where) => ??? // TODO: When?
        case App(lhs, rhs) => visitTerm(lhs); visitTerm(rhs)
        case Test(trm, ty) => visitTerm(trm)
        case _: Lit | _: Super => ()
        case v: Var => visitVar(v)
        case AdtMatchWith(cond, arms) => ??? // TODO: How?
        case Inst(body) => visitTerm(body)
      }
    }(_ => s"visitTerm ==> ${shortName(term)}")

  private def visitNuTypeDef(symbol: TypeSymbol, defn: NuTypeDef)(implicit scope: Scope): Unit =
    trace(s"visitNuTypeDef <== ${defn.kind} ${defn.nme.name}") {
      visitTypingUnit(defn.body, defn.nme.name, scope)
      ()
    }(_ => s"visitNuTypeDef <== ${defn.kind} ${defn.nme.name}")

  private def visitFunction(symbol: FunctionSymbol, defn: NuFunDef)(implicit scope: Scope): Unit =
    trace(s"visitFunction <== ${defn.nme.name}") {
      defn.rhs match {
        case Left(term) => 
          val subScope = if (defn.isLetRec === S(false)) scope else scope + symbol
          visitTerm(term)(subScope)
        case Right(value) => ()
      }
    }(_ => s"visitFunction ==> ${defn.nme.name}")

  private def visitLetBinding(symbol: ValueSymbol, rec: Bool, rhs: Term)(implicit scope: Scope): Unit =
    trace(s"visitLetBinding(rec = $rec, ${symbol.name})") {

    }()

  private def visitTypingUnit(typingUnit: TypingUnit, name: Str, parentScope: Scope): (Scope, TypeContents) =
    trace(s"visitTypingUnit <== $name: ${typingUnit.describe}") {
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
        case (acc, term: Term) => visitTerm(term)(acc); acc
        case (acc, defn: NuTypeDef) => acc
        case (acc, defn @ NuFunDef(Some(rec), nme, _, _, L(rhs))) =>
          val symbol = new ValueSymbol(defn.nme, true)
          val scopeWithVar = acc + symbol
          visitLetBinding(symbol, rec, rhs)(if (rec) { scopeWithVar } else { acc })
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
          visitNuTypeDef(symbol, symbol.defn)(innerScope)
        case symbol: FunctionSymbol => visitFunction(symbol, symbol.defn)(completeScope)
        case _: ValueSymbol => ()
        case _: SubValueSymbol => ()
      }
      (completeScope, new TypeContents)
    }({ case (scope, contents) => s"visitTypingUnit ==> ${scope.showLocalSymbols}" })

  def process(typingUnit: TypingUnit, scope: Scope, name: Str): (Scope, TypeContents) =
    trace(s"process <== $name: ${typingUnit.describe}") {
      visitTypingUnit(typingUnit, name, scope)
    }({ case (scope, contents) => s"process ==> ${scope.showLocalSymbols}" })
}
