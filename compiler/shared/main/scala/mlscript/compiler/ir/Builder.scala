package mlscript.compiler.ir

import mlscript.compiler.optimizer.FreeVarAnalysis
import mlscript.utils.shorthands._
import mlscript.utils._
import mlscript._
import mlscript.Message.MessageContext
import scala.collection.mutable.ListBuffer

final val ops = Set("+", "-", "*", "/", ">", "<", ">=", "<=", "!=", "==")
final val builtin = Set("builtin")

final class Builder(fresh: Fresh, fnUid: FreshInt, classUid: FreshInt, tag: FreshInt, raise: Diagnostic => Unit, verbose: Boolean = false):
  import Node._
  import Expr._
  
  private def log(x: Any) = if verbose then println(x)

  private final case class ClassInfoPartial(name: Str, fields: Ls[Str], methods: Set[Str]):
    var freeVars = Ls.empty[Str]
    var ctx = ctxEmpty

  private final case class DefnInfoPartial(name: Str, params: Ls[Str]):
    var freeVars = Ls.empty[Str]
    var ctx = ctxEmpty

  private type NameCtx = Map[Str, Name] // name -> new name
  private type ClassCtx = Map[Str, ClassInfoPartial] // class name -> partial class info
  private type FnCtx = Map[Str, DefnInfoPartial]    // fn name -> partial defn info
  private type OpCtx = Set[Str]         // op names
  
  private final case class Ctx(
    nameCtx: NameCtx = Map.empty,
    tyNameCtx: NameCtx = Map.empty,
    classCtx: ClassCtx = Map.empty,
    fnCtx: FnCtx = Map.empty,
    opCtx: OpCtx = Set.empty,
    jpAcc: ListBuffer[Defn],
    defAcc: ListBuffer[NuFunDef],
    lcAcc: ListBuffer[NuTypeDef],
  ):
    def hasClassLifted = lcAcc.nonEmpty
    def hasLifted = jpAcc.nonEmpty || defAcc.nonEmpty || lcAcc.nonEmpty

  private def ctxEmpty = Ctx(
      nameCtx = Map.empty,
      tyNameCtx = Map.empty,
      classCtx = Map.empty,
      fnCtx = Map.empty,
      opCtx = ops,
      jpAcc = ListBuffer.empty,
      defAcc = ListBuffer.empty,
      lcAcc = ListBuffer.empty,
  )

  private def ctxJoin(c1: Ctx, c2: Ctx) =
    Ctx(
      nameCtx = c1.nameCtx ++ c2.nameCtx,
      tyNameCtx = c1.tyNameCtx ++ c2.tyNameCtx,
      classCtx = c1.classCtx ++ c2.classCtx,
      fnCtx = c1.fnCtx ++ c2.fnCtx,
      opCtx = c1.opCtx ++ c2.opCtx,
      jpAcc = c1.jpAcc,
      defAcc = c1.defAcc,
      lcAcc = c1.lcAcc,
    )

  private def ref(x: Name) = Ref(x)
  private def result(x: Ls[TrivialExpr]) = Result(x).attachTag(tag)
  private def sresult(x: TrivialExpr) = Result(Ls(x)).attachTag(tag)
  private def unexpectedNode(x: Node) = throw IRError(s"unsupported node $x")
  private def unexpectedTerm(x: Statement) = throw IRError(s"unsupported term $x")

  private def buildBinding(using ctx: Ctx)(name: Str, e: Term, body: Term)(k: Node => Node): Node =
    buildResultFromTerm(e) {
      case Result((r: Ref) :: Nil) =>
        given Ctx = ctx.copy(nameCtx = ctx.nameCtx + (name -> r.name))
        buildResultFromTerm(body)(k)
      case Result((lit: Literal) :: Nil) =>
        val v = fresh.make
        given Ctx = ctx.copy(nameCtx = ctx.nameCtx + (name -> v))
        LetExpr(v,
          lit,
          buildResultFromTerm(body)(k)).attachTag(tag)
      case node @ _ => node |> unexpectedNode
    }
  
  private def buildResultFromTup(using ctx: Ctx)(tup: Tup)(k: Node => Node): Node =
    tup match
      case Tup(N -> Fld(FldFlags.empty, x) :: xs) => buildResultFromTerm(x) {
        case Result(x :: Nil) =>
          buildResultFromTup(Tup(xs)) {
            case Result(xs) => x :: xs |> result |> k
            case node @ _ => node |> unexpectedNode
          }
        case node @ _ => node |> unexpectedNode
      }
      case Tup(Nil) => Nil |> result |> k
      
  private def bindingPatternVariables(scrut: Str, tup: Tup, cls: ClassInfoPartial, rhs: Term): Term =
    val params = tup |> getTupleFields
    val fields = cls.fields
    val tm = params.zip(fields).foldLeft(rhs) {
      case (tm, (param, field)) => 
        Let(false, Var(param), App(Sel(Var(cls.name), Var(field)), Tup(Ls(N -> Fld(FldFlags.empty, Var(scrut))))), tm)
    }
    tm

  private def freeVariablesIf(ucs: If): Set[Str] =
    val ifbody: IfBody = ucs.body
    val els: Opt[Term] = ucs.els

    def f(ifbody: IfBody): Set[Str] = ifbody match
      case IfBlock(lines) => lines.foldLeft(Set.empty[Str]) {
        case (acc, Left(ifbody2)) => acc ++ f(ifbody2)
        case (acc, Right(rhs)) => acc ++ freeVariables(rhs)._2
      }
      case IfElse(expr) => freeVariables(expr)
      case IfLet(isRec, name, rhs, body) =>
        if isRec then
          (freeVariables(rhs) -- freeVariables(name)) ++ (f(body) -- freeVariables(name))
        else
          freeVariables(rhs) ++ (f(body) -- freeVariables(name))
      case IfOpApp(lhs, op, rhs) => freeVariables(lhs) ++ f(rhs)
      case IfOpsApp(lhs, opsRhss) => freeVariables(lhs) ++ opsRhss.foldLeft(Set.empty[Str]) {
        case (acc, (op, rhs)) => acc ++ f(rhs)
      }
      case IfThen(expr, rhs) => freeVariables(rhs) -- freeVariables(expr)

    val fvs1 = f(ifbody)
    val fvs2 = els.fold(Set.empty[Str]) { freeVariables }

    fvs1 ++ fvs2

  private def freeVariables(tu: TypingUnit): Set[Str] =
    var all_defined = tu.rawEntities.foldLeft(Set.empty[Str]) {
      case (defined, stmt) => defined ++ freeVariables(stmt)._1
    }
    tu.rawEntities.foldLeft(Set.empty[Str]) {
      case (acc, stmt) => acc ++ (freeVariables(stmt)._2 -- all_defined)
    }

    // for this fv analysis, we also need to return the variables that are defined in this statement
  private def freeVariables(stmt: Statement): (Set[Str], Set[Str]) = stmt match
    case DataDefn(body) => throw IRError("unsupported DataDefn")
    case DatatypeDefn(head, body) => throw IRError("unsupported DatatypeDefn")
    case LetS(isRec, pat, rhs) => throw IRError("unsupported LetS")
    case ntd: NuTypeDef => 
      val fvs = freeVariables(ntd.body) -- ntd.params.fold(Set.empty)(freeVariables)
      (Set(ntd.nme.name), fvs)
    case Constructor(params, body) => throw IRError("unsupported Constructor")
    case nfd: NuFunDef =>
      val fvs = nfd.isLetRec match
        case None | Some(true) => nfd.rhs.fold(tm => freeVariables(tm) -- freeVariables(nfd.nme), ty => Set.empty)
        case Some(false) => nfd.rhs.fold(tm => freeVariables(tm), ty => Set.empty)
      (freeVariables(nfd.nme), fvs)
    case Def(rec, nme, rhs, isByname) => throw IRError("unsupported Def")
    case TypeDef(kind, nme, tparams, body, mthDecls, mthDefs, positionals, adtInfo) => throw IRError("unsupported TypeDef")
    case x: Term =>
      val fvs = freeVariables(x)
      (Set.empty, fvs)

  private def freeVariables(tm: Term): Set[Str] = tm match
    case AdtMatchWith(cond, arms) =>
      val inner: Set[Str] = arms.foldLeft(Set.empty){
        case (acc, AdtMatchPat(pat, body)) => acc ++ freeVariables(body) -- freeVariables(pat)
      }
      freeVariables(cond) ++ inner
    case Ann(ann, receiver) => freeVariables(receiver)
    case App(lhs, rhs) => freeVariables(lhs) ++ freeVariables(rhs)
    case Asc(trm, ty) => freeVariables(trm)
    case Assign(lhs, rhs) => freeVariables(lhs) ++ freeVariables(rhs)
    case Bind(lhs, rhs) => freeVariables(lhs)
    case Blk(stmts) => 
      var fvs = Set.empty[Str]
      var defined = Set.empty[Str]
      stmts.foreach {
        stmt => {
          val stmt_fvs = freeVariables(stmt)
          fvs ++= stmt_fvs._2
          fvs --= defined
          defined ++= stmt_fvs._1
        }
      }
      fvs
    case Bra(rcd, trm) => freeVariables(trm)
    case CaseOf(trm, cases) =>
      import mlscript.{Case => CCase}
      def f(pat: CaseBranches): Set[Str] =
        pat match
          case CCase(pat, body, rest) => freeVariables(body) -- freeVariables(pat) ++ f(rest)
          case NoCases => Set.empty
          case Wildcard(body) => freeVariables(body)
      freeVariables(trm) ++ f(cases)
    case Eqn(lhs, rhs) => freeVariables(rhs)
    case Forall(params, body) => freeVariables(body)
    case x: If => freeVariablesIf(x)
    case Inst(body) => freeVariables(body)
    case Lam(lhs, rhs) => 
      freeVariables(rhs) -- freeVariables(lhs)
    case Let(isRec, name, rhs, body) => 
      if isRec then
        (freeVariables(rhs) -- freeVariables(name)) ++ (freeVariables(body) -- freeVariables(name))
      else
        freeVariables(rhs) ++ (freeVariables(body) -- freeVariables(name))
    case New(head, body) => throw IRError("unsupported New")
    case NuNew(cls) => freeVariables(cls)
    case Quoted(body) => throw IRError("unsupported Quoted")
    case Rcd(fields) => fields.foldLeft(Set.empty[Str]) {
      case (acc, (_, Fld(_, trm))) => acc ++ freeVariables(trm)
    }
    case Rft(base, decls) => throw IRError("unsupported Rft")
    case Sel(receiver, fieldName) => freeVariables(receiver)
    case Splc(fields) => fields.foldLeft(Set.empty[Str]) {
      case (acc, Left(trm)) => acc ++ freeVariables(trm) 
      case (acc, Right(Fld(_, trm))) => acc ++ freeVariables(trm)
    }
    case Subs(arr, idx) => freeVariables(arr) ++ freeVariables(idx)
    case Super() => Set.empty
    case Test(trm, ty) => freeVariables(trm)
    case Tup(fields) => fields.foldLeft(Set.empty[Str]) {
      case (acc, (_, Fld(_, trm))) => acc ++ freeVariables(trm)
    }
    case TyApp(lhs, targs) => freeVariables(lhs)
    case Unquoted(body) => throw IRError("unsupported Unquoted")
    case Where(body, where) => throw IRError("unsupported Where")
    case While(cond, body) => freeVariables(cond) ++ freeVariables(body)
    case With(trm, fields) => freeVariables(trm) ++ freeVariables(fields: Term)
    case Var(name) => Set(name)
    case DecLit(value) => Set.empty
    case IntLit(value) => Set.empty
    case StrLit(value) => Set.empty
    case UnitLit(undefinedOrNull) => Set.empty

    private def buildLetCall(using ctx: Ctx)(f: Var, xs: Tup, ann: Option[Term])(k: Node => Node) =        
      buildResultFromTup(xs) {
        case Result(args) =>
          val v = fresh.make
          ctx.nameCtx.get(f.name) match
            case None => throw IRError(s"unknown name $f in $ctx")
            case Some(f2) =>
              ctx.fnCtx.get(f2.str) match
                case None => throw IRError(s"unknown function $f2 in $ctx")
                case Some(dInfo) =>
                  val args2 = 
                    if args.size != dInfo.params.size then
                      args ++ dInfo.freeVars.map(x => Ref(ctx.nameCtx(x))) // it's possible that the free vars as parameters have been filled when do eta expansion
                    else
                      args
                  ann match
                    case Some(ann @ Var(nme)) =>
                      if nme === "tailcall" then 
                        LetCall(List(v), DefnRef(Right(f2.str)), args2, true, v |> ref |> sresult |> k)(f.toLoc).attachTag(tag)
                      else
                        if nme === "tailrec" then
                          raise(ErrorReport(List(msg"@tailrec is for annotating functions; try @tailcall instead" -> ann.toLoc), true, Diagnostic.Compilation))
                        LetCall(List(v), DefnRef(Right(f2.str)), args2, false, v |> ref |> sresult |> k)(f.toLoc).attachTag(tag) 
                    case Some(_) => throw IRError("unsupported annotation")
                    case None => LetCall(List(v), DefnRef(Right(f2.str)), args2, false, v |> ref |> sresult |> k)(f.toLoc).attachTag(tag)
        case node @ _ => node |> unexpectedNode
      }
  private def buildResultFromTerm(using ctx: Ctx)(tm: Statement)(k: Node => Node): Node =
    val res = tm match
      case lit: Lit => Literal(lit) |> sresult |> k
      case v @ Var(name) =>
        if (name.isCapitalized)
          ctx.tyNameCtx.get(name) match
            case Some(x) => 
              val v = fresh.make
              ctx.classCtx.get(x.str) match
                case Some(clsinfo) =>
                  val args = (if clsinfo.freeVars.isEmpty then Nil else clsinfo.freeVars.map(x => Ref(ctx.nameCtx(x))))
                  LetExpr(v,
                    CtorApp(ClassRef(Right(x.str)), args),
                    v |> ref |> sresult |> k).attachTag(tag)
                case None => throw IRError(s"unknown class $name in $ctx")
            case None => throw IRError(s"unknown type name $name in $ctx")
        else
          ctx.nameCtx.get(name) match {
            case Some(x) =>
              if (ctx.fnCtx.contains(x.str))
                val info = ctx.fnCtx(x.str)
                val arity = info.params.size - info.freeVars.size
                val range = 0 until arity
                val xs = range.map(_ => fresh.make.str).toList
                val params = Tup(xs.map(x => N -> Fld(FldFlags.empty, Var(x))))
                val args = Tup(params.fields ++ info.freeVars.map(x => N -> Fld(FldFlags.empty, Var(x))))
                val lam = Lam(params, App(Var(x.str), args))
                buildResultFromTerm(lam)(k)
              else
                x |> ref |> sresult |> k
            case None => throw IRError(s"unknown name $name in $ctx")
          }
      case lam @ Lam(Tup(fields), body) =>
        val tmp = fresh.make
        val lambdaName = fresh.make("Lambda")
        val result = Var(lambdaName.str)
        val localCls = Blk(
          NuTypeDef(Cls, TypeName(lambdaName.str), Nil, N, N, N, Ls(Var("Callable")), N, N, TypingUnit(
            NuFunDef(N, Var(s"apply${fields.size}"), None, Nil, L(Lam(Tup(fields), body)))(tm.getLoc, N, N, N, N, false, Nil) :: Nil
          ))(tm.getLoc, tm.getLoc, Nil) :: result :: Nil)
        buildResultFromTerm(localCls)(k)

      case App(
        App(Var(name), Tup((_ -> Fld(_, e1)) :: Nil)),
        Tup((_ -> Fld(_, e2)) :: Nil)) if ctx.opCtx.contains(name) =>
        buildResultFromTerm(e1) {
          case Result(v1 :: Nil) =>
            buildResultFromTerm(e2) {
              case Result(v2 :: Nil) =>
                val v = fresh.make
                LetExpr(v,
                  BasicOp(name, List(v1, v2)),
                  v |> ref |> sresult |> k).attachTag(tag)
              case node @ _ => node |> unexpectedNode
            }
          case node @ _ => node |> unexpectedNode
        }
      case x @ App(Var(name), xs @ Tup(_)) if name.isCapitalized || ctx.opCtx.contains(name) =>
        if name.isCapitalized then
          buildResultFromTerm(xs) {
            case Result(args) => 
              ctx.tyNameCtx.get(name) match
                case Some(x) =>
                  val v = fresh.make
                  ctx.classCtx.get(x.str) match
                    case Some(clsinfo) =>
                      val args2 = args ++ clsinfo.freeVars.map(x => Ref(ctx.nameCtx(x)))
                      LetExpr(v,
                        CtorApp(ClassRef(Right(x.str)), args2),
                        v |> ref |> sresult |> k).attachTag(tag)
                    case None => throw IRError(s"unknown class $name in $ctx")
                case None => throw IRError(s"unknown type name $name in $ctx")
            case node @ _ => node |> unexpectedNode
          }
        else
          buildResultFromTerm(xs) {
            case Result(args) =>
              val v = fresh.make
              LetExpr(v,
                BasicOp(name, args),
                v |> ref |> sresult |> k).attachTag(tag)
            case node @ _ => node |> unexpectedNode
          }
      case App(
        member @ Sel(Var(clsName), Var(fld)), 
        xs @ Tup((_ -> Fld(_, Var(s))) :: _)) if clsName.isCapitalized =>
        buildResultFromTup(xs) {
          case Result(xs @ (Ref(name) :: args)) =>
            ctx.tyNameCtx.get(clsName) match
              case Some(x) => 
                val v = fresh.make
                val cls = ctx.classCtx(x.str)
                val isField = cls.fields.contains(fld)
                if isField then
                  LetExpr(v, Select(name, ClassRef(Right(x.str)), fld),
                    v |> ref |> sresult |> k).attachTag(tag)
                else
                  if cls.methods.contains(fld) then
                    LetMethodCall(Ls(v), ClassRef(Right(x.str)), Name(fld), xs, v |> ref |> sresult |> k).attachTag(tag)
                  else
                    throw IRError(s"unknown field or method $fld in $cls")
              case None => throw IRError(s"unknown type name $clsName in $ctx")
          case node @ _ => node |> unexpectedNode
        }
      case App(vf @ Var(f), xs @ Tup(_)) if ctx.fnCtx.contains(f) || ctx.nameCtx.get(f).fold(false)(x => ctx.fnCtx.contains(x.str)) => 
        buildLetCall(vf, xs, None)(k)
      case Ann(ann, App(vf @ Var(f), xs @ Tup(_))) if ctx.fnCtx.contains(f) || ctx.nameCtx.get(f).fold(false)(x => ctx.fnCtx.contains(x.str)) =>
        buildLetCall(vf, xs, Some(ann))(k)
      case App(f, xs @ Tup(_)) =>
        buildResultFromTerm(f) {
          case Result(Ref(f) :: Nil) => buildResultFromTerm(xs) {
            case Result(args) =>
              val v = fresh.make
              // LetApply(List(v), f, args, v |> ref |> sresult |> k).attachTag(tag)
              LetMethodCall(List(v), ClassRef(R("Callable")), Name("apply" + args.length), (Ref(f): TrivialExpr) :: args, v |> ref |> sresult |> k).attachTag(tag)
            case node @ _ => node |> unexpectedNode
          }
          case node @ _ => node |> unexpectedNode
      }

      case Ann(ann @ Var(name), recv) =>
        if name === "tailcall" then
          raise(ErrorReport(List(msg"@tailcall may only be used to annotate function calls" -> ann.toLoc), true, Diagnostic.Compilation))
        else if name === "tailrec" then
          raise(ErrorReport(List(msg"@tailrec may only be used to annotate functions" -> ann.toLoc), true, Diagnostic.Compilation))

        buildResultFromTerm(recv)(k)
      case Let(false, Var(name), rhs, body) => 
        buildBinding(name, rhs, body)(k)

      case If(IfThen(cond, tru), Some(fls)) => 
        buildResultFromTerm(cond) {
          case Result(Ref(cond) :: Nil) => 
            if (!ctx.classCtx.contains("True") || !ctx.classCtx.contains("False"))
              throw IRError("True or False class not found, unable to use 'if then else'")
            val jp = fresh.make("j")
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = Defn(
              fnUid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              jpbody,
              false,
              None
            )
            ctx.jpAcc.addOne(jpdef)
            val tru2 = buildResultFromTerm(tru) {
              case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
              case node @ _ => node |> unexpectedNode
            }
            val fls2 = buildResultFromTerm(fls) {
              case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
              case node @ _ => node |> unexpectedNode
            }
            Case(cond, Ls(
              (Pat.Class(ClassRef(Right("True"))), tru2),
              (Pat.Class(ClassRef(Right("False"))), fls2)), None).attachTag(tag)
          case node @ _ => node |> unexpectedNode
        }
        
      case If(IfOpApp(lhs, Var("is"), IfBlock(lines)), N)
        => buildResultFromTerm(lhs) {
          case Result(Ref(scrut) :: Nil) =>
            val jp = fresh.make("j")
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = Defn(
              fnUid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              jpbody,
              false,
              None,
            )
            ctx.jpAcc.addOne(jpdef)
            var defaultCase: Opt[Node] = None
            val cases: Ls[(Pat, Node)] = lines flatMap {
              case L(IfThen(App(Var(ctor), params: Tup), rhs)) =>
                S(Pat.Class(ClassRef(Right(ctor))) -> {
                  // need this because we have built terms (selections in case arms) containing names that are not in the original term
                  given Ctx = ctx.copy(nameCtx = ctx.nameCtx + (scrut.str -> scrut))
                  buildResultFromTerm(
                    bindingPatternVariables(scrut.str, params, ctx.classCtx(ctor), rhs)) {
                      case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
                      case node @ _ => node |> unexpectedNode
                    }
                })
              case L(IfThen(lit @ IntLit(_), rhs)) =>
                S(Pat.Lit(lit) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
                  case node @ _ => node |> unexpectedNode
                })
              case L(IfThen(Var("_"), rhs)) =>
                defaultCase = Some(buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
                  case node @ _ => node |> unexpectedNode
                })
                N
              case L(IfThen(Var(ctor), rhs)) =>
                S(Pat.Class(ClassRef(Right(ctor))) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
                  case node @ _ => node |> unexpectedNode
                })
              case _ => throw IRError(s"not supported UCS")
            }
            Case(scrut, cases, defaultCase).attachTag(tag)
          case node @ _ => node |> unexpectedNode
        }

      case Bra(false, tm) => buildResultFromTerm(tm)(k)

      case Blk(stmts) =>
        val (nfds, ntds, terms) = collectInfo(stmts)
        val (ctx2, nfds2, ntds2) = renameToBeLifted(nfds, ntds)
        val ctx3 = initContextForStatementsFrom(
          nfds2, ntds2, terms, scanNamesInThisScope(stmts)
        )(using ctx2)

        ctx.lcAcc.addAll(ntds2)
        ctx.defAcc.addAll(nfds2)

        buildResultFromTerms(using ctx3)(terms)(k)

      case tup: Tup => buildResultFromTup(tup)(k)

      case term => term |> unexpectedTerm
    
    res

  private def buildResultFromTerms(using ctx: Ctx)(tms: Ls[Statement])(k: Node => Node): Node =
    tms match
      case Nil => throw IRError("empty term list")
      case NuFunDef(S(false), Var(name), _, _, Left(tm)) :: xs =>
        xs match
          case Nil => throw IRError("unsupported NuFunDef at tail position")
          case _ => buildResultFromTerm(tm) {
            case Result((r: Ref) :: Nil) =>
              given Ctx = ctx.copy(nameCtx = ctx.nameCtx + (name -> r.name))
              buildResultFromTerms(xs)(k)
            case Result((lit: Literal) :: Nil) =>
              val v = fresh.make
              given Ctx = ctx.copy(nameCtx = ctx.nameCtx + (name -> v))
              LetExpr(v,
                lit,
                buildResultFromTerms(xs)(k)).attachTag(tag)
            case node @ _ => node |> unexpectedNode
          }
      case x :: Nil => buildResultFromTerm(x)(k)
      case x :: xs => buildResultFromTerm(x) {
        case _ => buildResultFromTerms(xs)(k)
      }

  private def getTupleFields(tup: Tup) = tup.fields.map {
    case N -> Fld(FldFlags.empty, Var(name)) => name
    case S(Var(name)) -> Fld(_, ty) => name
    case _ => throw IRError("unsupported field")
  }

  private def buildDefFromMethod(using ctx: Ctx)(fields: List[Str], nfd: Statement): Defn = nfd match
    case nfd @ NuFunDef(_, Var(name), None, Nil, L(Lam(xs @ Tup(_), body))) =>
      val defnInfoPartial = getDefnInfoPartial(ctx.fnCtx.keySet ++ ctx.classCtx.keySet ++ fields, ctx)(nfd).get
      val params = defnInfoPartial.params
      val names = params map (fresh.make(_))
      val ctx2 =  ctxJoin(ctx, defnInfoPartial.ctx)
      given Ctx = ctx2.copy(nameCtx = ctx2.nameCtx ++ (params zip names))
      Defn(
        fnUid.make,
        name,
        params = names,
        resultNum = 1,
        body = buildResultFromTerm(body) { x => x },
        isTailRec = false,
        loc = nfd.getLoc,
      )
    case fd @ _ => throw IRError("unsupported NuFunDef " + fd.toString)

  private def buildDefFromNuFunDef(using ctx: Ctx)(nfd: Statement): Defn = nfd match
    case nfd @ NuFunDef(_, Var(name), None, Nil, L(Lam(xs @ Tup(_), body))) =>
      val defnInfoPartial = getDefnInfoPartial(ctx.fnCtx.keySet ++ ctx.classCtx.keySet, ctx)(nfd).get
      val params = defnInfoPartial.params
      val names = params map (fresh.make(_))
      val ctx2 =  ctxJoin(ctx, defnInfoPartial.ctx)
      given Ctx = ctx2.copy(nameCtx = ctx2.nameCtx ++ (params zip names))
      val trAnn = nfd.annotations.find { 
        case Var("tailrec") => true
        case ann @ Var("tailcall") =>
          raise(ErrorReport(List(msg"@tailcall is for annotating function calls; try @tailrec instead" -> ann.toLoc), true, Diagnostic.Compilation))
          false
        case _ => false }
      Defn(
        fnUid.make,
        name,
        params = names,
        resultNum = 1,
        buildResultFromTerm(body) { x => x },
        trAnn.isDefined,
        trAnn.flatMap(_.toLoc)
      )
    case fd @ _ => throw IRError("unsupported NuFunDef " + fd.toString)

  private def buildClassInfo(using ctx: Ctx)(ntd: Statement): ClassInfo = ntd match
    case ntd @ NuTypeDef(Cls | Mod, TypeName(name), _, params, N, _, parents, N, N, TypingUnit(methods)) =>
      val clsInfoPartial = getClassInfoPartial(ctx.classCtx.keySet ++ ctx.fnCtx.keySet, ctx)(ntd)
      val cls = ClassInfo(classUid.make, name, clsInfoPartial.fields)
      val ctx2 = ctxJoin(ctx, clsInfoPartial.ctx)
      given Ctx = ctx2.copy(
        nameCtx = ctx2.nameCtx ++ clsInfoPartial.fields.map(x => x -> Name(x)),
        classCtx = ctx2.classCtx + (name -> clsInfoPartial)
      )
      def resolveParentName(parent: Term): String = parent match {
        case Var(name) if name.isCapitalized => name
        case TyApp(lhs, _) => resolveParentName(lhs)
        case App(lhs, _) => resolveParentName(lhs)
        case _ => throw IRError("unsupported parent")
      }
      cls.parents = parents.map(resolveParentName).toSet
      cls.methods = methods.map {
        case x: NuFunDef => x.name -> buildDefFromMethod(clsInfoPartial.fields, x)
        case x @ _ => throw IRError(f"unsupported method $x")
      }.toMap
      cls
    case x @ _ => throw IRError(f"unsupported NuTypeDef $x")


  private def getDefnInfoPartial(names: Set[Str], ctx: Ctx)(nfd: NuFunDef): Opt[DefnInfoPartial] = nfd match
    case NuFunDef(_, Var(name), _, _, Left(Lam(Var(x), _))) => 
      val originalFvs = freeVariables(nfd)._2
      val fvs = (originalFvs -- builtin -- ops -- names).toList
      val params = x :: fvs
      val dip = DefnInfoPartial(name, params)
      dip.freeVars = fvs
      dip.ctx = ctx
      S(dip)
    case NuFunDef(_, Var(name), _, _, Left(Lam(tp @ Tup(fields), _))) =>
      val originalFvs = freeVariables(nfd)._2
      val fvs = (originalFvs -- builtin -- ops -- names).toList
      val params = getTupleFields(tp) ++ fvs
      val dip = DefnInfoPartial(name, params)
      dip.freeVars = fvs
      dip.ctx = ctx
      S(dip)
    case NuFunDef(_, Var(name), _, _, _) => N


  private def getClassInfoPartial(names: Set[Str], ctx: Ctx)(ntd: NuTypeDef): ClassInfoPartial = ntd match
    case ntd @ NuTypeDef(Cls | Mod, TypeName(name), _, params, N, _, parents, N, N, TypingUnit(other)) =>
      val originalFvs = freeVariables(ntd)._2
      log(s"getClassInfoPartial $name")
      log(originalFvs)
      log(names)
      val fvs = (originalFvs -- builtin -- ops -- names).toList
      val fields = params.fold(fvs)(xs => getTupleFields(xs) ++ fvs)
      val methods = other.map {
        case x: NuFunDef => x.name
        case x @ _ => throw IRError(f"unsupported method $x")
      }
      val cls = ClassInfoPartial(name, fields, methods.toSet)
      cls.freeVars = fvs
      cls.ctx = ctx
      cls
    case x @ _ => throw IRError(f"unsupported NuTypeDef $x")
  
  private def collectInfo(stmts: Ls[Statement]): (Ls[NuFunDef], Ls[NuTypeDef], Ls[Statement]) =
    var nfds = ListBuffer.empty[NuFunDef]
    var ntds = ListBuffer.empty[NuTypeDef]
    var terms = ListBuffer.empty[Statement]
    stmts.foreach {
      case tm @ NuFunDef(S(false), Var(_), _, _, Left(_)) =>
        terms.addOne(tm)
      case nfd: NuFunDef => nfds.addOne(nfd)
      case ntd: NuTypeDef => ntds.addOne(ntd)
      case tm: Term => terms.addOne(tm)
      case _ => throw IRError("unsupported statement")
    }
    (nfds.toList, ntds.toList, terms.toList)

  private def makeNameMap(str: IterableOnce[Str]) = str.iterator.map(x => (x, Name(x))).toMap

  private def scanNamesInThisScope(stmt: Ls[Statement]): Set[Str] =
    val names = stmt flatMap {
      case NuTypeDef(_, TypeName(name), _, _, _, _, _, _, _, _) => S(name)
      case NuFunDef(_, Var(name), _, _, _) => S(name)
      case _ => Nil
    }
    names.toSet
  
  private def renameToBeLifted(nfds: Ls[NuFunDef], ntds: Ls[NuTypeDef])(using ctx: Ctx): (Ctx, Ls[NuFunDef], Ls[NuTypeDef]) =
    val oldFnNames = scanNamesInThisScope(nfds).toList
    val oldTyNames = scanNamesInThisScope(ntds).toList
    // TODO: currently, rename cause bugs
    //val newFnNames = oldFnNames.map(x => fresh.make(x))
    //val newTyNames = oldTyNames.map(x => if x.startsWith("Lambda$") then Name(x) else fresh.make(x))
    val newFnNames = oldFnNames.map(Name(_))
    val newTyNames = oldTyNames.map(Name(_))
    val nameCtx = oldFnNames.zip(newFnNames).toMap
    val tyNameCtx = oldTyNames.zip(newTyNames).toMap
    val nfds2 = nfds.map(x => x.copy(nme = Var(nameCtx(x.name).str))(x.declareLoc, x.virtualLoc, x.mutLoc, x.signature, x.outer, x.genField, x.annotations))
    val ntds2 = ntds.map(x => x.copy(nme = TypeName(tyNameCtx(x.name).str))(x.declareLoc, x.abstractLoc, x.annotations))

    (ctx.copy(nameCtx = ctx.nameCtx ++ nameCtx, tyNameCtx = ctx.tyNameCtx ++ tyNameCtx), nfds2, ntds2)

  private def initContextForStatementsFrom(nfds: Ls[NuFunDef], ntds: Ls[NuTypeDef], terms: Ls[Statement], excluded: Set[Str])(using ctx: Ctx): Ctx =
    // they are in the same mutual group or higher group, mustn't capture them
    val excludedNames = excluded ++ scanNamesInThisScope(nfds) ++ scanNamesInThisScope(ntds) ++ ctx.fnCtx.keySet ++ ctx.classCtx.keySet
    val partialDefnInfo = nfds flatMap getDefnInfoPartial(excludedNames, ctx)
    val partialClassInfo = ntds map getClassInfoPartial(excludedNames, ctx)
    val fnNames = partialDefnInfo.map(_.name)
    val fnCtx = fnNames.zip(partialDefnInfo).toMap
    val nameCtx = makeNameMap(builtin) ++ makeNameMap(fnNames) ++ makeNameMap(ops)
    val tyNames = partialClassInfo.map(_.name)
    val tyNameCtx = makeNameMap(tyNames)
    val classCtx = tyNames.zip(partialClassInfo).toMap

    ctx.copy(
      tyNameCtx = ctx.tyNameCtx ++ tyNameCtx,
      nameCtx = ctx.nameCtx ++ nameCtx,
      classCtx = ctx.classCtx ++ classCtx,
      fnCtx = ctx.fnCtx ++ fnCtx,
    )

  private def initContextForStatements(nfds: Ls[NuFunDef], ntds: Ls[NuTypeDef], terms: Ls[Statement]): Ctx =
    val ctx = Ctx(
      nameCtx = Map.empty,
      tyNameCtx = Map.empty,
      classCtx = Map.empty,
      fnCtx = Map.empty,
      opCtx = ops,
      jpAcc = ListBuffer.empty,
      defAcc = ListBuffer.empty,
      lcAcc = ListBuffer.empty,
    )
    initContextForStatementsFrom(nfds, ntds, terms, Set.empty)(using ctx)

  def getHiddenNames(prelude: TypingUnit): Set[Str] =
    def resolveTypeName(x: Term): Str = x match
      case Var(name) => name
      case TyApp(lhs, _) => resolveTypeName(lhs)
      case App(lhs, _) => resolveTypeName(lhs)
      case _ => throw IRError("unsupported type name")
    val hidden = prelude.rawEntities.flatMap {
      case NuFunDef(_, Var(name), _, _, _) => Nil
      case NuTypeDef(_, TypeName(name), _, params, _, _, _, _, _, _) if name == "HiddenTheseEntities" =>
        params.fold{Nil}{
          x => x.fields.flatMap {
            case S(Var(name)) -> Fld(FldFlags.empty, ty) => resolveTypeName(ty) :: Nil
            case _ => Nil
          }
        }
      case NuTypeDef(_, TypeName(name), _, _, _, _, _, _, _, _) => Nil
      case _ => Nil
    }
    hidden.toSet

  def buildGraph(unit: TypingUnit, prelude: TypingUnit, addPrelude: Boolean = true): Program =
    val unit2 = if addPrelude then TypingUnit(prelude.rawEntities ++ unit.rawEntities) else unit
    val hiddenNames = getHiddenNames(unit2)
    val (nfds, ntds, terms) = collectInfo(unit2.rawEntities)
    var ctx = initContextForStatements(nfds, ntds, terms)

    val definitions = ListBuffer.empty[Defn]
    val classes = ListBuffer.empty[ClassInfo]

    var first = true

    var curNfds = nfds
    var curNtds = ntds
    val main = buildResultFromTerm(using ctx)(Blk(terms)){ k => k }
    while first || ctx.hasLifted do
      first = false
      ctx.jpAcc.clear()
      ctx.defAcc.clear()
      ctx.lcAcc.clear()
      definitions.addAll(curNfds.map(buildDefFromNuFunDef(using ctx)))
      definitions.addAll(ctx.jpAcc)
      classes.addAll(curNtds.map(buildClassInfo(using ctx)))
      curNfds = ctx.defAcc.toList
      curNtds = ctx.lcAcc.toList
      ctx = initContextForStatementsFrom(curNfds, curNtds, Nil, Set.empty)(using ctx)

    val clsInfo = classes.toSet
    val defs = definitions.toSet

    resolveRef(main, defs, clsInfo, true)
    validate(main, defs, clsInfo)
    
    Program(clsInfo, defs, main)
