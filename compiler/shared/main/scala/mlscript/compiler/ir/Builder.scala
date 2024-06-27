package mlscript.compiler.ir

import mlscript.compiler.optimizer.FreeVarAnalysis
import mlscript.utils.shorthands._
import mlscript.utils._
import mlscript._
import collection.mutable.ListBuffer

final val ops = Set("+", "-", "*", "/", ">", "<", ">=", "<=", "!=", "==")
final val builtin = Set("builtin")

final class Builder(fresh: Fresh, fnUid: FreshInt, classUid: FreshInt, tag: FreshInt, verbose: Boolean = false):
  import Node._
  import Expr._
  
  private def log(x: Any) = if verbose then println(x)

  private type NameCtx = Map[Str, Name]
  private type ClassCtx = Map[Str, ClassInfo]
  private type FieldCtx = Map[Str, (Str, ClassInfo)]
  private type FnCtx = Map[Str, Int]
  private type OpCtx = Set[Str]
  
  private final case class Ctx(
    val nameCtx: NameCtx = Map.empty,
    val classCtx: ClassCtx = Map.empty,
    val fnCtx: FnCtx = Map.empty,
    val opCtx: OpCtx = Set.empty,
    var jpAcc: ListBuffer[Defn],
    var defAcc: ListBuffer[Defn],
    var lcAcc: ListBuffer[ClassInfo],
  )

  private def ref(x: Name) = Ref(x)
  private def result(x: Ls[TrivialExpr]) = Result(x).attachTag(tag)
  private def sresult(x: TrivialExpr) = Result(Ls(x)).attachTag(tag)
  private def unexpectedNode(x: Node) = throw IRError(s"unsupported node $x")
  private def unexpectedTerm(x: Term) = throw IRError(s"unsupported term $x")

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
      
  private def bindingPatternVariables(scrut: Str, tup: Tup, cls: ClassInfo, rhs: Term): Term =
    val params = tup.fields.map {
      case N -> Fld(FldFlags.empty, Var(name)) => name
      case _ => throw IRError("unsupported field")
    }
    val fields = cls.fields
    val tm = params.zip(fields).foldLeft(rhs) {
      case (tm, (param, field)) => 
        Let(false, Var(param), App(Sel(Var(cls.ident), Var(field)), Tup(Ls(N -> Fld(FldFlags.empty, Var(scrut))))), tm)
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

  private def freeVariables(stmt: Statement): (Set[Str], Set[Str]) = stmt match
    case DataDefn(body) => throw IRError("unsupported DataDefn")
    case DatatypeDefn(head, body) => throw IRError("unsupported DatatypeDefn")
    case LetS(isRec, pat, rhs) => throw IRError("unsupported LetS")
    case ntd: NuTypeDef => 
      val fvs = freeVariables(ntd.body) -- ntd.params.fold(Set.empty)(freeVariables)
      (Set.empty, fvs)
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

  private def freeVariables(tm: Term): Set[Str] =tm match
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
    case LetGroup(bindings) => throw IRError("unsupported LetGroup")
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
    case TyApp(lhs, targs) => throw IRError("unsupported TyApp")
    case Unquoted(body) => throw IRError("unsupported Unquoted")
    case Where(body, where) => throw IRError("unsupported Where")
    case While(cond, body) => freeVariables(cond) ++ freeVariables(body)
    case With(trm, fields) => freeVariables(trm) ++ freeVariables(fields: Term)
    case Var(name) => Set(name)
    case CharLit(value) => Set.empty
    case DecLit(value) => Set.empty
    case IntLit(value) => Set.empty
    case StrLit(value) => Set.empty
    case UnitLit(undefinedOrNull) => Set.empty

  private def buildResultFromTerm(using ctx: Ctx)(tm: Term)(k: Node => Node): Node =
    val res = tm match
      case lit: Lit => Literal(lit) |> sresult |> k
      case v @ Var(name) =>
        if (name.isCapitalized)
          val v = fresh.make
          LetExpr(v,
            CtorApp(ctx.classCtx(name), Nil),
            v |> ref |> sresult |> k).attachTag(tag)
        else if (ctx.fnCtx.contains(name))
          val arity = ctx.fnCtx(name)
          val range = 0 until arity
          val xs = range.map(_ => fresh.make.str).toList
          val paramsAndArgs = Tup(xs.map(x => N -> Fld(FldFlags.empty, Var(x))))
          val lam = Lam(paramsAndArgs, App(Var(name), paramsAndArgs))
          buildResultFromTerm(lam)(k)
        else
          ctx.nameCtx.get(name) match {
            case Some(x) => x |> ref |> sresult |> k
            case None => throw IRError(s"unknown name $name in $ctx")
          }
      case lam @ Lam(Tup(fields), body) =>
        val tmp = fresh.make
        val lambdaName = fresh.make("Lambda")
        var fvs = freeVariables(lam)
        fvs --= ctx.opCtx
        fvs --= ctx.fnCtx.keySet
        val fvsList = fvs.toList
        val paramsTup = Tup(fvsList.map{ x => N -> Fld(FldFlags.empty, Var(x)) })
        val newParams = if fvs.isEmpty then N else S(paramsTup)
        val result = (if fvs.isEmpty then Var(lambdaName.str) else App(Var(lambdaName.str), paramsTup))
        val localCls = Blk(
          NuTypeDef(Cls, TypeName(lambdaName.str), Nil, newParams, N, N, Ls(Var("Callable")), N, N, TypingUnit(
            NuFunDef(N, Var(s"apply${fields.size}"), None, Nil, L(Lam(Tup(fields), body)))(tm.getLoc, N, N, N, N, false, Nil) :: Nil
          ))(tm.getLoc, tm.getLoc, Nil)
          :: result :: Nil)
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
      case App(Var(name), xs @ Tup(_)) if name.isCapitalized || ctx.opCtx.contains(name) =>
        if name.isCapitalized then
          buildResultFromTerm(xs) {
            case Result(args) => 
              val v = fresh.make
              LetExpr(v,
                CtorApp(ctx.classCtx(name), args),
                v |> ref |> sresult |> k).attachTag(tag)
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
            val v = fresh.make
            val cls = ctx.classCtx(clsName)
            val isField = cls.fields.contains(fld)
            if isField then
              LetExpr(v, Select(name, cls, fld),
                v |> ref |> sresult |> k).attachTag(tag)
            else
              if cls.methods.contains(fld) then
                LetMethodCall(Ls(v), cls, Name(fld), xs, v |> ref |> sresult |> k).attachTag(tag)
              else
                throw IRError(s"unknown field or method $fld in $cls")
          case node @ _ => node |> unexpectedNode
        }
      case App(Var(f), xs @ Tup(_)) if ctx.fnCtx.contains(f) =>
        buildResultFromTerm(xs) {
            case Result(args) =>
              val v = fresh.make
              LetCall(List(v), DefnRef(Right(f)), args, v |> ref |> sresult |> k).attachTag(tag)
            case node @ _ => node |> unexpectedNode
        }
      case App(f, xs @ Tup(_)) =>
        buildResultFromTerm(f) {
          case Result(Ref(f) :: Nil) => buildResultFromTerm(xs) {
            case Result(args) =>
              val v = fresh.make
              LetApply(List(v), f, args, v |> ref |> sresult |> k).attachTag(tag)
            case node @ _ => node |> unexpectedNode
          }
          case node @ _ => node |> unexpectedNode
      }

      case Let(false, Var(name), rhs, body) => 
        buildBinding(name, rhs, body)(k)

      case If(IfThen(cond, tru), Some(fls)) => 
        buildResultFromTerm(cond) {
          case Result(Ref(cond) :: Nil) => 
            if (!ctx.classCtx.contains("True") || !ctx.classCtx.contains("False"))
              throw IRError("True or False class not found, unable to use 'if then else'")
            val jp = fresh make "j"
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = Defn(
              fnUid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              specialized = None,
              jpbody
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
              (Pat.Class(ctx.classCtx("True")), tru2),
              (Pat.Class(ctx.classCtx("False")), fls2)), None).attachTag(tag)
          case node @ _ => node |> unexpectedNode
        }
        
      case If(IfOpApp(lhs, Var("is"), IfBlock(lines)), N)
        => buildResultFromTerm(lhs) {
          case Result(Ref(scrut) :: Nil) =>
            val jp = fresh make "j"
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = Defn(
              fnUid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              specialized = None,
              jpbody,
            )
            ctx.jpAcc.addOne(jpdef)
            var defaultCase: Opt[Node] = None
            val cases: Ls[(Pat, Node)] = lines flatMap {
              case L(IfThen(App(Var(ctor), params: Tup), rhs)) =>
                S(Pat.Class(ctx.classCtx(ctor)) -> {
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
              case L(IfThen(lit @ CharLit(_), rhs)) =>
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
                S(Pat.Class(ctx.classCtx(ctor)) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(DefnRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attachTag(tag)
                  case node @ _ => node |> unexpectedNode
                })
              case _ => throw IRError(s"not supported UCS")
            }
            Case(scrut, cases, defaultCase).attachTag(tag)
          case node @ _ => node |> unexpectedNode
        }

      case Bra(false, tm) => buildResultFromTerm(tm)(k)

      case Blk((tm: Term) :: Nil) => buildResultFromTerm(tm)(k)
      
      case Blk((tm: Term) :: xs) => buildBinding("_", tm, Blk(xs))(k)

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: Nil) =>
        throw IRError("unsupported let at tail position")

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: xs) =>
        buildBinding(name, tm, Blk(xs))(k)

      case Blk(NuFunDef(S(true) | N, Var(name), None, _, L(tm)) :: Nil) =>
        throw IRError("unsupported recursive definition at tail position")

      case Blk((nfd @ NuFunDef(N, Var(name), None, _, L(tm))) :: xs) =>
        val defn = buildDefFromNuFunDef(nfd)
        ctx.defAcc.addOne(defn)
        val ctx2 = ctx.copy(fnCtx = ctx.fnCtx + (name -> defn.resultNum))
        buildResultFromTerm(using ctx)(Blk(xs))(k)

      case Blk((cls @ NuTypeDef(Cls | Mod, name, Nil, params, N, N, parents, N, N, body)) :: xs) =>
        val classInfo = buildClassInfo(cls)
        ctx.lcAcc.addOne(classInfo)
        val ctx2 = ctx.copy(classCtx = ctx.classCtx + (name.name -> classInfo), nameCtx = ctx.nameCtx + (name.name -> Name(name.name)))
        buildResultFromTerm(using ctx2)(Blk(xs))(k)

      case tup: Tup => buildResultFromTup(tup)(k)

      case term => term |> unexpectedTerm
    
    res

  private def buildDefFromNuFunDef(using ctx: Ctx)(nfd: Statement): Defn = nfd match
    case NuFunDef(_, Var(name), None, Nil, L(Lam(Tup(fields), body))) =>
      val strs = fields map {
          case N -> Fld(FldFlags.empty, Var(x)) => x
          case f @ _ => throw IRError(s"unsupported field $f") 
        }
      val names = strs map (fresh.make(_))
      given Ctx = ctx.copy(nameCtx = ctx.nameCtx ++ (strs zip names))
      Defn(
        fnUid.make,
        name,
        params = names,
        resultNum = 1,
        specialized = None,
        buildResultFromTerm(body) { x => x }
      )
    case fd @ _ => throw IRError("unsupported NuFunDef " + fd.toString())
  
  private def buildClassInfo(using ctx: Ctx)(ntd: Statement): ClassInfo = ntd match
    case NuTypeDef(Cls | Mod, TypeName(name), Nil, params, N, _, parents, N, N, TypingUnit(methods)) =>
      val paramsList = params.fold(Ls()) {
        case Tup(xs) => 
          xs map {
            case N -> Fld(FldFlags.empty, Var(name)) => name
            case S(Var(name)) -> Fld(_, ty) => name
            case x @ _ => throw IRError(s"unsupported field $x")
          }
      }
      val cls = ClassInfo(
        classUid.make,
        name,
        paramsList,
      )
      cls.parents = parents.map { 
        case Var(name) if name.isCapitalized =>
          name
        case _ => throw IRError("unsupported parent")
      }.toSet
      given Ctx = ctx.copy(nameCtx = ctx.nameCtx ++ paramsList.map(x => x -> Name(x)), classCtx = ctx.classCtx + (name -> cls))
      cls.methods = methods.map {
        case x: NuFunDef => x.name -> buildDefFromNuFunDef(x)
        case x @ _ => throw IRError(f"unsupported method $x")
      }.toMap
      cls
    case x @ _ => throw IRError(f"unsupported NuTypeDef $x")


  private def getDefnResultsArity(nfd: Statement): (Str, Int) = nfd match
    case NuFunDef(_, Var(name), _, _, Left(Lam(Var(_), _))) => (name, 1)
    case NuFunDef(_, Var(name), _, _, Left(Lam(Tup(fields), _))) => (name, fields.length)
    case NuFunDef(_, Var(name), _, _, _) => (name, 0)
    case _ => throw IRError("unsupported NuFunDef")

  private def collectInfo(stmts: Ls[Statement]): (Ls[NuFunDef], Ls[NuTypeDef], Ls[Term]) =
    var nfds = ListBuffer.empty[NuFunDef]
    var ntds = ListBuffer.empty[NuTypeDef]
    var terms = ListBuffer.empty[Term]
    stmts.foreach {
      case nfd: NuFunDef => nfds = nfds :+ nfd
      case ntd: NuTypeDef => ntds = ntds :+ ntd
      case tm: Term => terms = terms :+ tm
      case _ => throw IRError("unsupported statement")
    }
    (nfds.toList, ntds.toList, terms.toList)

  
  private def makeNameMap(str: IterableOnce[Str]) = str.iterator.map(x => (x, Name(x))).toMap

  private def initContextForStatements(stmts: Ls[Statement]): Ctx =
    val (nfds, ntds, terms) = collectInfo(stmts)
    val ra = nfds.map(getDefnResultsArity)
    val fnCtx = ra.toMap
    val fnNames = ra.keys.toList
    val nameCtx = makeNameMap(builtin) ++ makeNameMap(fnNames) ++ makeNameMap(ops)



    ???

  def buildGraph(unit: TypingUnit, addPrelude: Boolean = true): Program = 
    val unit2 =  if addPrelude then
      TypingUnit(
        NuTypeDef(Mod,TypeName("True"),List(),None,None,None,List(),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("False"),List(),None,None,None,List(),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("Callable"),List(),None,None,None,List(),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("List"),List(),None,None,None,List(),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Cls,TypeName("Cons"),List(),Some(Tup(List((None,Fld(FldFlags.empty,Var("h"))), (None,Fld(FldFlags.empty,Var("t")))))),None,None,List(Var("List")),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("Nil"),List(),None,None,None,List(Var("List")),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("Option"),List(),None,None,None,List(),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Cls,TypeName("Some"),List(),Some(Tup(List((None,Fld(FldFlags.empty,Var("x")))))),None,None,List(Var("Option")),None,None,TypingUnit(List()))(N, N, Nil) ::
        NuTypeDef(Mod,TypeName("None"),List(),None,None,None,List(Var("Option")),None,None,TypingUnit(List()))(N, N, Nil) ::
        unit.rawEntities
      )
      else unit
    unit2 match
    case TypingUnit(entities) =>
      val grouped = entities groupBy {
        case ntd: NuTypeDef => 0
        case nfd: NuFunDef => 1
        case tm: Term => 2
        case _ => throw IRError("unsupported entity")
      }

      import scala.collection.mutable.{ HashSet => MutHSet }
      
      val defns = grouped.getOrElse(1, Nil)
      val defn_info = defns.map(getDefnResultsArity)
      val fn_ctx: FnCtx = defn_info.toMap
      val defn_names = defn_info.map(_._1)
      var name_ctx: NameCtx = builtin.zip(builtin.map(Name(_))).toMap ++ defn_names.zip(defn_names.map(Name(_))).toMap ++ ops.map { op => (op, Name(op)) }.toList

      val jp_acc = ListBuffer.empty[Defn]
      val def_acc = ListBuffer.empty[Defn]
      val lc_acc = ListBuffer.empty[ClassInfo]
      var ctx = Ctx(
        nameCtx = name_ctx,
        classCtx = Map.empty,
        fnCtx = fn_ctx,
        opCtx = ops,
        jpAcc = jp_acc,
        defAcc = def_acc,
        lcAcc = lc_acc,
      )

      val cls = grouped.getOrElse(0, Nil).map(x => buildClassInfo(using ctx)(x))
      var clsinfo = cls.toSet
      val class_ctx: ClassCtx = cls.map { case ClassInfo(_, name, _) => name }.zip(cls).toMap

      ctx = Ctx(
        nameCtx = name_ctx,
        classCtx = class_ctx,
        fnCtx = fn_ctx,
        opCtx = ops,
        jpAcc = jp_acc,
        defAcc = def_acc,
        lcAcc = lc_acc,
      )

      given Ctx = ctx

      var defs: Set[Defn] = grouped.getOrElse(1, Nil).map(buildDefFromNuFunDef).toSet
      val terms: Ls[Term] = grouped.getOrElse(2, Nil).map {
        case tm: Term => tm
        case _ => ??? /* unreachable */
      }

      val main = buildResultFromTerm (terms match {
        case x :: Nil => x
        case _ => throw IRError("only exactly one term is allowed in the top level scope")
      }) { k => k }

      defs ++= jp_acc.toList
      defs ++= def_acc.toList
      clsinfo ++= lc_acc.toList

      resolveDefnRef(main, defs, true)
      validate(main, defs)
      
      Program(clsinfo, defs, main)
