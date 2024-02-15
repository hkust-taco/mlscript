package mlscript.compiler.ir

import mlscript.compiler.optimizer.FreeVarAnalysis
import mlscript.utils.shorthands._
import mlscript.utils._
import mlscript._
import collection.mutable.ListBuffer

final val ops = Set("+", "-", "*", "/", ">", "<", ">=", "<=", "!=", "==")

final class IRBuilder(fresh: Fresh, fn_uid: FreshInt, class_uid: FreshInt, tag: FreshInt):
  import GONode._
  import GOExpr._
  
  private type NameCtx = Map[Str, Name]
  private type ClassCtx = Map[Str, ClassInfo]
  private type FieldCtx = Map[Str, (Str, ClassInfo)]
  private type FnCtx = Set[Str]
  private type OpCtx = Set[Str]
  
  private final case class Ctx(
    val name_ctx: NameCtx = Map.empty,
    val class_ctx: ClassCtx = Map.empty,
    val field_ctx: FieldCtx = Map.empty,
    val fn_ctx: FnCtx = Set.empty,
    val op_ctx: OpCtx = Set.empty,
    var jp_acc: ListBuffer[GODef],
  )

  private def ref(x: Name) = Ref(x)
  private def result(x: Ls[TrivialExpr]) = Result(x).attach_tag(tag)
  private def sresult(x: TrivialExpr) = Result(Ls(x)).attach_tag(tag)
  private def unexpected_node(x: GONode) = throw IRError(s"unsupported node $x")
  private def unexpected_term(x: Term) = throw IRError(s"unsupported term $x")

  private def buildBinding(using ctx: Ctx)(name: Str, e: Term, body: Term)(k: GONode => GONode): GONode =
    buildResultFromTerm(e) {
      case Result((r: Ref) :: Nil) =>
        given Ctx = ctx.copy(name_ctx = ctx.name_ctx + (name -> r.name))
        buildResultFromTerm(body)(k)
      case Result((lit: Literal) :: Nil) =>
        val v = fresh.make
        given Ctx = ctx.copy(name_ctx = ctx.name_ctx + (name -> v))
        LetExpr(v,
          lit,
          buildResultFromTerm(body)(k)).attach_tag(tag)
      case node @ _ => node |> unexpected_node
    }
  
  private def buildResultFromTup(using ctx: Ctx)(tup: Tup)(k: GONode => GONode): GONode =
    tup match
      case Tup(N -> Fld(FldFlags.empty, x) :: xs) => buildResultFromTerm(x) {
        case Result(x :: Nil) =>
          buildResultFromTup(Tup(xs)) {
            case Result(xs) => x :: xs |> result |> k
            case node @ _ => node |> unexpected_node
          }
        case node @ _ => node |> unexpected_node
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
        Let(false, Var(param), Sel(Var(scrut), Var(field)), tm)
    }
    tm

  private def buildResultFromTerm(using ctx: Ctx)(tm: Term)(k: GONode => GONode): GONode =
    val res = tm match
      case lit: Lit => Literal(lit) |> sresult |> k
      case v @ Var(name) =>
        if (name.isCapitalized)
          val v = fresh.make
          LetExpr(v,
            CtorApp(ctx.class_ctx(name), Nil),
            v |> ref |> sresult |> k).attach_tag(tag)
        else
          ctx.name_ctx.get(name) match {
            case Some(x) => x |> ref |> sresult |> k
            case _ => throw IRError(s"unknown name $name in $ctx")
          }

      case Lam(Tup(fields), body) =>
        throw IRError("not supported: lambda")
      case App(
        App(Var(name), Tup((_ -> Fld(_, e1)) :: Nil)), 
        Tup((_ -> Fld(_, e2)) :: Nil)) if ctx.op_ctx.contains(name) =>
        buildResultFromTerm(e1) {
          case Result(v1 :: Nil) =>
            buildResultFromTerm(e2) {
              case Result(v2 :: Nil) =>
                val v = fresh.make
                LetExpr(v,
                  BasicOp(name, List(v1, v2)),
                  v |> ref |> sresult |> k).attach_tag(tag)
              case node @ _ => node |> unexpected_node
            }
          case node @ _ => node |> unexpected_node
        }
        
      case App(Var(name), xs @ Tup(_)) if name.isCapitalized =>
        buildResultFromTerm(xs) {
          case Result(args) => 
            val v = fresh.make
            LetExpr(v,
              CtorApp(ctx.class_ctx(name), args),
              v |> ref |> sresult |> k).attach_tag(tag)
          case node @ _ => node |> unexpected_node
        }

      case App(f, xs @ Tup(_)) =>
        buildResultFromTerm(f) {
        case Result(Ref(f) :: Nil) if ctx.fn_ctx.contains(f.str) => buildResultFromTerm(xs) {
          case Result(args) =>
            val v = fresh.make
            LetCall(List(v), GODefRef(Right(f.str)), args, v |> ref |> sresult |> k).attach_tag(tag)
          case node @ _ => node |> unexpected_node
        }
        case Result(Ref(f) :: Nil) => buildResultFromTerm(xs) {
          case Result(args) =>
            throw IRError(s"not supported: apply")
          case node @ _ => node |> unexpected_node
        }
        case node @ _ => node |> unexpected_node
      }

      case Let(false, Var(name), rhs, body) => 
        buildBinding(name, rhs, body)(k)

      case If(IfThen(cond, tru), Some(fls)) => 
        buildResultFromTerm(cond) {
          case Result(Ref(cond) :: Nil) => 
            if (!ctx.class_ctx.contains("True") || !ctx.class_ctx.contains("False"))
              throw IRError("True or False class not found, unable to use 'if then else'")
            val jp = fresh make "j"
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = GODef(
              fn_uid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              specialized = None,
              jpbody
            )
            ctx.jp_acc.addOne(jpdef)
            val tru2 = buildResultFromTerm(tru) {
              case Result(xs) => Jump(GODefRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attach_tag(tag)
              case node @ _ => node |> unexpected_node
            }
            val fls2 = buildResultFromTerm(fls) {
              case Result(xs) => Jump(GODefRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attach_tag(tag)
              case node @ _ => node |> unexpected_node
            }
            Case(cond, Ls((ctx.class_ctx("True"), tru2), (ctx.class_ctx("False"), fls2))).attach_tag(tag)
          case node @ _ => node |> unexpected_node
        }
        
      case If(IfOpApp(lhs, Var("is"), IfBlock(lines)), N)
        if lines forall {
          case L(IfThen(App(Var(ctor), Tup((N -> Fld(FldFlags.empty, _: Var)) :: _)), _)) => ctor.isCapitalized
          case L(IfThen(Var(ctor), _)) => ctor.isCapitalized || ctor == "_"
          case _ => false
        }
        => buildResultFromTerm(lhs) {
          case Result(Ref(scrut) :: Nil) =>
            val jp = fresh make "j"
            val res = fresh.make
            val jpbody = res |> ref |> sresult |> k
            val fvs = FreeVarAnalysis(extended_scope = false).run_with(jpbody, Set(res.str)).toList
            val jpdef = GODef(
              fn_uid.make,
              jp.str,
              params = res :: fvs.map(x => Name(x)),
              resultNum = 1,
              specialized = None,
              jpbody,
            )
            ctx.jp_acc.addOne(jpdef)
            val cases: Ls[(ClassInfo, GONode)] = lines map {
              case L(IfThen(App(Var(ctor), params: Tup), rhs)) =>
                ctx.class_ctx(ctor) -> {
                  // need this because we have built terms (selections in case arms) containing names that are not in the original term
                  given Ctx = ctx.copy(name_ctx = ctx.name_ctx + (scrut.str -> scrut))
                  buildResultFromTerm(
                    bindingPatternVariables(scrut.str, params, ctx.class_ctx(ctor), rhs)) {
                      case Result(xs) => Jump(GODefRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attach_tag(tag)
                      case node @ _ => node |> unexpected_node
                    }
                }
              case L(IfThen(Var(ctor), rhs)) =>
                ctx.class_ctx(ctor) -> buildResultFromTerm(rhs) {
                  case Result(xs) => Jump(GODefRef(Right(jp.str)), xs ++ fvs.map(x => Ref(Name(x)))).attach_tag(tag)
                  case node @ _ => node |> unexpected_node
                }
              case _ => throw IRError(s"not supported UCS")
            }
            Case(scrut, cases).attach_tag(tag)
          case node @ _ => node |> unexpected_node
        }

      case Bra(false, tm) => buildResultFromTerm(tm)(k)

      case Blk((tm: Term) :: Nil) => buildResultFromTerm(tm)(k)
      
      case Blk((tm: Term) :: xs) => buildBinding("_", tm, Blk(xs))(k)

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: Nil) =>
        buildBinding(name, tm, Var(name))(k)

      case Blk(NuFunDef(S(false), Var(name), None, _, L(tm)) :: xs) =>
        buildBinding(name, tm, Blk(xs))(k)

      case Sel(tm @ Var(name), Var(fld)) =>
        buildResultFromTerm(tm) {
          case Result(Ref(res) :: Nil) =>
            val v = fresh.make
            val cls = ctx.field_ctx(fld)._2
            LetExpr(v,
              Select(res, cls, fld),
              v |> ref |> sresult |> k).attach_tag(tag)
          case node @ _ => node |> unexpected_node
        }

      case tup: Tup => buildResultFromTup(tup)(k)

      case term => term |> unexpected_term
    
    res
  
  private def buildDefFromNuFunDef(using ctx: Ctx)(nfd: Statement): GODef = nfd match
    case NuFunDef(_, Var(name), None, Nil, L(Lam(Tup(fields), body))) =>
      val strs = fields map {
          case N -> Fld(FldFlags.empty, Var(x)) => x
          case _ => throw IRError("unsupported field") 
        }
      val names = strs map (fresh.make(_))
      given Ctx = ctx.copy(name_ctx = ctx.name_ctx ++ (strs zip names))
      GODef(
        fn_uid.make,
        name,
        params = names,
        resultNum = 1,
        specialized = None,
        buildResultFromTerm(body) { x => x }
      )
    case _ => throw IRError("unsupported NuFunDef")
  
  private def buildClassInfo(ntd: Statement): ClassInfo = ntd match
    case NuTypeDef(Cls, TypeName(name), Nil, S(Tup(args)), N, N, Nil, N, N, TypingUnit(Nil)) =>
      ClassInfo(
        class_uid.make,
        name, 
        args map {
          case N -> Fld(FldFlags.empty, Var(name)) => name
          case _ => throw IRError("unsupported field")
        }
      )
    case NuTypeDef(Cls, TypeName(name), Nil, N, N, N, Nil, N, N, TypingUnit(Nil)) =>
      ClassInfo(
        class_uid.make,
        name,
        Ls(),
      )
    case x @ _ => throw IRError(f"unsupported NuTypeDef $x")

  private def checkDuplicateField(ctx: Set[Str], cls: ClassInfo): Set[Str] =
    val u = cls.fields.toSet intersect ctx
    if (u.nonEmpty) throw IRError(f"duplicate class field $u")
    cls.fields.toSet union ctx

  private def getDefinitionName(nfd: Statement): Str = nfd match
    case NuFunDef(_, Var(name), _, _, _) => name
    case _ => throw IRError("unsupported NuFunDef")

  def buildGraph(unit: TypingUnit): GOProgram = unit match
    case TypingUnit(entities) =>
      val grouped = entities groupBy {
        case ntd: NuTypeDef => 0
        case nfd: NuFunDef => 1
        case tm: Term => 2
        case _ => throw IRError("unsupported entity")
      }

      import scala.collection.mutable.{ HashSet => MutHSet }

      val cls = grouped.getOrElse(0, Nil).map(buildClassInfo)
      cls.foldLeft(Set.empty)(checkDuplicateField(_, _))

      val clsinfo = cls.toSet
      val defn_names = grouped.getOrElse(1, Nil).map(getDefinitionName)
      val class_ctx: ClassCtx = cls.map { case ClassInfo(_, name, _) => name }.zip(cls).toMap
      val field_ctx: FieldCtx = cls.flatMap { case ClassInfo(_, name, fields) => fields.map((_, (name, class_ctx(name)))) }.toMap
      val fn_ctx: FnCtx = defn_names.toSet
      var name_ctx: NameCtx = defn_names.zip(defn_names.map(Name(_))).toMap ++ ops.map { op => (op, Name(op)) }.toList

      val jp_acc = ListBuffer.empty[GODef]
      given Ctx = Ctx(
        name_ctx = name_ctx,
        class_ctx = class_ctx,
        field_ctx = field_ctx,
        fn_ctx = fn_ctx,
        op_ctx = ops,
        jp_acc = jp_acc,
      )

      var defs: Set[GODef] = grouped.getOrElse(1, Nil).map(buildDefFromNuFunDef).toSet
      val terms: Ls[Term] = grouped.getOrElse(2, Nil).map {
        case tm: Term => tm
        case _ => ??? /* unreachable */
      }

      val main = buildResultFromTerm (terms match {
        case x :: Nil => x
        case _ => throw IRError("only one term is allowed in the top level scope")
      }) { k => k }

      defs ++= jp_acc.toList

      

      
      relink(main, defs, true)
      validate(main, defs)
      
      GOProgram(clsinfo, defs, main)
