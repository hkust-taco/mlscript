package memir

// every non-integer data access will be cloned and dropped when out of scope
// return doesn't involve data access so will not be dropped

def simpleCodeGen(expr: Expr)(implicit
    retName: String,
    vars: Map[String, IRType],
    layoutGen: LayoutGenerator
): List[CStmt] =
  def genVal(v: Val): CExpr = v match
    case Val.VarVal(v) =>
      val variable = CExpr.Var(v.name)
      if vars(v.name) == IRType.Int32 then variable
      else CExpr.Dup(variable)
    case Val.LitInt(v) => CExpr.IntConst(v)

  def genCase(
      obj: CExpr,
      p: Pattern,
      expr: Expr
  ): (CExpr, List[CStmt]) =
    val layout = layoutGen.layout(p.ty.fields)
    implicit val localVars =
      vars ++ Map.from(p.vars.map(_.name).zip(p.ty.fields))
    val init = p.vars.zipWithIndex
      .map((v, i) =>
        CStmt.Assignment(
          CExpr.Var(v.name),
          CExpr.Dup(CExpr.FieldAccess(obj, layout(i)))
        )
      )
    val body = simpleCodeGen(expr)
    val drops = p.vars
      .zip(p.ty.fields)
      .filter(_._2 != IRType.Int32)
      .map((v, _) => CStmt.Drop(CExpr.Var(v.name)))
    (CExpr.TypeMatch(obj, p.ty), init ++ body ++ drops)

  expr match
    case Expr.SimpleValue(v) =>
      List(CStmt.Assignment(CExpr.Var(retName), genVal(v)))
    case Expr.LetExpr(x, ty, let, expr) =>
      implicit val localVars = vars ++ Map((x.name, ty))
      val init = let match
        case LetCase.Simple(e) =>
          implicit val localRetName = x.name
          simpleCodeGen(e)
        case LetCase.FunApp(None, f, params) =>
          // maybe also handle constructors?
          val p = params.map(genVal)
          List(CStmt.Assignment(CExpr.Var(x.name), CExpr.Call(f, p)))
        case LetCase.FunApp(Some(obj), f, params) =>
          // get mangled function name
          val classid = obj match
            case Val.VarVal(v) =>
              vars.get(v.name) match
                case Some(IRType.Union(ty :: Nil)) => ty.id
                case _ => throw RuntimeException("should be unreachable...")
            case Val.LitInt(_) => 0 // we assume integers have classid 0
          val name = classid.toString ++ f
          List(
            CStmt.Assignment(
              CExpr.Var(x.name),
              CExpr.Call(name, genVal(obj) :: params.map(genVal))
            )
          )
      val body = simpleCodeGen(expr)
      val drop =
        if ty == IRType.Int32 then Nil else List(CStmt.Drop(CExpr.Var(x.name)))
      init ++ body ++ drop
    case Expr.MatchExpr(v, cases, default) =>
      val branches =
        cases.map((pattern, expr) => genCase(genVal(v), pattern, expr))
      val defaultBranch = default.flatMap(simpleCodeGen).toList
      List(CStmt.Matches(branches, defaultBranch))
