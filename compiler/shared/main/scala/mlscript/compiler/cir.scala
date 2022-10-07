package memir

enum CType:
  case Void
  case Int32
  case Pointer

  override def toString(): String = this match
    case Void    => "void"
    case Int32   => "int"
    case Pointer => "void*"

enum CExpr:
  case Alloc
  case IntConst(val v: Int)
  case Dup(val ptr: CExpr)
  case Var(val name: String)

  case Call(val f: String, params: List[CExpr])
  // indices: somewhat similar to GEP index in LLVM, but we do perform memory
  // access because our nodes are of fixed size
  case FieldAccess(val obj: CExpr, val indices: List[Int])

  case Cast(val ty: CType, val v: CExpr)
  case TypeMatch(val obj: CExpr, val ty: IRClassType)

  override def toString(): String = this match
    case Alloc           => "alloc()"
    case IntConst(v)     => v.toString()
    case Dup(ptr)        => s"dup($ptr)"
    case Var(name)       => name
    case Call(f, params) => s"f(${params.map(_.toString()).mkString(", ")})"
    case FieldAccess(obj, indices) =>
      obj.toString() ++ "[" ++ indices.map(_.toString()).mkString(", ") ++ "]"
    case Cast(ty, v)        => s"($ty)($v)"
    case TypeMatch(obj, ty) => s"typematch($obj, $ty)"

enum CStmt:
  case Drop(val ptr: CExpr)
  case Assignment(val lhs: CExpr, val rhs: CExpr)
  case Matches(branches: List[(CExpr, List[CStmt])], otherwise: List[CStmt])

  def prettyPrint(level: Int = 0): String =
    val indent = "  " * level
    this match
      case Drop(ptr)            => indent ++ s"drop($ptr)"
      case Assignment(lhs, rhs) => indent ++ s"$lhs = $rhs"
      case Matches(branches, otherwise) =>
        val branchLines = branches.zipWithIndex.map((b, i) =>
          (indent ++ (if i == 0 then "if " else "else if ") ++ b._1
            .toString() ++ ":") ::
            b._2.map(_.prettyPrint(level + 1))
        )
        val lines =
          if otherwise.isEmpty then branchLines
          else
            branchLines ++ (s"$indent else:" :: otherwise.map(
              _.prettyPrint(level + 1)
            ))
        lines.mkString("\n")

class CFunction(
    val params: List[(String, CType)],
    val ret: CType,
    val statements: List[CStmt]
)

class CRegistry(
    // function names: `{classid}${methodname}`
    val functions: Map[String, CFunction]
)
