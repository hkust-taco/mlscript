package mlscript.compiler.printer

import mlscript.compiler.{Expr, Isolation, Item, ModuleUnit, Parameter}

class ExprPrinter:
  private val printer = BlockPrinter()

  import printer.{endLine, enter, leave, print}

  private def show(module: ModuleUnit): Unit = module.items.foreach {
    case expr: Expr => show(expr)
    case item: Item => show(item)
  }

  private def show(params: List[Parameter]): String =
    params.iterator.map {
      case (flags, Expr.Ref(name), _) => (if flags.spec then "#" else "") + name
    }.mkString("(", ", ", ")")

  private def show(params: Option[List[Parameter]]): String = params match
    case None => ""
    case Some(p) => p.iterator.map {
      case (flags, Expr.Ref(name), _) => (if flags.spec then "#" else "") + name
    }.mkString("(", ", ", ")")

  private def show(item: Item): Unit = item match
    case Item.TypeDecl(Expr.Ref(name), kind, typeParams, params, parents, body) =>
      val typeParamsStr = if typeParams.isEmpty then ""
        else typeParams.iterator.map(_.name).mkString("[", ", ", "]")
      val reprParents = if parents.isEmpty then ""
        else parents.iterator.map { case (parent, args) =>
          parent.show(true) + args.iterator.mkString("(", ", ", ")")
        }.mkString(": ", ", ", "")
      print(s"$kind $name$typeParamsStr${show(params)}$reprParents ")
      show(body)
    case Item.FuncDecl(isLetRec, Expr.Ref(name), params, body) =>
      print(s"fun $name${show(params)} =")
      enter()
      show(body)
      leave()
    case Item.FuncDefn(Expr.Ref(name), typeParams, polyType) =>
      val reprTypeParams = if typeParams.isEmpty then "" else
        s"${typeParams.mkString("[", ", ", "]")} => "
      print(s"fun $name: $reprTypeParams${polyType.show}")

  private def show(isolation: Isolation): Unit =
    enter("{", "}")
    isolation.items.foreach {
      case expr: Expr => show(expr)
      case item: Item => show(item)
    }
    leave()

  private def show(expr: Expr) =
    print(expr.toString)
    endLine()

  def toLines: List[String] = printer.toLines

  override def toString(): String = printer.toString

object ExprPrinter:
  def print(node: ModuleUnit | Item | Isolation | Expr): String =
    val printer = ExprPrinter()
    node match
      case module: ModuleUnit => printer.show(module)
      case item: Item => printer.show(item)
      case isolation: Isolation => printer.show(isolation)
      case expr: Expr => printer.show(expr)
    printer.toString

  def printLines(node: ModuleUnit | Item | Isolation | Expr): List[String] =
    val printer = ExprPrinter()
    node match
      case module: ModuleUnit => printer.show(module)
      case item: Item => printer.show(item)
      case isolation: Isolation => printer.show(isolation)
      case expr: Expr => printer.show(expr)
    printer.toLines
