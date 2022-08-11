package mlscript.mono.printer

import mlscript.mono.{Expr, Isolation, Item, Module, Parameter}

class ExprPrinter:
  private val printer = BlockPrinter()

  import printer.{endLine, enter, leave, print}

  private def show(module: Module): Unit = module.items.foreach {
    case expr: Expr => show(expr)
    case item: Item => show(item)
  }

  private def show(params: List[Parameter]): String =
    params.iterator.map {
      case (spec, Expr.Ref(name)) => (if spec then "#" else "") + name
    }.mkString("(", ", ", ")")

  private def show(item: Item): Unit = item match
    case Item.TypeDecl(Expr.Ref(name), kind, typeParams, params, parents, body) =>
      val typeParamsStr = if typeParams.isEmpty then ""
        else typeParams.iterator.map(_.name).mkString("[", ", ", "]")
      val parentsStr = if parents.isEmpty then ""
        else parents.iterator.map(_.show).mkString(": ", " with ", "")
      print(s"$kind $name$typeParamsStr${show(params)}$parentsStr ")
      show(body)
    case Item.FuncDecl(Expr.Ref(name), params, body) =>
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

  // private def show(expr: Expr): Unit = expr match
  //   case Expr.Ref(name) => name
  //   case Expr.Lambda(params, body) => 
  //     val head = params.mkString("(", ", ", ")")
  //     s"(fun $head -> $body)"
  //   case Expr.Apply(Expr.Apply(Expr.Ref("."), lhs :: Nil), rhs :: Nil) =>
  //     s"$lhs.$rhs"
  //   case Expr.Apply(Expr.Apply(Expr.Ref(op), lhs :: Nil), rhs :: Nil)
  //       if !op.headOption.forall(_.isLetter) =>
  //     s"($lhs $op $rhs)"
  //   case Expr.Apply(callee, arguments) =>
  //     val tail = arguments.mkString(", ")
  //     s"($callee $tail)"
  //   case Expr.Tuple(fields) => 
  //     val inner = fields.mkString(", ")
  //     "(" + (if fields.length == 1 then inner + ", " else inner) + ")"
  //   case Expr.Record(fields) =>
  //     "{" + fields.iterator.map { (name, value) => s"$name = $value" } + "}"
  //   case Expr.Select(receiver, field) => s"$receiver.$field"
  //   case Expr.LetIn(isRec, name, rhs, body) => s"let $name = $rhs in $body"
  //   case Expr.Block(items) => items.mkString(";")
  //   case Expr.As(value, toType) => s"$value as $toType"
  //   case Expr.Assign(assignee, value) => s"$assignee = $value"
  //   case Expr.With(value, fields) => s"$value with $fields"
  //   case Expr.Subscript(receiver, index) => s"$receiver[$index]"
  //   case Expr.Match(scrutinee, branches) =>
  //     s"$scrutinee match " + branches.iterator.mkString("{", "; ", "}")
  //   case Expr.Literal(value) => value.toString
  //   case Expr.New(Some((callee, args)), body) =>
  //     s"new ${callee.name}" + args.mkString(" (", ", ", ") ") + body.toString
  //   case Expr.New(None, body) => "new " + body.toString
  //   case Expr.IfThenElse(condition, consequent, None) =>
  //     s"if $condition then $consequent"
  //   case Expr.IfThenElse(condition, consequent, Some(alternate)) =>
  //     s"if $condition then $consequent else $alternate"
  //   case Expr.Isolated(isolation) => s"{\n$isolation\n}"

object ExprPrinter:
  def print(node: Module | Item | Isolation | Expr): String =
    val printer = ExprPrinter()
    node match
      case module: Module => printer.show(module)
      case item: Item => printer.show(item)
      case isolation: Isolation => printer.show(isolation)
      case expr: Expr => printer.show(expr)
    printer.toString

  def printLines(node: Module | Item | Isolation | Expr): List[String] =
    val printer = ExprPrinter()
    node match
      case module: Module => printer.show(module)
      case item: Item => printer.show(item)
      case isolation: Isolation => printer.show(isolation)
      case expr: Expr => printer.show(expr)
    printer.toLines
