package memir

class IRClassType(
    // class ID, should be unique for different types
    val id: Int,
    // instance fields of the class
    val fields: List[IRType],
    // instance methods of the class, this will be stored in a method table
    //
    // (multiple) inheritance is not handled (yet)...
    // we now assume that the methods can be identified statically, as casts can
    // only convert between pointer and the original type
    val methods: Map[String, (IRType, IRType)]
)

enum IRType:
  case Ptr
  case Int32
  case Union(val types: List[IRClassType])

trait LayoutGenerator:
  def size(ty: IRType): Int
  def layout(fields: List[IRType]): List[List[Int]]

class SimpleLayoutGenerator(n: Int) extends LayoutGenerator:
  import IRType.*

  def size(ty: IRType): Int = ty match
    case Ptr       => 8
    case Int32     => 4
    case Union(_)  => 8

  def layout(fields: List[IRType]): List[List[Int]] =
    def f(m: Int, i: Int, ls: List[(IRType, Int)]): List[List[Int]] = ls match
      case (field, r) :: remaining =>
        if n == m && r > n then f(n - 8, i, ls)
        else if m >= size(field) then
          List.fill(i)(0) ++ List(n - m) :: f(m - size(field), i, remaining)
        else f(n, i + 1, ls)
      case Nil => Nil
    val remainingSize = fields.map(size).reverse.scanLeft(0)(_ + _).reverse
    f(n, 0, fields.zip(remainingSize))

