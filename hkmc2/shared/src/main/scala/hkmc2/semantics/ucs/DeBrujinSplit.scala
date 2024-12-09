package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*

object DeBrujinSplit:
  final val Outermost = 1
  
  type Alternative = Branch | Reject.type
  
  // def elaborate(tree: syntax.Tree, elaborator: Elaborator)(using Elaborator.Ctx) =
  //   import syntax.Tree, Tree.*, PatternStub.*, HelperExtractors.*, elaborator.tl.*
  //   type F = (=> DeBrujinSplit, => Alternative) => Alternative
  //   def nest(constructor: Ident | Sel, parameters: Ls[Tree]): F =
  //     val clsTrm = elaborator.cls(constructor, inAppPrefix = false)
  //     clsTrm.symbol.flatMap(_.asClsLike).map(ClassLike.apply) match
  //       case S(pattern) => (conclusion, alternative) =>
  //         val consequence = parameters.foldRight(conclusion):
  //           case (parameter, acc) => 
  //         Branch(Outermost, pattern, consequence, alternative)
  //       case N => (_, alternative) => alternative
  //   def next(n: Int, tree: Tree): F = tree match
  //     case lhs or rhs => (consequence, alternative) =>
  //       next(lhs)(consequence, next(rhs)(consequence, alternative))
  //     case literal: syntax.Literal => (consequence, alternative) =>
  //       Branch(Outermost, Literal(literal), consequence, alternative)
  //     case constructor: (Ident | Sel) => nest(constructor, Nil)
  //     case App(constructor: (Ident | Sel), Tup(parameters)) =>
  //       nest(constructor, parameters)
  //   Binder(next(tree)(Accept(Nil), Reject))
end DeBrujinSplit

import DeBrujinSplit.{Alternative, Outermost}

enum DeBrujinSplit:
  case Binder(body: DeBrujinSplit)
  case Branch(scrutinee: Int,
              pattern: PatternStub,
              consequence: DeBrujinSplit,
              alternative: Alternative)
  case Accept(variables: List[Int])
  case Reject
  
  def firstPatterns: Set[PatternStub] =
    def go(split: DeBrujinSplit, target: Int): Set[PatternStub] =
      split match
        case Binder(body) => go(body, target + 1)
        case Branch(scrutinee, pattern, consequence, alternative) =>
          go(consequence, target) ++ go(alternative, target) ++ 
            (if scrutinee == target then Set(pattern) else Set())
        case Accept(_) | Reject => Set()
    go(this, Outermost)
    
  def display: Str =
    val freshName = for
      size <- (1 to Int.MaxValue).iterator
      chars <- ('a' to 'z').combinations(size)
    yield chars.mkString
    def go(split: DeBrujinSplit, ctx: Map[Int, Str]): Str = split match
      case Binder(body) => go(body, ctx.mapKeys(_ + 1).toMap + (Outermost -> freshName.next))
      case Branch(scrutinee, pattern, consequence, alternative) =>
        val con = go(consequence, ctx)
        val alt = go(alternative, ctx)
        s"${ctx(scrutinee)} is ${pattern.showDbg} -> " +
          (if con.contains('\n') then "\n" + con.indent("  ") else con) +
          (if alt == "reject" then "" else s"\n$alt")
      case Accept(indices) => indices.map(ctx).mkString("accept ", " ", "")
      case Reject => "reject"
    go(this, Map())
    
// extension (split: DeBrujinSplit.Binder)
//   def zip(that: DeBrujinSplit.Binder): DeBrujinSplit.Binder =
//     def go(lhs: DeBrujinSplit, rhs: DeBrujinSplit): DeBrujinSplit =
//       (lhs, rhs) match
//         case (Binder(lhsBody), Binder(rhsBody)) => Binder(go(lhsBody, rhsBody))
//         case (Branch())
//   def specialize(topicPattern: PatternStub): DeBrujinSplit =
//     import DeBrujinSplit.*
//     def go(split: DeBrujinSplit, target: Int): DeBrujinSplit =
//       split match
//         case Binder(body) => go(body, target + 1)
//         case Branch(`target`, pattern, consequence, alternative) =>
//           // We should check if the topic pattern can be subsumed by the current
//           // pattern. We simply use equality check for now.
//           if pattern == topicPattern then
//             consequence ++ go(alternative, target)
//           else
//             Reject
//         case split @ Branch(_, _, consequence, alternative) =>
//           split.copy(consequence = go(consequence, target),
//                      alternative = go(alternative, target))
//         case Accept(_) | Reject => split
//     go(split.body, Outermost)
