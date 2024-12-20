package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import scala.annotation.tailrec
import collection.immutable.SortedMap
import hkmc2.utils.{TraceLogger, tl}

object DeBrujinSplit:
  final val Outermost = 1
  
  def elaborate(tree: syntax.Tree, elaborator: Elaborator)(using Elaborator.Ctx, Elaborator.State, Raise): DeBrujinSplit =
    import elaborator.tl.*, syntax.Tree, Tree.*, PatternStub.*, HelperExtractors.*
    type F = (Int, => DeBrujinSplit, => DeBrujinSplit) => DeBrujinSplit
    def cls(ctor: Ident | Sel, params: Ls[Tree]): F =
      val term = scoped("ucs:mute"):
        elaborator.cls(ctor, inAppPrefix = false)
      term.symbol.flatMap(_.asClsLike) match
        case S(symbol) =>
          val pattern = ClassLike(symbol)
          val paramCount = params.length
          if pattern.arity == paramCount || paramCount == 0 then
            (scrutinee, innermost, alternative) => trace(
              pre = s"cls ${pattern.showDbg} <<< $paramCount param(s)",
              post = (s: DeBrujinSplit) => s"cls ${pattern.showDbg} >>>\n${s.showDbg}"
            ):
              val consequence = params.zipWithIndex.foldRight(innermost.increment(paramCount)):
                case ((tree, index), inner) => trace(
                  pre = s"param $index <<<",
                  post = (s: DeBrujinSplit) => s"param $index >>>\n${s.showDbg}"
                ):
                  go(tree)(paramCount - index, inner, Reject)
              Branch(scrutinee, pattern, consequence.bind(paramCount), alternative)
          else
            (_, _, alternative) => alternative // TODO: report the error
        case N => (_, _, alternative) => alternative // TODO: report the error
    def go(tree: Tree): F = tree match
      case lhs or rhs => (scrutinee, consequence, alternative) => trace(
        pre = s"or <<<",
        post = (_: DeBrujinSplit) => s"or >>>"
      ):
        val buildLeft = go(lhs)
        val buildRight = go(rhs)
        val latter = buildRight(scrutinee, consequence, alternative)
        buildLeft(scrutinee, consequence, latter)
      case Ident("_") => (_, consequence, _) => consequence
      case ctor: (Ident | Sel) => cls(ctor, Nil)
      case App(ctor: (Ident | Sel), Tup(params)) => cls(ctor, params)
      case literal: syntax.Literal => Branch(_, Literal(literal), _, _)
    scoped("ucs:elaborate-pattern"):
      Binder(go(tree)(Outermost, Accept(0), Reject))
end DeBrujinSplit

import DeBrujinSplit.{Outermost}

enum DeBrujinSplit:
  case Binder(body: DeBrujinSplit)
  case Branch(scrutinee: Int,
              pattern: PatternStub,
              consequent: DeBrujinSplit,
              alternative: DeBrujinSplit)
  case Accept(outcome: Int)
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
    
  def showDbg: Str =
    def go(split: DeBrujinSplit): Str = split match
      case Binder(body) =>
        val bod = go(body)
        val shouldIndent = body match
          case Binder(_) => false
          case _ => true
        "λ " + (if shouldIndent then "\n" + bod.indent("  ") else bod)
      case Branch(scrutinee, pattern, consequence, alternative) =>
        val con = go(consequence)
        val alt = go(alternative)
        val shouldIndent = consequence match
          case Binder(_) => false
          case _ => con.contains('\n')
        s"$scrutinee is ${pattern.showDbg} -> " +
          (if shouldIndent then "\n" + con.indent("  ") else con) +
          (if alt == "reject" then "" else s"\n$alt")
      case Accept(outcome) => s"accept $outcome"
      case Reject => "reject"
    go(this)

  def display: Str =
    val freshName = for
      size <- (1 to Int.MaxValue).iterator
      chars <- ('a' to 'z').combinations(size)
    yield chars.mkString
    def go(split: DeBrujinSplit, ctx: SortedMap[Int, Str]): Str = split match
      case Binder(body) =>
        val name = freshName.next
        val bod = go(body, ctx.mapKeys(_ + 1).toSortedMap + (Outermost -> name))
        val shouldIndent = body match
          case Binder(_) => false
          case _ => true
        name + " => " + (if shouldIndent then "\n" + bod.indent("  ") else bod)
      case Branch(scrutinee, pattern, consequence, alternative) =>
        val con = go(consequence, ctx)
        val alt = go(alternative, ctx)
        val shouldIndent = consequence match
          case Binder(_) => false
          case _ => con.contains('\n')
        s"${ctx.getOrElse(scrutinee, "?")} is ${pattern.showDbg} -> " +
          (if shouldIndent then "\n" + con.indent("  ") else con) +
          (if alt == "reject" then "" else s"\n$alt")
      case Accept(outcome) => s"accept $outcome"
      case Reject => "reject"
    go(this, SortedMap())
end DeBrujinSplit

import DeBrujinSplit.{Binder, Branch, Accept, Reject}

case class Subst(entries: SortedMap[Int, Int], offset: Int):
  def get(key: Int): Option[Int] = entries.get(key - offset).map(_ + offset)
  infix def +(level: Int) = copy(offset = offset + level)

object Subst:
  def apply(entries: (Int, Int)*): Subst = Subst(SortedMap(entries*), 0)
  
extension (range: Range)
  infix def +(shift: Int): Range =
    Range(range.start + shift, range.end + shift, range.step)
    
extension (split: DeBrujinSplit)
  def ++(right: DeBrujinSplit): DeBrujinSplit =
    split match
      case Binder(body) => ??? // TODO: concatenating binders is ridiculous
      case Branch(scrutinee, pattern, consequence, alternative) =>
        Branch(scrutinee, pattern, consequence, alternative ++ right)
      case Accept(outcome) => split
      case Reject => right

  def unbind: (Int, DeBrujinSplit) =
    @tailrec
    def go(level: Int, split: DeBrujinSplit): (Int, DeBrujinSplit) = split match
      case Binder(body) => go(level + 1, body)
      case _ => (level, split)
    go(0, split)
  
  def bind(level: Int): DeBrujinSplit =
    (0 until level).foldRight(split)((_, body) => Binder(body))
  
  def increment(level: Int): DeBrujinSplit =
    def go(split: DeBrujinSplit, binderCount: Int): DeBrujinSplit = split match
      case Binder(body) => Binder(go(body, binderCount + 1))
      case split @ Branch(scrutinee, _, consequence, alternative) =>
        split.copy(scrutinee = if scrutinee > binderCount then scrutinee + level else scrutinee,
                   consequent = go(consequence, binderCount),
                   alternative = go(alternative, binderCount))
      case Accept(_) | Reject => split
    go(split, 0)
  
  def decrement(level: Int): DeBrujinSplit = increment(-level)
  
  def substitute(subst: Subst): DeBrujinSplit =
    def go(split: DeBrujinSplit)(using subst: Subst): DeBrujinSplit = split match
      case Binder(body) => Binder(go(body)(using subst + 1))
      case Branch(scrutinee, pattern, consequence, alternative) =>
        val newScrutinee = subst.get(scrutinee).getOrElse(scrutinee)
        Branch(newScrutinee, pattern, go(consequence), go(alternative))
      case Accept(outcome) => Accept(outcome)
      case Reject => Reject
    go(split)(using subst)
    
  def normalize(using TraceLogger): DeBrujinSplit =
    import DeBrujinSplit.*, PatternStub.*
    val visited = collection.mutable.Map[DeBrujinSplit.Branch, (Opt[Int], Opt[DeBrujinSplit])]()
    def go(split: DeBrujinSplit): DeBrujinSplit =
      split match
        case Binder(body) => Binder(go(body))
        case split @ Branch(scrutinee, pattern, consequence, alternative) => tl.trace(
          pre = s"normalize <<<\n${split.showDbg}",
          post = (s: DeBrujinSplit) => s"normalize >>>\n${s.showDbg}"
        ):
          val arity = pattern.arity
          val consequence2 = 
            consequence.unbind match
              case (level @ (`arity` | 0), body) =>
                // The scrutinee handling below is tricky.
                tl.log(s"[Step 1] specialize the consequence")
                val former = body.specialize(scrutinee + level, pattern, 1 to arity)
                tl.log(s"the former split:\n${former.showDbg}")
                // We need to increment the level because it is going to be put into a binder.
                val latter = alternative.specialize(scrutinee, pattern, 1 to arity)
                tl.log(s"the latter split:\n${latter.showDbg}")
                val res = go((former ++ latter))
                tl.log(s"increment by $arity")
                // If the original consequence doesn't have binders, we need to increment the level.
                val res2 = if level == arity then res else res.increment(arity)
                tl.log(s"bind with $arity")
                res2.bind(arity)
              case (_, _) =>
                // TODO: report mismatched arity
                tl.log("mismatched arity")
                Reject
          val alternative2 = go(alternative.despecialize(scrutinee, pattern))
          split.copy(consequent = consequence2, alternative = alternative2)
        case Accept(_) | Reject => split
      
    go(split)
  
  def specialize(scrutinee: Int, pattern: PatternStub, parameters: Range)(using TraceLogger): DeBrujinSplit =
    require(parameters.length == pattern.arity)
    def go(split: DeBrujinSplit)(using target: Int, parameters: Range): DeBrujinSplit =
      split match
        case Binder(body) =>
          tl.log("go into the binder")
          Binder(go(body)(using target + 1, parameters + 1))
        case Branch(`target`, `pattern`, consequence, alternative) =>
          val (level, body) = consequence.unbind
          tl.log(s"consequence:\n${consequence.showDbg}")
          tl.log(s"unbound consequence:\n${body.showDbg}")
          if level == 0 || level == pattern.arity then
            body ++ go(alternative)(using target, parameters)
          else
            // TODO: report mismatched arity.
            Reject
        case Branch(`target`, _, consequence, alternative) =>
          tl.log("skip the consequence")
          alternative
        case split @ Branch(_, _, consequence, alternative) =>
          split.copy(consequent = go(consequence),
                     alternative = go(alternative))
        case Accept(_) | Reject => split
    tl.trace(
      pre = s"S+ ($scrutinee is ${pattern.showDbg}) <<<" + {
        val dbg = split.showDbg
        if dbg.contains('\n') then s"\n$dbg" else s" $dbg"},
      post = (s: DeBrujinSplit) => s"S+ ($scrutinee is ${pattern.showDbg}) >>>" +
        (if s == split then " (no change)" else s"\n${s.showDbg}")
    ):
      go(split)(using scrutinee, parameters)

  def despecialize(scrutinee: Int, pattern: PatternStub)(using TraceLogger): DeBrujinSplit =
    def go(split: DeBrujinSplit)(using target: Int): DeBrujinSplit =
      split match
        case Binder(body) => Binder(go(body)(using target + 1))
        case Branch(`target`, `pattern`, _, alternative) =>
          go(alternative)
        case split @ Branch(_, _, consequence, alternative) =>
          split.copy(consequent = go(consequence),
                     alternative = go(alternative))
        case Accept(_) | Reject => split
    tl.trace(
      pre = s"S- ($scrutinee is ${pattern.showDbg}) <<<" + {
        val dbg = split.showDbg
        if dbg.contains('\n') then s"\n$dbg" else s" $dbg"},
      post = (s: DeBrujinSplit) => s"S- ($scrutinee is ${pattern.showDbg}) >>>" +
        (if s == split then " (no change)" else s"\n${s.showDbg}")
    ):
      go(split)(using scrutinee)
