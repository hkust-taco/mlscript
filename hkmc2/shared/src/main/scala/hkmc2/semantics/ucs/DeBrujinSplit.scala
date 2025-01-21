package hkmc2
package semantics
package ucs

import mlscript.utils.*, shorthands.*
import scala.annotation.tailrec
import collection.immutable.SortedMap
import utils.{TraceLogger, tl}, Message.MessageContext

object DeBrujinSplit:
  final val Outermost = 1
  
  def elaborate(patternParams: List[Param],
                tree: syntax.Tree,
                elaborator: Elaborator)
               (using Elaborator.Ctx,
                      Elaborator.State,
                      Raise): DeBrujinSplit =
    import elaborator.tl.*, syntax.Tree, Tree.*, PatternStub.*, HelperExtractors.*
    type F = (Int, => DeBrujinSplit, => DeBrujinSplit) => DeBrujinSplit
    /** Resolve the constructor in the elaborator context. */
    def resolve(ctor: Ident | Sel, params: Ls[Tree]): Opt[F] =
      val term = scoped("ucs:mute"):
        elaborator.cls(ctor, inAppPrefix = false)
      term.symbol.flatMap(_.asClsLike).map:
        case symbol: (ClassSymbol | ModuleSymbol) =>
          val pattern = ClassLike(ConstructorLike.Symbol(symbol))
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
          else (_, _, alternative) =>
            error(
              msg"The class `${symbol.nme}` expected ${pattern.arity.toString} arguments." -> symbol.toLoc,
              msg"But only ${paramCount.toString} sub-pattern${if paramCount == 1 then " is" else "s are"} given." ->
                params.foldLeft[Opt[Loc]](N):
                  (acc, tree) => acc.fold(tree.toLoc)(_ ++ tree.toLoc |> S.apply))
            alternative
        case symbol: PatternSymbol =>
          val arguments = params.map: param =>
            (Binder(go(param)(Outermost, Accept(0), Reject)), param)
          val pattern = ClassLike(ConstructorLike.Instantiation(symbol, arguments))
          val expectedArity = symbol.patternParams.size
          val actualArity = arguments.length
          if expectedArity == actualArity then
            (scrutinee, innermost, alternative) => trace(
              pre = s"pattern ${pattern.showDbg} <<< $actualArity param(s)",
              post = (s: DeBrujinSplit) => s"pattern ${pattern.showDbg} >>>\n${s.showDbg}"
            ):
              val arity = 0 // TODO: reserved for captures
              val consequence = innermost.increment(arity)
              Branch(scrutinee, pattern, consequence.bind(arity), alternative)
          else (_, _, alternative) =>
            error(
              msg"The pattern `${symbol.nme}` expected ${"pattern argument".pluralize(expectedArity, true)}." -> symbol.toLoc,
              msg"But ${"argument".pluralize(actualArity, true)} ${if actualArity == 1 then "is" else "are"} given." ->
                params.foldLeft[Opt[Loc]](N):
                  (acc, tree) => acc.fold(tree.toLoc)(_ ++ tree.toLoc |> S.apply))
            alternative
    /** Resolve the constructor name in `patternParams` first. Call `resolve` if
      * not found.
      */
    def dealWithCtor(ctor: Ident | Sel, params: Ls[Tree]): F = ctor match
      case Ident("~") => (scrutinee, innermost, alternative) =>
        Branch(scrutinee, ClassLike(ConstructorLike.StringJoin), innermost.increment(2), alternative)
        alternative
      case Ident(ctorName) => patternParams.find(_.sym.name == ctorName) match
        case S(Param(_, symbol, _)) => (scrutinee, innermost, alternative) =>
          log(s"found an input pattern: ${symbol.name}")
          val arity = 0 // TODO: fill in the arity
          Branch(scrutinee, ClassLike(ConstructorLike.Parameter(symbol)), innermost.increment(arity), alternative)
        case N => resolve(ctor, params).getOrElse: (_, _, alternative) =>
          error(msg"Name not found: ${ctorName}" -> ctor.toLoc)
          alternative
      case ctor: Sel => resolve(ctor, params).getOrElse: (_, _, alternative) =>
        error(msg"Name not found: ${ctor.showDbg}" -> ctor.toLoc)
        alternative
    def go(tree: Tree): F = tree.deparenthesized match
      case lhs or rhs => (scrutinee, consequence, alternative) => trace(
        pre = s"or <<<",
        post = (_: DeBrujinSplit) => s"or >>>"
      ):
        val buildLeft = go(lhs)
        val buildRight = go(rhs)
        val latter = buildRight(scrutinee, consequence, alternative)
        buildLeft(scrutinee, consequence, latter)
      case Under() => (_, consequence, _) => consequence
      case ctor: (Ident | Sel) => dealWithCtor(ctor, Nil)
      case App(Ident("-"), Tup(IntLit(n) :: Nil)) =>
        Branch(_, Literal(IntLit(-n)), _, _)
      case App(Ident("-"), Tup(DecLit(n) :: Nil)) =>
        Branch(_, Literal(DecLit(-n)), _, _)
      // BEGIN TODO: Support range patterns. This is just to suppress the errors.
      case (lo: StrLit) to (incl, hi: StrLit) =>
        (_, _, alternative) => alternative
      case (lo: IntLit) to (incl, hi: IntLit) =>
        (_, _, alternative) => alternative
      case (lo: DecLit) to (incl, hi: DecLit) =>
        (_, _, alternative) => alternative
      case (lo: syntax.Literal) to (_, hi: syntax.Literal) =>
        (_, _, alternative) => alternative
      // END TODO: Support range patterns
      case App(ctor: (Ident | Sel), Tup(params)) => dealWithCtor(ctor, params)
      case literal: syntax.Literal => Branch(_, Literal(literal), _, _)
    scoped("ucs:rp:elaborate"):
      log(s"tree: ${tree.showDbg}")
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
  
  /** Collect all the patterns matched by the first scrutinee, if any. */
  lazy val firstPatterns: Set[PatternStub] =
    def go(split: DeBrujinSplit, target: Int): Set[PatternStub] =
      split match
        case Binder(body) => go(body, target + 1)
        case Branch(scrutinee, pattern, consequent, alternative) =>
          go(consequent, target) ++ go(alternative, target) ++ 
            (if scrutinee == target then Set(pattern) else Set())
        case Accept(_) | Reject => Set()
    this match
      case Binder(body) => go(body, Outermost)
      case _ => Set()
  
  def showDbg: Str =
    def go(split: DeBrujinSplit): Str = split match
      case Binder(body) =>
        val bod = go(body)
        val shouldIndent = body match
          case Binder(_) => false
          case _ => bod contains '\n'
        "λ " + (if shouldIndent then "\n" + bod.indent("  ") else bod)
      case Branch(scrutinee, pattern, consequence, alternative) =>
        val con = go(consequence)
        val alt = go(alternative)
        val shouldIndent = consequence match
          case Binder(_) => false
          case _ => con.contains('\n')
        val pat = pattern match
          case PatternStub.ClassLike(ConstructorLike.Nested(split)) =>
            s"split: ${split.showDbg}\n"
          case _ => pattern.showDbg + " "
        s"$scrutinee is $pat-> " + 
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
  def from(entries: IterableOnce[(Int, Int)]): Subst = Subst(SortedMap.from(entries), 0)
  def apply(entries: (Int, Int)*): Subst = from(entries)
  
extension (range: Range)
  infix def +(shift: Int): Range =
    Range(range.start + shift, range.end + shift, range.step)

  // extension (branch: DeBrujinSplit.Branch)
  /** Expand all branches that match the same scrutinee against synonyms. */
  // def expandAll(using tl: TraceLogger): DeBrujinSplit =
  //   import DeBrujinSplit.*, PatternStub.*
  //   def go(split: DeBrujinSplit, scrutinee: Int): DeBrujinSplit =
  //     split match
  //     case Binder(body) => Binder(go(body, scrutinee + 1))
  //     case Branch(`scrutinee`, ClassLike(symbol: PatternSymbol), consequence, alternative) =>
  //       val consequence2 = go(consequence, scrutinee)
  //       val alternative2 = go(alternative, scrutinee)
  //       symbol.split.expand(scrutinee :: Nil, consequence2) ++ alternative2
  //     case split @ Branch(_, _, consequence, alternative) =>
  //       split.copy(consequent = go(consequence, scrutinee),
  //                  alternative = go(alternative, scrutinee))
  //     case Accept(_) | Reject => split
  //   tl.traceSplit(s"expandAll (${branch.scrutinee})", branch):
  //     go(branch, branch.scrutinee)

extension (split: DeBrujinSplit)
  def traceChange(prefix: => Str)(thunk: => DeBrujinSplit)(using TraceLogger) =
    tl.trace(
      pre = s"$prefix <<<" + {
        val dbg = split.showDbg
        if dbg.contains('\n') then s"\n$dbg" else s" $dbg"},
      post = (output: DeBrujinSplit) => s"$prefix >>>" +
        (if output == split then " (no change)" else s"\n${output.showDbg}")
    )(thunk)

  def ++(right: DeBrujinSplit): DeBrujinSplit =
    split match
      case Binder(body) => ??? // TODO: concatenating binders is ridiculous
      case Branch(scrutinee, pattern, consequence, alternative) =>
        Branch(scrutinee, pattern, consequence, alternative ++ right)
      case Accept(outcome) => split
      case Reject => right
  
  /** Count the outermost binders. */
  def arity: Int =
    @tailrec def go(split: DeBrujinSplit, n: Int): Int = split match
      case Binder(body) => go(body, n + 1)
      case _ => n
    go(split, 0)
  
  def freeScrutinees: Set[Int] =
    def go(acc: Set[Int], split: DeBrujinSplit, binderCount: Int): Set[Int] = split match
      case Binder(body) => go(acc, body, binderCount + 1)
      case Branch(scrutinee, _, consequence, alternative) =>
        val init = if scrutinee > binderCount then acc + scrutinee else acc
        go(go(init, consequence, binderCount), alternative, binderCount)
      case Accept(_) | Reject => acc
    go(Set(), split, 0)

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
  
  /** Apply a split to variables and replace all accepts with another split. */
  def expand(scrutinees: List[Int], consequence: DeBrujinSplit)(using tl: TraceLogger): DeBrujinSplit =
    import tl.*
    def go(split: DeBrujinSplit, binderCount: Int, subst: Map[Int, Int]): DeBrujinSplit = split match
      case Binder(body) => Binder(go(body, binderCount + 1, subst))
      case Branch(scrutinee, pattern, consequent, alternative) =>
        val newScrutinee = subst.get(scrutinee + binderCount) match
          case S(outermostIndex) => outermostIndex + binderCount
          case N => scrutinee
        Branch(newScrutinee, pattern,
               go(consequent, binderCount, subst),
               go(alternative, binderCount, subst))
      case Accept(_) =>
        // We assume there's only one outcome because it's in pattern synonyms.
        consequence.increment(binderCount)
      case Reject => Reject
    val arity = scrutinees.length
    split.unbind match
      case (`arity`, body) =>
        go(body, 0, (1 to arity).zip(scrutinees).toMap)
      case _ =>
        // lastWords(s"Arity mismatch in expand: ${split.unbind}")
        Reject // TODO: report mismatched arity
  
  def toSplit(scrutinees: Vector[() => Term.Ref],
              localPatterns: Map[Int, TempSymbol],
              outcomes: Map[Opt[Int], Split],
              elab: Elaborator)(using Elaborator.Ctx, Elaborator.State, Raise
  ): Split = elab.tl.trace(
    pre = s"toSplit <<<\n${split.showDbg}",
    post = (s: Split) => s"toSplit >>>\n${Split.display(s)}"
  ):
    import DeBrujinSplit.*, PatternStub.*, syntax.Tree.Empty, elab.tl.*
    scoped("ucs:rp:split"):
      val desugaring = new DesugaringBase:
        val elaborator = elab
      def go(split: DeBrujinSplit, ctx: Vector[() => Term.Ref]): Split =
        split match
        case Binder(body) => go(body, ctx)
        case Branch(scrutinee, pattern, consequence, alternative) =>
          log(s"pattern is ${pattern.showDbg}")
          lazy val nullaryConsequent = consequence.unbind match
            case (0, body) => go(body, ctx)
          pattern match
            case Literal(value) => 
              semantics.Branch(ctx(scrutinee - 1)(), Pattern.Lit(value), nullaryConsequent) ~: go(alternative, ctx)
            case ClassLike(ConstructorLike.Symbol(symbol: ClassSymbol)) =>
              log(s"make temporary symbols for $symbol")
              val subSymbols = (1 to symbol.arity).map(i => TempSymbol(N, s"arg_$i")).toList
              log(s"class case ${symbol.name} with ${subSymbols.length} sub-scrutinees")
              val consequent2 = consequence.unbind match
                case (level, body) => // TODO: check level == arity
                  val ctx2 = subSymbols.reverseIterator.map(s => () => s.ref()).toVector ++ ctx
                  log(s"now there are ${ctx2.length} elements in the new context")
                  go(body, ctx2)
              val select = scoped("ucs:sel"):
                elab.reference(symbol).getOrElse(Term.Error)
              val pattern = Pattern.ClassLike(symbol, select, S(subSymbols), false)(Empty())
              semantics.Branch(ctx(scrutinee - 1)(), pattern, consequent2) ~: go(alternative, ctx)
            case ClassLike(ConstructorLike.Symbol(symbol: ModuleSymbol)) =>
              val select = scoped("ucs:sel"):
                elab.reference(symbol).getOrElse(Term.Error)
              val pattern = Pattern.ClassLike(symbol, select, N, false)(Empty())
              semantics.Branch(ctx(scrutinee - 1)(), pattern, nullaryConsequent) ~: go(alternative, ctx)
            case ClassLike(ConstructorLike.LocalPattern(id)) =>
              log(s"apply scrutinee $scrutinee to local pattern $id")
              desugaring.makeLocalPatternBranch(ctx(scrutinee - 1)(), localPatterns(id), nullaryConsequent)(go(alternative, ctx))
            case ClassLike(ConstructorLike.Nested(split)) => // The arity of embedded splits is always 1.
              val innerConsequent = consequence.unbind match
                case (0, body) => go(body, ctx)
              val nestedOutcomes = Map(N -> Split.End, S(0) -> innerConsequent)
              split.toSplit(Vector(ctx(scrutinee - 1)), localPatterns, nestedOutcomes, elab) ~~: go(alternative, ctx)
        case Accept(outcome) => outcomes(S(outcome))
        case Reject => outcomes.getOrElse(N, Split.End)
      split.unbind match
        case (arity, body) if arity == scrutinees.length =>
          go(split, scrutinees)
        case _ =>
          error(msg"Mismatched arity in split" -> N)
          Split.End // TODO: report mismatched arity
  
  /** To instantiate the body of a pattern synonym. */
  def instantiate(context: Map[LocalSymbol & NamedSymbol, DeBrujinSplit])(using tl: TraceLogger): DeBrujinSplit =
    import DeBrujinSplit.*, PatternStub.*, ConstructorLike.*, tl.*
    def go(split: DeBrujinSplit): DeBrujinSplit = split.traceChange("instantiate"):
      split match
      case Binder(body) => Binder(go(body))
      case Branch(scrutinee, pattern0 @ ClassLike(Instantiation(symbol, arguments)), consequence, alternative) =>
        val instantiatedArguments = arguments.map:
          case (split, tree) => (go(split), tree)
        val pattern = ClassLike(Instantiation(symbol, instantiatedArguments))
        Branch(scrutinee, pattern, go(consequence), go(alternative))
      case Branch(scrutinee, ClassLike(Parameter(symbol)), consequence, alternative) =>
        context.get(symbol) match
          case S(split) =>
            split.expand(Ls(scrutinee), go(consequence)) ++ go(alternative)
          case N => lastWords(s"Pattern parameter not found: ${symbol.nme}")
      case Branch(scrutinee, pattern, consequence, alternative) =>
        Branch(scrutinee, pattern, go(consequence), go(alternative))
      case Accept(outcome) => Accept(outcome)
      case Reject => Reject
    scoped("ucs:rp:instantiation"):
      log(s"pattern parameter context:")
      context.foreach:
        case (symbol, split) => log(s"${symbol.nme} => ${split.showDbg}")
      go(split)
  
  def normalize(using tl: TraceLogger, raise: Raise): (DeBrujinSplit, Map[Int, DeBrujinSplit]) =
    import DeBrujinSplit.*, PatternStub.*, ConstructorLike.*, collection.mutable.{Buffer, Map as MutMap}, tl.*
    type Expansion = (id: Int, repr: Str, recursive: Bool, normalized: Opt[DeBrujinSplit])
    val expandedPatterns = MutMap.empty[Instantiation, Expansion]
    def go(split: DeBrujinSplit): DeBrujinSplit =
      scoped("ucs:rp:normalize"):
        split match
        case Binder(body) => Binder(go(body))
        case Branch(scrutinee, ClassLike(key @ Instantiation(symbol, arguments)), consequent, alternative) => trace(
          pre = s"pattern application <<< ${symbol.nme}",
          post = (s: DeBrujinSplit) => s"pattern application >>>\n${s.showDbg}"
        ):
          if arguments.size == symbol.patternParams.size then
            val pattern = expandedPatterns.get(key) match
            case S((id, repr, recursive, S(normalized))) =>
              ClassLike(if recursive then LocalPattern(id) else Nested(normalized))
            case S((id, repr, recursive, N)) =>
              if !recursive then
                scoped("ucs:rp:memo"):
                  log(s"found a recursive pattern: ${symbol.nme}")
                expandedPatterns += key -> (id, repr, true, N)
              ClassLike(LocalPattern(id))
            case N =>
              val repr = symbol.nme + arguments.iterator.map(_.tree.showDbg).mkString("(", ", ", ")")
              scoped("ucs:rp:memo"):
                log(s"add to memo: ${repr}")
              expandedPatterns += key -> (expandedPatterns.size, repr, false, N)
              val normalized =
                val context = symbol.patternParams.iterator.map(_.sym).zip(arguments.iterator.map(_.split)).toMap
                val instantiated = symbol.split.instantiate(context)
                scoped("ucs:rp:memo"):
                  log(s"instantiated: ${instantiated.showDbg}")
                go(instantiated)
              expandedPatterns.get(key) match
                case S((id, repr, recursive, N)) =>
                  expandedPatterns += key -> (id, repr, recursive, S(normalized))
                  ClassLike(if recursive then LocalPattern(id) else Nested(normalized))
                case S((id, _, _, S(_))) => lastWords(s"the pattern should not be normalized: ${symbol.nme}")
                case N => lastWords(s"the pattern should be memoized: ${symbol.nme}")
            Branch(scrutinee, pattern, go(consequent), go(alternative))
          else
            // TODO: maybe this check is unnecessary as it has been checked in the elaboration.
            error(
              msg"Pattern `${symbol.nme}` expects ${"pattern argument".pluralize(symbol.patternParams.size, true)}" ->
                symbol.patternParams.foldLeft[Opt[Loc]](N):
                case (N, param) => param.sym.toLoc
                case (S(loc), param) => S(loc ++ param.sym.toLoc),
              msg"But ${"pattern argument".pluralize(arguments.size, true)} were given" -> N)
            Reject
        case split @ Branch(scrutinee, pattern, consequence, alternative) => trace(
          pre = s"normalize <<<\n${split.showDbg}",
          post = (s: DeBrujinSplit) => s"normalize >>>\n${s.showDbg}"
        ):
          scoped("ucs:rp:normalize"):
            val arity = pattern.arity
            val whenTrue = consequence.unbind match
              case (level @ (`arity` | 0), consequentBody) =>
                // The scrutinee handling below is tricky.
                val former = trace(s"[Step 1] specialize consequence"):
                  consequentBody.specialize(scrutinee + level, pattern, 1 to arity)
                // We need to increment the level because it is going to be put into a binder.
                val latter = trace(s"[Step 2] specialize alternative"):
                  alternative.specialize(scrutinee, pattern, 1 to arity)
                val together = former ++ latter
                log(s"[Step 3] concatenate specialized splits\n${together.showDbg}")
                val res = trace(s"[Step 4] normalize concatenated splits"):
                  go(together)
                // If the original consequence doesn't have binders, we need to increment the level.
                val res2 = if level == arity then res else res.increment(arity)
                // log(s"bind with $arity")
                res2.bind(arity)
              case (_, _) => lastWords("unexpected number of binders")
            val whenFalse =
              log(s"[Step 5] despecialize alternative")
              val despecialized = alternative.despecialize(scrutinee, pattern)
              go(despecialized)
            split.copy(consequent = whenTrue, alternative = whenFalse)
        case Accept(_) | Reject => split
    end go
    val rootSplit = go(split)
    val recursivePatterns = expandedPatterns.iterator.collect:
      // Maybe we can store more information about the instantiation.
      case (pattern, (id, _, true, S(normalized))) => (id, normalized)
    .toMap
    scoped("ucs:rp:memo"):
      log("memo:")
      expandedPatterns.values.foreach:
        case (id, repr, true, S(normalized)) => log(s"$id $repr =>\n${normalized.display}")
        case _ => ()
    (rootSplit, recursivePatterns)
  
  def specialize(scrutinee: Int, pattern: PatternStub, parameters: Range)(using tl: TraceLogger): DeBrujinSplit =
    import PatternStub.*, ConstructorLike.*, tl.*
    require(parameters.length == pattern.arity)
    def go(split: DeBrujinSplit)(using target: Int, parameters: Range): DeBrujinSplit =
      split match
        case Binder(body) =>
          log("go into the binder")
          Binder(go(body)(using target + 1, parameters + 1))
        case Branch(`target`, `pattern`, consequence, alternative) =>
          val (level, body) = consequence.unbind
          log(s"consequence:\n${consequence.showDbg}")
          log(s"unbound consequence:\n${body.showDbg}")
          val substedConsequent = if level == 0 then body else body.substitute(Subst.from((1 to level).zip(parameters)))
          if level == 0 || level == pattern.arity then
            body ++ go(alternative)(using target, parameters)
          else
            lastWords("unexpected number of binders")
        case Branch(`target`, pattern, consequence, alternative) =>
          log(s"found ${pattern.showDbg}: remove the consequent")
          go(alternative)
        case split @ Branch(_, _, consequence, alternative) =>
          split.copy(consequent = go(consequence),
                     alternative = go(alternative))
        case Accept(_) | Reject => split
    split.traceChange(s"S+ $scrutinee is ${pattern.showDbg}#${pattern.arity}${parameters.mkString("(", ", ", ")")}"):
      go(split)(using scrutinee, parameters)

  def despecialize(scrutinee: Int, pattern: PatternStub)(using TraceLogger): DeBrujinSplit =
    def go(split: DeBrujinSplit)(using target: Int): DeBrujinSplit =
      split match
        case Binder(body) => Binder(go(body)(using target + 1))
        case Branch(`target`, `pattern`, _, alternative) => go(alternative)
        case split @ Branch(_, _, consequent, alternative) =>
          split.copy(consequent = go(consequent),
                     alternative = go(alternative))
        case Accept(_) | Reject => split
    split.traceChange(s"S- $scrutinee is ${pattern.showDbg}#${pattern.arity}"):
      go(split)(using scrutinee)
