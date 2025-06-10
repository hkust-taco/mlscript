package hkmc2
package semantics
package ups


import mlscript.utils.shorthands.*

import syntax.Tree, Tree.Ident
import codegen.{Block, Case, Match, End}
import Pattern.Head

import collection.mutable.Map as MutMap
import collection.immutable.{Set, Map}
import hkmc2.codegen.Value.Rcd
import hkmc2.codegen.RcdArg


class Compiler(using Elaborator.State, Raise):

  private type Label = Int

  var labelMap: MutMap[Pattern, Label] = MutMap()

  var multiMatchers: MutMap[Set[Label], BlockLocalSymbol] = MutMap()
  var implementations: MutMap[BlockLocalSymbol, Block] = MutMap()

  extension (pattern: Pattern)

    def label: Label = labelMap.getOrElseUpdate(pattern, labelMap.size)

  def buildMatchFunction(patterns: Set[Pattern]): BlockLocalSymbol =
    val labels = patterns.map(_.label)
    multiMatchers.get(labels) match
    case Some(f) => f
    case None =>
      val f = TempSymbol(N, s"multimatcher_${multiMatchers.size}")
      multiMatchers += (labels -> f)
      val expandedPatterns = patterns.map(p => (p.label, p.expand()))
      val heads = expandedPatterns.flatMap((_, p) => p.heads).toList
      val scrut = TempSymbol(N, s"scrut")
      val branches = heads.map: head =>
        val specialized = expandedPatterns.map((l, p) => (l, p.specialize(Some(head))))
        val branch = multiMatcherBranch(specialized, scrut)
        head match
          case Term.Lit(lit) => (Case.Lit(lit), branch)
          case sym: ClassSymbol => (Case.Cls(sym, ???), branch)
      val els =
        val specialized = expandedPatterns.map((l, p) => (l, p.specialize(None)))
        multiMatcherBranch(specialized, scrut)
      implementations += (f -> Match(/* scrut */???, branches, Some(els), ???))
      f

  def multiMatcherBranch(patterns: Set[(Label, Pattern)], scrut: BlockLocalSymbol): Block =
    val labels = patterns.map((l, _) => l)
    val fields = patterns.flatMap((_, p) => p.fields)
    val subScrutineeVars = Map.from(fields.map(id => id -> TempSymbol(N, s"$scrut.$id")))
    val bindings = fields.map: field =>
      val subPatterns = patterns.flatMap((_, p) => p.collectSubPatterns(field))
      val f = buildMatchFunction(subPatterns)
      ???
    ???
