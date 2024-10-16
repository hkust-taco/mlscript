package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.*


sealed abstract class Block extends Product with AutoLocated:
  protected def children: Ls[Located] = ??? // Maybe extending AutoLocated is unnecessary
  lazy val definedVars: Set[Local] = this match
    case _: Return | _: Throw => Set.empty
    case Begin(sub, rst) => rst.definedVars
    case Assign(l, r, rst) => rst.definedVars + l
    case Match(scrut, arms, dflt, rst) =>
      arms.flatMap(_._2.definedVars).toSet ++ dflt.toList.flatMap(_.definedVars) ++ rst.definedVars
    case End(_) => Set.empty
    case Define(defn, rst) => rst.definedVars

case class Match(
  scrut: Path,
  arms: Ls[Case -> Block],
  dflt: Opt[Block],
  rest: Block,
) extends Block with ProductWithTail

case class Return(res: Result) extends Block

case class Throw(exc: Result) extends Block

case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail

sealed abstract class Defn

final case class TermDefn(
    k: syntax.TermDefKind,
    sym: TermSymbol,
    params: Opt[Ls[Param]],
    body: Block,
) extends Defn

/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends Block with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassSymbol)

sealed abstract class Result

type Local = LocalSymbol

case class Call(fun: Path, args: Ls[Path]) extends Result

abstract class Path extends Result

case class Select(qual: Path, name: Tree.Ident) extends Path

enum Value extends Path:
  case Ref(l: Local)
  case Lit(lit: Literal)
  case Lam(params: Ls[Param], body: Block)

