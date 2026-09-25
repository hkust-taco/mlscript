package hkmc2
package codegen

import scala.collection.mutable

import hkmc2.utils.*, shorthands.*
import semantics.*
import semantics.Elaborator.{Ctx, State}
import semantics.Term.*

/** The capability to inspect completed resolution. Created only after elaboration/resolution;
  * executable lowering additionally requires this instance's whole-program pass to have finished.
  */
final class Erasure private (using Config, Ctx, State):
  private given Erasure = this
  private var completed: Opt[Statement] = N

  def requireCompleted(statement: Statement): Unit =
    assert(completed.exists(_ is statement), "Lowering requires completed erasure of this program")

  /** Erase an interpretation registered during elaboration, without installing new listeners. */
  private def erase(resolution: TypeResolution, seen: Set[TypeResolution]): ErasedValueType =
    import TypeShape.*
    if seen(resolution) || resolution.hasErrors then ErasedType.Unknown
    else
      val next = seen + resolution
      resolution.shapes.toList match
        case Nominal(defn) :: Nil => defn.sym match
          case symbol: (ClassSymbol | ModuleOrObjectSymbol) => ErasedType.ValueLike(S(false), symbol)
          case _ => ErasedType.Unknown
        case Alias(_, rhs) :: Nil => rhs.fold(ErasedType.Unknown)(erase(_, next))
        case Union(left, right) :: Nil => ErasedType.union(erase(left, next), erase(right, next))
        case Captured(base, _) :: Nil => erase(base, next)
        case Applied(base, _) :: Nil => erase(base, next)
        case Function(_, _) :: Nil => ErasedType.Function(S(false))
        case Polymorphic(_, _, body) :: Nil => erase(body, next)
        case Unit :: Nil => ErasedType.Unit
        case _ => ErasedType.Unknown

  private def eraseSignature(sign: Term): Opt[ErasedValueType] =
    if config.language.useNewResolution then
      assert(sign.typeInterpretation.isDefined, "Signature was not registered during elaboration")
      S(erase(sign.typeInterpretation.get, Set.empty))
    else ErasedType.eraseSign(sign)

  private def declaredType(sign: Opt[Term], modulefulness: Modulefulness): Opt[ErasedValueType] =
    modulefulness.msym match
      case S(msym) => S(ErasedType.ValueLike(rsc = S(false), msym))
      case N => sign.flatMap(eraseSignature)

  /** Splits written arrows, retaining an unknown arity when a parameter tuple contains a spread. */
  private def splitSignature(sign: Term): Opt[(Ls[Ls[Opt[ErasedValueType]]], Term)] =
    def paramsOf(lhs: Term): Opt[Ls[Opt[ErasedValueType]]] = lhs match
      case Tup(fields) =>
        val noParams: Opt[Ls[Opt[ErasedValueType]]] = S(Nil)
        fields.foldRight(noParams): (fld, acc) =>
          (fld, acc) match
            case (Fld(_, t, _), S(rest)) => S(eraseSignature(t) :: rest)
            case _ => N
      case single => S(eraseSignature(single) :: Nil)
    sign match
      case Forall(_, _, body) => splitSignature(body)
      case FunTy(lhs, rhs, _) => paramsOf(lhs).map: ps =>
        splitSignature(rhs) match
          case S((rest, ret)) => (ps :: rest, ret)
          case N => (ps :: Nil, rhs)
      case _ => N

  private def definitionType(td: TermDefinition): Opt[ErasedType] =
    val declared = Annot.declareModifierOf(td.annotations).isDefined
    // A declared function with no written parameters obtains its calling convention from its arrows.
    // An ordinary paramless function instead returns the value denoted by the entire signature.
    val sigShape =
      if (td.k is syntax.Fun) && td.params.isEmpty && declared then td.sign.flatMap(splitSignature)
      else N
    val resultSign = sigShape.map(_._2).orElse(td.resultSignature)
    def fullResult(res: TypeResolution, count: Int, seen: Set[TypeResolution]): ErasedValueType =
      if seen(res) then ErasedType.Unknown
      else if count == 0 then erase(res, Set.empty)
      else res.shapes.toList match
        case TypeShape.Alias(_, S(rhs)) :: Nil => fullResult(rhs, count, seen + res)
        case TypeShape.Captured(base, _) :: Nil => fullResult(base, count, seen + res)
        case TypeShape.Applied(base, _) :: Nil => fullResult(base, count, seen + res)
        case TypeShape.Polymorphic(_, _, body) :: Nil => fullResult(body, count, seen + res)
        case TypeShape.Function(_, ret) :: Nil => fullResult(ret, count - 1, seen + res)
        case _ => ErasedType.Unknown
    val resultType =
      if config.language.useNewResolution && td.sign.nonEmpty && (td.k is syntax.Fun)
          && !td.flags.hasResultAnnotation && td.params.nonEmpty && !td.modulefulness.isModuleful
      then S(fullResult(td.sign.get.typeInterpretation.get, td.params.length, Set.empty))
      else declaredType(resultSign, td.modulefulness)
    td.k match
      case syntax.Fun =>
        val paramLists = sigShape match
          case S((ps, _)) => ps
          case N => td.params.map(_.params.map(_.sym.erasedType))
        // Block-level nullary functions take an implicit empty list and references auto-invoke them.
        // Member getters and global declarations denote their result directly.
        val physicalParamLists =
          if paramLists.isEmpty && td.owner.isEmpty && !declared then Nil :: Nil else paramLists
        if physicalParamLists.isEmpty then resultType
        else S(ErasedType.FuncRef(rsc = S(false), physicalParamLists, resultType))
      case _: syntax.Val => resultType
      case _ => N

  private def run(root: Statement): Unit =
    val visited = mutable.Set.empty[Identity[Statement]]
    val statements = mutable.ArrayBuffer.empty[Statement]
    val parameters = mutable.ArrayBuffer.empty[Param]
    def params(ps: ParamList): Unit = ps.foreach(parameters += _)
    // Handler continuations and rejected class rest parameters can survive as references after their
    // parameter list has been removed. The symbol retains the source declaration needed for erasure.
    def referencedParameter(sym: VarSymbol): Unit = sym.decl match
      case S(p: Param) =>
        parameters += p
        p.subTerms.foreach(visit)
      case _ => ()
    def visit(statement: Statement): Unit = if visited.add(Identity(statement)) then
      statements += statement
      statement match
        case td: TermDefinition => td.params.foreach(params); td.tparams.foreach(_.foreach(parameters += _))
        case cls: ClassLikeDef =>
          cls.paramsOpt.foreach(params)
          cls.auxParams.foreach: ps =>
            params(ps)
            ps.subTerms.foreach(visit)
          cls.ext.foreach(visit)
          cls match
            case pat: PatternDef =>
              parameters ++= pat.parameters
              pat.parameters.flatMap(_.subTerms).foreach(visit)
              pat.pattern.subTerms.foreach(visit)
            case _ => ()
        case Lam(ps, _) => params(ps)
        case Handle(_, _, _, _, definitions, _) => definitions.foreach: d =>
          referencedParameter(d.resumeSym)
          visit(d.td)
        case Ref(sym: VarSymbol) => referencedParameter(sym)
        case SimpleRef(sym: VarSymbol) => referencedParameter(sym)
        case New(_, _, refinement) => refinement.foreach(r => visit(r._2.blk))
        case Rcd(_, stats) => stats.foreach(visit)
        case _ => ()
      statement.subStatements.foreach(visit)
      // Legacy resolution may insert executable terms (for example implicit applications).
      // Expanded nodes may share their children with the source tree; visit their identities only once.
      statement match
        case term: Resolvable => visit(term.expanded)
        case _ => ()
    visit(root)

    // No erased representation is read until every interpretation has been validated and every
    // nominal parent header has been published, including forward and external declarations.
    statements.foreach:
      case term: Term => term.typeInterpretation.foreach(_.validate(Set.empty))
      case _ => ()
    statements.foreach:
      case cls: ClassLikeDef => cls.sym match
        case sym: ClassLikeSymbol if sym.irClassHeader.isEmpty =>
          sym.irClassHeader = cls.ext match
            case N => S(ClassHeader(N))
            case S(parent) => parent.cls.resolvedSym.flatMap(_.asClsOrMod).map(p => ClassHeader(S(p)))
        case _ => ()
      case _ => ()

    parameters.foreach: p =>
      if !p.sym.isErased then p.sym.erasedType = declaredType(p.sign, p.modulefulness)
      // Public fields have a BlockMemberSymbol; private/auxiliary constructor fields have a TermSymbol.
      // Their source signatures belong to the parameter, not to the synthesized field definition.
      val field = p.fldSym.flatMap:
        case sym: TermSymbol => S(sym)
        case sym: BlockMemberSymbol => sym.tsym
        case _ => N
      field.foreach: sym =>
        if !sym.isErased then sym.erasedType = p.sym.erasedType
    statements.foreach:
      case td: TermDefinition if !td.tsym.isErased => td.tsym.erasedType = definitionType(td)
      case _ => ()
    statements.foreach:
      case LetDecl(sym: TermSymbol, _) if !sym.isErased => sym.erasedType = N
      case _ => ()
    completed = S(root)

object Erasure:
  /** Prelude declarations use the same pass even though they have no executable program. */
  def apply(root: Statement)(using Config, Ctx, State): Erasure =
    val erasure = new Erasure
    erasure.run(root)
    erasure
