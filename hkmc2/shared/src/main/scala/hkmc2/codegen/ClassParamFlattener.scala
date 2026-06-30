package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*

import hkmc2.semantics.Elaborator.State


/** Flattens class constructor parameter lists in the Block IR.
  *
  * After this pass, every `ClsLikeDefn` is normalized so that
  * `paramsOpt` is `N` and `auxParams` contains exactly one `ParamList`
  * (which may be empty for parameterless classes).
  *
  * Instantiations are saturated by the time this pass runs, so every
  * `Instantiate` can be rewritten without consulting the class definition.
  * Source-level constructor wrapper functions keep their original calling
  * convention when they are used partially. Saturated calls to curried class
  * wrappers are lowered to instantiations, matching the `new` path without
  * paying for the curried wrapper at runtime.
  * Argument spreads are intentionally preserved as `Arg`s while only the
  * surrounding argument-list boundary is removed.
  */
class ClassParamFlattener(using State) extends BlockTransformer(SymbolSubst.Id):
  
  private def flattenParamLists(paramss: Ls[ParamList]): ParamList =
    val flags = paramss.headOption.fold(ParamListFlags.empty)(_.flags)
    val (init, last) = paramss.splitAt(paramss.length - 1)
    val params = init.flatMap(_.allParams) ::: last.flatMap(_.params)
    ParamList(flags, params, last.flatMap(_.restParam).headOption)
  
  /** Normalize class params so that `paramsOpt = N` and `auxParams` has exactly one element. */
  private def flattenClsParams(cls: ClsLikeDefn): ClsLikeDefn =
    val paramss = cls.paramsOpt.toList ::: cls.auxParams
    val flatAux = paramss match
      case Nil => PlainParamList(Nil)
      case single :: Nil => single
      case _ => flattenParamLists(paramss)
    cls.copy(paramsOpt = N, auxParams = flatAux :: Nil)(
      cls.configOverride,
      cls.annotations,
    )
  
  private def classPathFor(fun: Path, cls: ClassSymbol): Opt[Path] = fun match
    case Value.MemberRef(bms, _) => S(bms.asMemberRef(cls))
    case s @ Select(qual, name) => S(Select(qual, name)(S(cls))(s.sanitize))
    case _ => N

  private def saturatedCurriedClassCall(fun: Path, argss: NELs[Ls[Arg]]): Opt[Path] =
    fun.targetSymbol.collect:
      case sym: TermSymbol => sym
    .flatMap: sym =>
      sym.defn.flatMap: td =>
        td.sym.asCls.flatMap: cls =>
          cls.defn.collect:
            case defn =>
              defn.paramsOpt.toList ::: defn.auxParams
          .flatMap:
            case paramss if paramss.lengthCompare(1) > 0 && argss.lengthCompare(paramss.length) == 0 =>
              classPathFor(fun, cls)
            case _ => N

  override def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block): Block =
    super.applyClsLikeDefn(defn):
      case cls: ClsLikeDefn => k(flattenClsParams(cls))
      case defn => k(defn)
  
  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case c @ Call(r @ Value.RefLike(State.superSymbol), argss) =>
      applyArgss(argss): argss2 =>
        val flatArgss =
          if argss2.lengthCompare(1) > 0 then argss2.flatten ne_:: Nil
          else argss2
        k:
          if flatArgss is argss then c
          else Call(r, flatArgss)(c.metadata).withLocOf(c)
    case call @ Call(fun, argss) =>
      saturatedCurriedClassCall(fun, argss) match
      case S(cls) =>
        applyPath(cls): cls2 =>
          applyArgss(argss): argss2 =>
            val flatArgss =
              if argss2.lengthCompare(1) > 0 then argss2.flatten ne_:: Nil
              else argss2
            k(Instantiate(false, cls2, flatArgss)(InstantiateMetadata(call.metadata.annotations)).withLocOf(call))
      case N =>
        super.applyResult(r)(k)
    case inst @ Instantiate(mut, cls, argss) =>
      applyPath(cls): cls2 =>
        applyArgss(argss): argss2 =>
          val flatArgss =
            if argss2.lengthCompare(1) > 0 then argss2.flatten :: Nil
            else argss2
          k:
            if (cls2 is cls) && (flatArgss is argss) then inst
            else Instantiate(mut, cls2, flatArgss)(inst.metadata).withLocOf(inst)
    case _ =>
      super.applyResult(r)(k)
  
end ClassParamFlattener

object ClassParamFlattener:
  def apply(program: Program)(using State): Program =
    new ClassParamFlattener().applyProgram(program)
  
  def apply(block: Block)(using State): Block =
    new ClassParamFlattener().applyBlock(block)
