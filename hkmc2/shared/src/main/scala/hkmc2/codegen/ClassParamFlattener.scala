package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


/** Flattens class constructor parameter lists in the Block IR.
  *
  * Instantiations are saturated by the time this pass runs, so every
  * `Instantiate` can be rewritten without consulting the class definition.
  * Source-level constructor wrapper functions keep their original calling
  * convention, which matters for external code and module imports.
  * Argument spreads are intentionally preserved as `Arg`s while only the
  * surrounding argument-list boundary is removed.
  */
class ClassParamFlattener extends BlockTransformer(SymbolSubst.Id):
  
  private def flattenParamLists(paramss: Ls[ParamList]): ParamList =
    val flags = paramss.headOption.fold(ParamListFlags.empty)(_.flags)
    val (init, last) = paramss.splitAt(paramss.length - 1)
    val params = init.flatMap(_.allParams) ::: last.flatMap(_.params)
    ParamList(flags, params, last.flatMap(_.restParam).headOption)
  
  private def flattenClsParams(cls: ClsLikeDefn): ClsLikeDefn =
    val paramss = cls.paramsOpt.toList ::: cls.auxParams
    if paramss.lengthCompare(1) > 0 then
      cls.copy(paramsOpt = N, auxParams = flattenParamLists(paramss) :: Nil)(
        cls.configOverride,
        cls.annotations,
      )
    else
      cls
  
  override def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block): Block =
    super.applyClsLikeDefn(defn):
      case cls: ClsLikeDefn => k(flattenClsParams(cls))
      case defn => k(defn)
  
  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case inst @ Instantiate(mut, cls, argss) =>
      applyPath(cls): cls2 =>
        applyArgss(argss): argss2 =>
          val flatArgss =
            if argss2.lengthCompare(1) > 0 then argss2.flatten :: Nil
            else argss2
          k:
            if (cls2 is cls) && (flatArgss is argss) then inst
            else Instantiate(mut, cls2, flatArgss).withLocOf(inst)
    case _ =>
      super.applyResult(r)(k)
  
end ClassParamFlattener

object ClassParamFlattener:
  def apply(program: Program): Program =
    new ClassParamFlattener().applyProgram(program)
  
  def apply(block: Block): Block =
    new ClassParamFlattener().applyBlock(block)
