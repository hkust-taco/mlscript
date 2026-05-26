package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import hkmc2.utils.*

import semantics.*


/** Flattens class constructor parameter lists in the Block IR.
  *
  * Instantiations are saturated by the time this pass runs, so every
  * `Instantiate` can be rewritten without consulting the class definition.
  * Statically resolved calls to source class constructor wrappers are flattened
  * in the same way, so the JS wrapper can have one flat parameter list too.
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
    cls.paramsOpt match
    case S(params) if cls.auxParams.nonEmpty =>
      val paramss = params :: cls.auxParams
      cls.copy(paramsOpt = S(flattenParamLists(paramss)), auxParams = Nil)(
        cls.configOverride,
        cls.annotations,
      )
    case _ =>
      cls
  
  private def shouldFlattenClassCtorCall(fun: Path): Bool =
    fun.targetSymbol.exists:
      case sym: TermSymbol =>
        sym.defn.exists: td =>
          td.companionClass.exists: cls =>
            cls.defn.exists(defn => defn.paramsOpt.isDefined && defn.auxParams.nonEmpty)
      case _ => false
  
  override def applyClsLikeDefn(defn: ClsLikeDefn)(k: Defn => Block): Block =
    super.applyClsLikeDefn(defn):
      case cls: ClsLikeDefn => k(flattenClsParams(cls))
      case defn => k(defn)
  
  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case call @ Call(fun, argss) if shouldFlattenClassCtorCall(fun) =>
      applyPath(fun): fun2 =>
        applyArgss(argss): argss2 =>
          val flatArgss =
            if argss2.lengthCompare(1) > 0 then argss2.flatten ne_:: Nil
            else argss2
          k:
            if (fun2 is fun) && (flatArgss is argss) then call
            else Call(fun2, flatArgss)(call.isMlsFun, call.mayRaiseEffects, call.explicitTailCall).withLocOf(call)
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
