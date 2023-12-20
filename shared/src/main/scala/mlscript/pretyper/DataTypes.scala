package mlscript.pretyper

import mlscript.{NuFunDef, NuTypeDef, Cls, Trt, Mxn, Als, Mod, Var, TypeName}
import collection.mutable.{Buffer, Map => MutMap, Set => MutSet}
import mlscript.utils._, shorthands._
import scala.annotation.tailrec

trait DataTypes { self: PreTyper =>

}