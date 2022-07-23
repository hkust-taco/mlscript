package mlscript.mono

import mlscript.TypingUnit
import mlscript.NuTypeDef
import mlscript.NuFunDef
import scala.collection.mutable.ArrayBuffer
import mlscript.NuDecl
import mlscript.Term
import mlscript.TypeName
import mlscript.Var

// Flatten nested classes.
object ClassLifter
