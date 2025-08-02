import Predef from "./Predef.mjs";

const RuntimeJS = {
  try_catch(computation, onError) {
    try { return computation() }
    catch (error) { return onError(error) }
  },
  symbols: {
    constructorName: Symbol.for("mlscript.constructorName"),
    fieldNames: Symbol.for("mlscript.fieldNames"),
    definitionKind: Symbol.for("mlscript.definitionKind"),
  }
}

export default RuntimeJS;

