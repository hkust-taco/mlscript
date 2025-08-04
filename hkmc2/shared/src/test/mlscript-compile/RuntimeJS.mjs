import Predef from "./Predef.mjs";

const RuntimeJS = {
  try_catch(computation, onError) {
    try { return computation() }
    catch (error) { return onError(error) }
  },
  short_and(lhs, rhs) {
    return lhs && rhs();
  },
  short_or(lhs, rhs) {
    return lhs || rhs();
  }
}

export default RuntimeJS;

