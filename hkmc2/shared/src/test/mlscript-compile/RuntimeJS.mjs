
const RuntimeJS = {
  try_catch(computation, onError) {
    try { return computation() }
    catch (error) { return onError(error) }
  }
}

export default RuntimeJS;

