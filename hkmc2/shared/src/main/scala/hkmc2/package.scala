package hkmc2


extension [A](a: A)
  infix inline def givenIn[R](inline k: A ?=> R) = k(using a)


// * Valid identifiers for the members of module and class-like definitions
// * Importantly, these are the same as valid JavaScript identifiers,
// * so we do not check them in JS code-generation.
val identifierPattern: scala.util.matching.Regex = "^[A-Za-z_$][A-Za-z0-9_$]*$".r


