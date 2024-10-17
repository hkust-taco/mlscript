package hkmc2


extension [A](a: A)
  infix inline def givenIn[R](inline k: A ?=> R) = k(using a)



