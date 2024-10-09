package hkmc2


extension [A](a: A)
  infix inline def givenIn[R](k: A ?=> R) = k(using a)



