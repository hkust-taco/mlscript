package hkmc2


extension [A](a: A)
  inline def in[R](k: A ?=> R) = k(using a)



