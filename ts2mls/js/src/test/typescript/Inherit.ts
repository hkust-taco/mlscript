class A {
  constructor() {}

  foo() {
      console.log("foo")
  }
}

class B extends A {}

class C<T> {
  constructor() {}

  private t: T

  set(x: T) { this.t = x; }
  get() { return this.t; } 
}

class D extends C<number> {
}

interface Wu {
  x: boolean
}

class WuWu extends Wu {
  y: boolean
}

interface WuWuWu extends WuWu {
  z: boolean
}

interface Never extends WuWuWu {
  w: () => never
}

class VG<T> {
  x: T
}

class Home<T> extends VG<string> {
  y: T
}

interface O<I> {
  xx: (x: I) => I
}

class OR<R> implements O<R> {
  xx(x: R): R {
    return x;
  }
}

namespace Five {
  export class ROTK {
    wu: string
  }

  export class Y extends Five.ROTK {}
}

class Y extends Five.ROTK {}