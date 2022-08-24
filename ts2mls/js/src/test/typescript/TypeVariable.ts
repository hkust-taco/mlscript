function inc<T extends number>(x: T) {
  return x + 1
}

class CC<T extends string> {
  constructor() {}

  print(s: T) { console.log(s) }
}

function con<U, T extends U>(t: T): U {
  return t;
}

class Printer<T> {
  constructor() {}

  print(t: T) { console.log(t) }
}

function setStringPrinter(p: Printer<string>) {}

function getStringPrinter(): Printer<string> { return new Printer<string>(); }

function foo<T>(p: Printer<T>, x: T): T {
  return null;
}

// TODO: `extends` is still not supported yet.
function foo2<T extends number[]>(p: Printer<T>, x: T): T {
  return null;
}

class F<T> {
  x: T

  GG<U>(y: U): T {
    return this.x;
  }
}

interface I<T> {
  x: T
  GG<U>(y: U): T
}

class FFF<T> {
  constructor() {}
  fff(x: T) {}
}

function fff(p: FFF<string>, s: string) {
  p.fff(s);
}

function getFFF(): FFF<number> {
  return new FFF<number>();
}