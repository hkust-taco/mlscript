function buildName(firstName: string, lastName?: string) {
  return firstName + lastName;
}

function buildName2(firstName: string, lastName = "DIO") {
  return firstName + lastName;
}

function buildName3(firstName: string, ...lastName) {
  console.log(lastName)
  return firstName;
}

interface SquareConfig {
  color?: string;
  width?: number;
}

function did(x: number, f?: (x: number) => number): number {
  if (f === undefined) return x;
  else return f(x);
}

function getOrElse(arr?: object[]): object {
  if (arr === undefined) return {};
  else return arr[0];
}

class ABC {}
function testABC(abc?: ABC) {}

function testSquareConfig(conf?: SquareConfig) {}

function err(msg?: [number, string]): void {
  if (msg === undefined) return;
  else throw msg;
}

function toStr(x?: number | boolean): string {
  if (x === undefined) return "undefined";
  else return x.toString();
}

function boo<T, U>(x?: T & U) {}

class B<T> {}

function boom(b?: B<never>): any {}