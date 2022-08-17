function extend<T, U>(first: T, second: U): T & U {
  let result = <T & U>{};
  return result;
}

function foo<T, U>(x: T & U) {
  console.log(x)
}

function over(f: ((x: number) => string) & ((x: object) => string)): string {
  return f(42);
}

interface IA{
  x: number
}

interface IB{
  y: number
}

function iii(x: IA & IB): IA & IB {
  return x;
}

function uu<U, V, T, P>(x: (U | V) & (T | P)): (U | V) & (T | P) {
  return x;
}

function iiii<U, T, V>(x: U & (T & V)): U & (T & V) {
  return x;
}

function arr<U, T>(a: U[] & T[]): U[] & T[] {
  return a;
}

function tt<U, T, V>(x: [U, T] & [V, V]): [U, T] & [V, V] {
  return x;
}

class A{}
class B{}

function inter(c: A & B): A & B {
  return c;
}