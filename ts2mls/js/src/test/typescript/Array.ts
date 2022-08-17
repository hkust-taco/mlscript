function first(x: string[]) {
  return x[0];
}

function getZero3() : number[] {
  return [0, 0, 0];
}

function first2(fs: ((x: number) => number)[]): ((x: number) => number) {
  return fs[0];
}

enum E {
  E, EE, EEE
}

function doEs(e: E[]): E[] {
  return e;
}

class C {}
interface I {i: number}

function doCs(c: C[]): C[] {
  return c;
}

function doIs(i: I[]): I[] {
  return i;
}

function inter<U, T>(x: (U & T)[]): (U & T)[] {
  return x;
}

function clean(x: [string, number][]): [string, number][] {
  return [];
}

function translate<T, U>(x: T[]): U[] {
  return []; // TODO:
}

function uu(x: (number | boolean)[]): (number | boolean)[] {
  return x;
}

class Temp<T> {
  x: T
}

function ta(ts: Temp<boolean>[]): Temp<boolean>[] {
  return [];
}

function tat<T>(ts: Temp<T>[]): Temp<T>[] {
  return [];
}