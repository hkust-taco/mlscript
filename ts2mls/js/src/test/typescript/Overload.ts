function f(x: number): string;
function f(x: string): string;

function f(x) {
  if (typeof x == "number") return "42";
  else return "->" + x;
}

class M {
  foo(x: number): string;
  foo(x: string): string;

  foo(x): string {
    return x.toString();
  }
}

function app(f: (x: string) => void, x: number): void;
function app(f: (x: string) => void, x: string): void;

function app(f, x): void {
  f(x.toString())
}

function create(x: number): () => boolean;
function create(x: boolean): () => boolean;

function create(x): () => boolean {
  return function() { return x == 0; }
}

function g0(x: string[]): string;
function g0(x: object[]): string;

function g0(x): string {
  return x[0].toString();
}

function db(x: number): number[];
function db(x: object): number[];

function db(x): number[] {
  return [0, 1];
}

class N {}

function id(x: M): void;
function id(x: N): void;

function id(x) {}

function tst(x: {z: number}): {y: string};
function tst(x: {z: boolean}): {y: string};

function tst(x): {y: string} {
  return {y: x.z.toString()}
}

function op(x: number, y?: number): void;
function op(x: number, y?: boolean): void;

function op(x, y): void {}

function swap(x: [number, string]): [string, number];
function swap(x: [string, number]): [number, string];

function swap(x) {
  return [x[1], x[0]];
}

function u(x: number | boolean): string;
function u(x: object): string;

function u(x): string {
  return x.toString();
}

function doSome<T, U>(x: T & U): never;
function doSome<T, U>(x: string): never;

function doSome<T, U>(x): never {
  while (true);
}

namespace XX {
  export function f<T>(x: T, n: number): string;
  export function f<T>(x: T, n: boolean): string;

  export function f<T>(x: T, n): string {
    return "";
  }
}

class WWW {
  F<T>(x: string): T;
  F<T>(x: number): T;

  F<T>(x: T): T {
    return null;
  }
}

function baz<T>(): T;
function baz<U, T>(): U;
function baz<U, T, P>(): P;
function baz() {
  return null;
}
