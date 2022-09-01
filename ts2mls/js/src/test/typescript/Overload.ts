function f(x: number): string;
function f(x: string): string;

function f(x) {
  if (typeof x == "number") return "42";
  else return "->" + x;
}

class M {
  foo(x: number): string;
  foo(x: string): string;

  foo(x) {
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

function create(x) {
  return function() { return x == 0; }
}

function g0(x: string[]): string;
function g0(x: object[]): string;

function g0(x) {
  return x[0].toString();
}

function db(x: number): number[];
function db(x: object): number[];

function db(x) {
  return [0, 1];
}

class N {}

function id(x: M): void;
function id(x: N): void;

function id(x) {}

function tst(x: {z: number}): {y: string};
function tst(x: {z: boolean}): {y: string};

function tst(x) {
  return {y: x.z.toString()}
}

function op(x: number, y?: number): void;
function op(x: number, y?: boolean): void;

function op(x, y) {}

function swap(x: [number, string]): [number, string];
function swap(x: [string, number]): [number, string];

function swap(x) {
  return [x[1], x[0]];
}

function u(x: number | boolean): string;
function u(x: object): string;

function u(x) {
  return x.toString();
}

function doSome<T, U>(x: T & U): never;
function doSome<T, U>(x: string): never;

function doSome<T, U>(x) {
  while (true);
}

namespace XX {
  export function f<T>(x: T, n: number): string;
  export function f<T>(x: T, n: boolean): string;

  export function f<T>(x, n) {
    return "";
  }
}

class WWW {
  F<T>(x: string): T;
  F<T>(x: number): T;

  F<T>(x) {
    return null;
  }
}