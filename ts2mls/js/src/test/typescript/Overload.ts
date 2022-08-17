function f(x: number): number;
function f(x: string): string;

function f(x) {
  if (typeof x == "number") return x + 42;
  else return "->" + x;
}

class M {
  foo(x: number): number;
  foo(x: string): string;

  foo(x) {
    return x;
  }
}

function app(f: (x: number) => void, x: number): void;
function app(f: (x: string) => void, x: string): void;

function app(f, x): void {
  f(x)
}

function create(x: number): () => number;
function create(x: boolean): () => boolean;

function create(x) {
  return function() { return x; }
}

function g0(x: string[]): string;
function g0(x: object[]): object;

function g0(x) {
  return x[0];
}

function db(x: number): number[];
function db(x: object): object[];

function db(x) {
  return [x, x];
}

class N {}

function id(x: M): M;
function id(x: N): N;

function id(x) { return x; }

id({foo: function(x: boolean): void {}}) // it works

function tst(x: {z: number}): {y: string};
function tst(x: {z: boolean}): {y: string};

function tst(x) {
  return {y: x.z.toString()}
}

function op(x: number, y?: number): void;
function op(x: number, y?: boolean): void;

function op(x, y) {}

function swap(x: [number, string]): [string, number];
function swap(x: [string, number]): [number, string];

function swap(x) {
  return [x[1], x[0]];
}

function u(x: number | boolean): string;
function u(x: object): string | object;

function u(x) {
  return x.toString();
}

function doSome<T, U>(x: T & U): T & U;
function doSome<T, U>(x: string): never;

function doSome<T, U>(x) {
  if (typeof x == "string") {
    while (true);
  }
  else {
    return x;
  }
}

class G<T> {
  g: T
}

function bar(x: G<string>): G<string>;
function bar(x: G<number>): G<number>;
function bar(x: G<boolean>): G<boolean>;

function bar(x) {
  return x;
}

namespace XX {
  export function f<T>(x: T, n: number): string;
  export function f<T>(x: T, n: boolean): string;

  export function f<T>(x, n) {
    return "";
  }
}