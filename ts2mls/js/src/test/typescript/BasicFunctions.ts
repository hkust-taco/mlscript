function hello() {
  console.log("hello")
}

function add(x: number, y: number): number {
  return x + y
}

function sub(x: number, y: number) {
  return x - y
}

function foo() {
  return 42;
}

function id(x) {
  return x;
}

function odd(x: number) {
  return (x % 2) !== 0;
}

function isnull(x) {
  return x == null;
}

function bar() {
  return undefined;
}

function nu(n: null): null {
  return n;
}

function un(n: undefined): undefined {
  return n;
}

function fail() : never {
  throw new Error("wuwuwu");
}

function create(): object {
  return {v: 0};
}

function pa(x: ((number))): number {
  return x + 42;
}

function wtf(x: unknown) {}