function getString(x: string | number | boolean): string {
  return x.toString()
}

function test(x: boolean): (string | number) {
  if (x) return "foo";
  else return 42;
}

function run(f: ((x: number) => number) | ((x: number) => string)): any {
  return f(42);
}

function get(arr: number[] | string[]) {
  console.log(arr[0])
}

function get2(t: [string, string] | [number, string]): string {
  return t[1];
}

function typeVar<T, U>(x: T | U): T | U {
  return x
}