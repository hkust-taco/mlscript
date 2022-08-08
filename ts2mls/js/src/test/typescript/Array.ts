function first(x: string[]) {
  return x[0];
}

function getZero3() : number[] {
  return [0, 0, 0];
}

function first2(fs: ((x: number) => number)[]): ((x: number) => number) {
  return fs[0];
}