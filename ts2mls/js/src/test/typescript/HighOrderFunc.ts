function h1(inc: (n: number) => number, num: number) {
  return inc(num)
}

function h2(hint: string) {
  return function() {
    return "hint: " + hint
  }
}

function h3(f: (x: number) => number, g: (x: number) => number) {
  return function(x: number) {
    return f(g(x))
  }
}