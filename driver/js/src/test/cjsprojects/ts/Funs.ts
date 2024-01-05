function f(x: number, y: number) {
  return x + y;
}

function g(x: number) {
  return f(x, x);
}

function h() {
  return g(42);
}

export = h;
