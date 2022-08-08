function extend<T, U>(first: T, second: U): T & U {
  let result = <T & U>{};
  return result;
}

function foo<T, U>(x: T & U) {
  console.log(x)
}