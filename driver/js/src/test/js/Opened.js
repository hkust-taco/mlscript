function log(x) {
  return console.info(x);
}
const hello = (x) => log([
  "hello!",
  x
]);
export {hello}
