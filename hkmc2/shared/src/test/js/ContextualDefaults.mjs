export default {
  run(x = 42) { return _n => x; },
  rest(x = 42, ...xs) { return _n => [x, xs]; },
};
