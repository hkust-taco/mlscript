export default {
  run(x = 42) { return _n => x; },
  rest(x = 42, ...xs) { return _n => [x, xs]; },
  pair(first, second = 42) { return _n => [first, second, arguments.length]; },
  trailing(...args) {
    const last = args.pop();
    const [x = 42, ...middle] = args;
    return _n => [x, middle, last];
  },
  curried(x = 42) { return _n => (y = 43) => _s => [x, y]; },
};
