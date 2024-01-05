function concat(x, y) {
  if (arguments.length === 2) {
    return x + y;
  } else {
    return (y) => x + y;
  }
}
export const Concat = new class Concat {
  constructor() {
  }
  concat2(s1, s2) {
    return concat(s1)(s2);
  }
  concat3(s1, s2, s3) {
    const qualifier = this;
    return qualifier.concat2(qualifier.concat2(s1, s2), s3);
  }
  $init() {}
};
Concat.$init();
