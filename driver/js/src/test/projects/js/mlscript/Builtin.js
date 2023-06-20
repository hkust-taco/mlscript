const Builtin = new class Builtin {
  #s;
  get s() { return this.#s; }
  #n;
  get n() { return this.#n; }
  constructor() {
  }
  $init() {
    this.#s = "abc";
    const s = this.#s;
    this.#n = 42;
    const n = this.#n;
    console.log(s.charAt(1));
    console.log(s.indexOf("c", undefined));
    console.log(String.fromCharCode(64));
    console.log(n.toString(8));
  }
};
Builtin.$init();
