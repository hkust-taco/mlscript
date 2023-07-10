class Baz {
  #times
  constructor(t: number) {
    this.#times = t;
  }

  baz() {
    for (let i = 0; i < this.#times; ++i) {
      console.log("baz")
    }
  }
}

export = {
  Baz: Baz
}
