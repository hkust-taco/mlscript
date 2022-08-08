class Student {
  name: string

  constructor() {}

  getID() { return 114514; }
  addScore(sub: string, score: number) {}
  isFriend(other: Student) { return true; }

  private a: number
  protected b: string
}

class Foo<T extends Student> {
  constructor() {}

  bar(x: T) {}
}

class EZ {
  inc(x: number) {
    return x + 1;
  }

  private foo() {}
  protected bar: undefined
}