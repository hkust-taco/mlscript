namespace N1 {
  export function f(x) {
    return 42;
  }

  function ff(y) {
    return 42;
  }

  export class C {
    f() {}
  }

  interface I {
    f: () => number
  }

  export namespace N2 {
    export function fff(x: boolean) {
      return 42;
    }
  }
}