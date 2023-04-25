export namespace Foo {
  interface IBar {
    a: string
  }

  export class Bar implements IBar {
    a = "bar"
  }

  export function Baz(aa: string): IBar {
    return {
      a: aa
    }
  }

  export const baz = Baz("baz")
}
