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

export default function id(x) {
  return x;
}

class E {}

export { E }
export { E as F }
export { B as G } from "./Dependency"
export * as H from "./Dependency"

