interface IFoo {
  a: string
  b: (x: number) => number
  c: () => boolean
  /**
   * @debug
   */
  d: (x: string) => void
}

interface II<T extends number> {
  test: (x: T) => number
}

function create() {
  return {v: 114};
}

function get(x: {t: string}): string {
  return x.t;
}

interface IEvent {
  callback(this: IEvent): (x: number) => void;
}

interface SearchFunc {
  (source: string, subString: string): boolean;
}

interface StringArray {
  [index: number]: string;
}

interface Counter {
  (start: number): string;
  interval: number;
  reset(): void;
}

interface Simple {
  a: number
  b: (x: boolean) => string
}

interface Simple2<T extends number> {
  abc: T
}

interface Next extends Simple {}

interface TTT<T> {
  ttt: (x: T) => T
}