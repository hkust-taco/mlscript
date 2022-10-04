interface None {
  readonly _tag: 'None'
}

interface Some<A> {
  readonly _tag: 'Some'
  readonly value: A
}

type Option<A> = None | Some<A>
type Func = (x: number) => number
type S2 = [string, string]

interface I1 {}
interface I2 {}

type I3 = I1 & I2
type StringArray = string[]
type SomeInterface = { x: number, y: number }
