decalre function getName(id: number | string): string
declare function render(callback?: ()=>void): string

declare interface Get{
  (id: string): string
}

declare class Person {
  constructor(name: string, age: number)
  getName(id: number): string 
}

declare namespace OOO{
}
