const lines = [
  "Admin", "1", "y", "4", "n"
]

let i = 0

export function getStrLn(): string {
  return lines[i++];
}

export function putStrLn(str: string): void {
  console.log(str);
}

// TODO: Option
export function parse(s: string) {
  const i = +s
  return isNaN(i) || i % 1 !== 0 ? -1 : i
}
