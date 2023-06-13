const lines = [
  "Admin", "1", "y", "foo", "y", "4", "n"
]

let i = 0

export function getStrLn(): string {
  return lines[i++];
}
