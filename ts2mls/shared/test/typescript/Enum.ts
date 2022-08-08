enum Color {Red, Yellow, Green}

function pass(c: Color): boolean {
  return c == Color.Green;
}

function stop(): Color {
  return Color.Red;
}