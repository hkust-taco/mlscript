import { stringify } from "json5";

export function generate(outDir: string) {
  const json = {
    "compilerOptions": {
      "outDir": outDir
    }
  }

  return stringify(json);
}
