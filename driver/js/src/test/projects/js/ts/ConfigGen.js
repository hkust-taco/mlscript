import { stringify } from "json5";
export function generate(outDir) {
    const json = {
        "compilerOptions": {
            "outDir": outDir
        }
    };
    return stringify(json);
}
