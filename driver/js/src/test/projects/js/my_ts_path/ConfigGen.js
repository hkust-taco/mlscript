import json5 from "json5";
export function generate(outDir) {
    const json = {
        "compilerOptions": {
            "outDir": outDir
        }
    };
    return json5.stringify(json);
}
