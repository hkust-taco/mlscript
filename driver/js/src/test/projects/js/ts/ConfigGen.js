"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.generate = void 0;
var json5_1 = require("json5");
function generate(outDir) {
    var json = {
        "compilerOptions": {
            "outDir": outDir
        }
    };
    return (0, json5_1.stringify)(json);
}
exports.generate = generate;
