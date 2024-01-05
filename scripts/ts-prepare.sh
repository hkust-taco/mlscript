#!/usr/bin/env bash

echo "install typescript and json5 for mlscript..."
npm ci
chmod 777 ./node_modules/typescript/bin/tsc

cd driver/js/src/test/cjsprojects
echo "install ts libraries for driver cjsprojects test..."
npm ci
echo "compile ts files for driver cjsprojects test..."
../../../../../node_modules/typescript/bin/tsc

cd ../esprojects
echo "install ts libraries for driver esprojects test..."
npm ci
echo "compile ts files for driver esprojects test..."
../../../../../node_modules/typescript/bin/tsc
