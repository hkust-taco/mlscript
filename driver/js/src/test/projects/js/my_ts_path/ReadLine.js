const lines = [
    "Admin", "1", "y", "4", "n"
];
let i = 0;
export function getStrLn() {
    return lines[i++];
}
export function putStrLn(str) {
    console.log(str);
}
// TODO: Option
export function parse(s) {
    const i = +s;
    return isNaN(i) || i % 1 !== 0 ? -1 : i;
}
