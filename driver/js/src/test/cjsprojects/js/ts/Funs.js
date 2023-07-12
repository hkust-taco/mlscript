"use strict";
function f(x, y) {
    return x + y;
}
function g(x) {
    return f(x, x);
}
function h() {
    return g(42);
}
module.exports = h;
