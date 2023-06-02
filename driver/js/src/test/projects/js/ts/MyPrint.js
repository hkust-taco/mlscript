"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.DatePrint = void 0;
var DatePrint = /** @class */ (function () {
    function DatePrint(p) {
        this.prefix = p;
    }
    DatePrint.prototype.print = function (msg) {
        var date = new Date(1145141919810);
        console.log("[".concat(this.prefix, "] ").concat(msg, ". (").concat(date, ")"));
    };
    return DatePrint;
}());
exports.DatePrint = DatePrint;
