export class DatePrint {
    constructor(p) {
        this.prefix = p;
    }
    print(msg) {
        let date = new Date(1145141919810);
        console.log(`[${this.prefix}] ${msg}. (${date.toLocaleString("en-US", { timeZone: "America/New_York" })})`);
    }
}
