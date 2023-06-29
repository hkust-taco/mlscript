export class DatePrint {
  private prefix: string
  constructor(p: string) {
    this.prefix = p
  }

  print(msg: string) {
    let date = new Date(1145141919810)
    console.log(`[${this.prefix}] ${msg}. (${date.toLocaleString("en-US", { timeZone: "America/New_York" })})`)
  }
}
