const Builtin = new class Builtin {
  constructor() {
  }
  $init() {
    const s = "abc";
    const n = 42;
    console.log(s.charAt(1));
    console.log(s.indexOf("c", undefined));
    console.log(String.fromCharCode(64));
    console.log(n.toString(8));
    console.log(Number["MAX_VALUE"]);
    console.log(s.hasOwnProperty("foo"));
    console.log(Math.PI);
  }
};
Builtin.$init();
