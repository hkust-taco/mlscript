import * as ReadLine from "../my_ts_path/ReadLine.js"

import { Concat } from "./tools/Concat.js"

const MLS2TheMax = new class MLS2TheMax {
  #Some;
  #None;
  #Game;
  constructor() {
  }
  ask(question) {
    return ((() => {
      console.log(question);
      return ReadLine.getStrLn();
    })());
  }
  parse(s) {
    const self = this;
    return ((() => {
      let i = parseInt(s);
      return isNaN(i) === true ? self.None() : self.Some(i);
    })());
  }
  get main() {
    const self = this;
    return ((() => {
      let name = self.ask("What is your name?");
      console.log(Concat.concat3("Hello, ", name, " welcome to the game!"));
      return self.Game(name).loop;
    })());
  }
  get Some() {
    const outer = this;
    if (this.#Some === undefined) {
      class Some {
        #value;
        get value() { return this.#value; }
        constructor(value) {
          this.#value = value;
        }
      };
      this.#Some = ((value) => Object.freeze(new Some(value)));
      this.#Some.class = Some;
    }
    return this.#Some;
  }
  get None() {
    const outer = this;
    if (this.#None === undefined) {
      class None {};
      this.#None = (() => Object.freeze(new None()));
      this.#None.class = None;
    }
    return this.#None;
  }
  get Game() {
    const outer = this;
    if (this.#Game === undefined) {
      class Game {
        #name;
        get name() { return this.#name; }
        #number;
        get number() { return this.#number; }
        constructor(name) {
          this.#name = name;
          this.#number = 4;
          const number = this.#number;
        }
        get shouldContinue() {
          const name = this.#name;
          const self = this;
          return ((() => {
            let ans = outer.ask("Do you want to continue?");
            return ans === "y" === true ? self.loop : console.log("Bye!");
          })());
        }
        check(x) {
          const name = this.#name;
          const self = this;
          return ((() => {
            return x == self.number === true ? console.log(Concat.concat2("You guessed right, ", name)) : console.log(Concat.concat2("You guessed wrong, ", name));
          })());
        }
        get loop() {
          const name = this.#name;
          const self = this;
          return ((() => {
            let guess = outer.ask(Concat.concat3("Dear ", name, ", please guess a number from 1 to 5"));
            ((tmp0) => tmp0 instanceof outer.Some.class ? ((i) => self.check(i))(tmp0.value) : console.log("Not a number!"))(outer.parse(guess));
            return self.shouldContinue;
          })());
        }
      };
      this.#Game = ((name) => Object.freeze(new Game(name)));
      this.#Game.class = Game;
    }
    return this.#Game;
  }
  $init() {
    const self = this;
    self.main;
  }
};
MLS2TheMax.$init();
