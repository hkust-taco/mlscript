import * as ReadLine from "../my_ts_path/ReadLine.js"

import { Concat } from "./tools/Concat.js"

const MLS2TheMax = new class MLS2TheMax {
  #Some;
  #Game;
  #None;
  constructor() {
  }
  ask(question) {
    return ((() => {
      console.log(question);
      return ReadLine.getStrLn();
    })());
  }
  parse(s) {
    const qualifier = this;
    return ((() => {
      let i = parseInt(s, undefined);
      return isNaN(i) === true ? qualifier.None : qualifier.Some(i);
    })());
  }
  get main() {
    const qualifier = this;
    return ((() => {
      let name = qualifier.ask("What is your name?");
      console.log(Concat.concat3("Hello, ", name, " welcome to the game!"));
      return qualifier.Game(name).loop;
    })());
  }
  get None() {
    const qualifier = this;
    if (this.#None === undefined) {
      class None {}
      this.#None = new None();
      this.#None.class = None;
    }
    return this.#None;
  }
  get Some() {
    const qualifier = this;
    if (this.#Some === undefined) {
      class Some {
        #value;
        constructor(value) {
          this.#value = value;
        }
      static
        unapply(x) {
          return [x.#value];
        }
      };
      this.#Some = ((value) => Object.freeze(new Some(value)));
      this.#Some.class = Some;
      this.#Some.unapply = Some.unapply;
    }
    return this.#Some;
  }
  get Game() {
    const qualifier = this;
    if (this.#Game === undefined) {
      class Game {
        #number;
        #name;
        constructor(name) {
          this.#name = name;
          this.#number = 4;
          const number = this.#number;
        }
        get shouldContinue() {
          const name = this.#name;
          const qualifier1 = this;
          return ((() => {
            let ans = qualifier.ask("Do you want to continue?");
            return ans === "y" === true ? qualifier1.loop : console.log("Bye!");
          })());
        }
        check(x) {
          const name = this.#name;
          const qualifier1 = this;
          return ((() => {
            return x == qualifier1.#number === true ? console.log(Concat.concat2("You guessed right, ", name)) : console.log(Concat.concat2("You guessed wrong, ", name));
          })());
        }
        get loop() {
          const name = this.#name;
          const qualifier1 = this;
          return ((() => {
            let guess = qualifier.ask(Concat.concat3("Dear ", name, ", please guess a number from 1 to 5"));
            ((tmp0) => tmp0 instanceof qualifier.Some.class ? (([i]) => qualifier1.check(i))(qualifier.Some.unapply(tmp0)) : console.log("Not a number!"))(qualifier.parse(guess));
            return qualifier1.shouldContinue;
          })());
        }
      static
        unapply(x) {
          return [x.#name];
        }
      };
      this.#Game = ((name) => Object.freeze(new Game(name)));
      this.#Game.class = Game;
      this.#Game.unapply = Game.unapply;
    }
    return this.#Game;
  }
  $init() {
    const qualifier = this;
    qualifier.main;
  }
};
MLS2TheMax.$init();
