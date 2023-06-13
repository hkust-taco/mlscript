import * as ReadLine from "../my_ts_path/ReadLine.js"

import { Concat } from "./tools/Concat.js"

const MLS2TheMax = new class MLS2TheMax {
  #Game;
  constructor() {
  }
  ask(question) {
    return ((() => {
      ReadLine.putStrLn(question);
      return ReadLine.getStrLn();
    })());
  }
  get main() {
    const self = this;
    return ((() => {
      let name = self.ask("What is your name?");
      ReadLine.putStrLn(Concat.concat3("Hello, ", name, " welcome to the game!"));
      return self.Game(name).loop;
    })());
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
            return ans === "y" === true ? self.loop : ReadLine.putStrLn("Bye!");
          })());
        }
        get loop() {
          const name = this.#name;
          const self = this;
          return ((() => {
            let guess = outer.ask(Concat.concat3("Dear ", name, ", please guess a number from 1 to 5"));
            ReadLine.parse(guess) == self.number === true ? ReadLine.putStrLn(Concat.concat2("You guessed right, ", name)) : ReadLine.putStrLn(Concat.concat2("You guessed wrong, ", name));
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
