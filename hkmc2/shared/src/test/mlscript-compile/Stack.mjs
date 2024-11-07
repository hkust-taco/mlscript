const Stack = new class Stack {
  constructor() {
    this.Cons = class Cons {
      constructor(head, tail) {
        this.head = head;
        this.tail = tail;
        
      }
      toString() { return "Cons(" + this.head + ", " + this.tail + ")"; }
    };
    this.Nil = new class Nil {
      constructor() {
        
      }
      toString() { return "Nil"; }
    };
  }
  isEmpty(xs) {
    if (xs === this.Nil) {
      return true
    } else {
      return false
    }
  }
  toString() { return "Stack"; }
};
undefined
export default Stack;
