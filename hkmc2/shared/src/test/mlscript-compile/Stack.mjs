const Stack$class = class Stack {
  constructor() {
    this.Cons = function Cons(head1, tail1) { return new Cons.class(head1, tail1); };
    this.Cons.class = class Cons {
      constructor(head, tail) {
        this.head = head;
        this.tail = tail;
        
      }
      toString() { return "Cons(" + this.head + ", " + this.tail + ")"; }
    };
    const Nil$class = class Nil {
      constructor() {
        
      }
      toString() { return "Nil"; }
    };
    this.Nil = new Nil$class;
    this.Nil.class = Nil$class;
  }
  isEmpty(xs) {
    if (xs instanceof this.Nil.class) {
      return true;
    } else {
      return false;
    }
  }
  toString() { return "Stack"; }
}; const Stack = new Stack$class;
Stack.class = Stack$class;
null
export default Stack;
