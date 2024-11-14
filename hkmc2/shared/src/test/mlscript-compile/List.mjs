const List$class = class List {
  constructor() {
    this.List = class List {
      constructor() {
        
      }
      toString() { return "List"; }
    };
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
  toString() { return "List"; }
}; const List = new List$class;
List.class = List$class;
undefined
export default List;
