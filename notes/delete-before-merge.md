# Delete this file before merge this branch!

## Commit a1e2c67

Wrong (this branch):

```
:d
class Monoid[A]
  method Empty: A
//│ 0. Typing type Top
//│ | vars=Map(A -> A0') newDefsInfo=Map(Monoid -> (Cls,1))
//│ => ⊤ | 
//│ >>> Going through method Empty in Monoid
//│ >>> reverseRigid2 (2 entries)
//│ >>> 0. A (o: ‹class type parameter:Loc(13,14,Repro:+72)›) -> A0' (o: ‹class type parameter:Loc(13,14,Repro:+72)›)
//│ >>> 1. Empty.this1 ([NO PROV]) -> Empty.this1 ([NO PROV])
//│ 1. Typing type TypeName(A)
//│ | vars=Map(A -> A) newDefsInfo=Map()
//│ => A | 
//│ >>> substituted method body type: PolymorphicType(0,A0')
//│ >>> Monoid.Empty : PolymorphicType(0,(((Monoid[A] & Empty.this1),) -> A0'))
//│ >> Checking subsumption for declared type of Empty : MethodType(0,Some(((Monoid[A] & Empty.this1),A0')),List(TypeName(Monoid)),false)
//│ Defined class Monoid
//│ Typed as: (((Monoid[A] & Empty.this1),) -> A0')
//│  where: Empty.this1 <: Monoid[A]
//│ Declared Monoid.Empty: Monoid[A] -> nothing
```

Correct (the main branch):

```
:d
class Monoid[A]
  method Empty: A
//│ 0. Typing type Top
//│ | vars=Map(A -> A0') newDefsInfo=Map(Monoid -> (Cls,1))
//│ => ⊤ | 
//│ 1. Typing type TypeName(A)
//│ | vars=Map(A -> A) newDefsInfo=Map()
//│ => A | 
//│ >> Checking subsumption for declared type of Empty : MethodType(0,Some((Monoid[A0'],A0')),List(TypeName(Monoid)),false)
//│ Defined class Monoid
//│ Typed as: ((Monoid[A0']) -> A0')
//│  where: 
//│ ty[true] ((Monoid[A0']) -> A0')
//│ -> DNF(((Monoid[A0']) -> A0'){})
//│ DNF[true] DNF(((Monoid[A0']) -> A0'){})
//│ | ty[false] (Monoid[A0'])
//│ | -> DNF((Monoid[A0']){_1: Monoid[A0']})
//│ | DNF[false] DNF((Monoid[A0']){_1: Monoid[A0']})
//│ | | ty[false] Monoid[A0']
//│ | | -> DNF(monoid<>{Monoid#A: (A0' -> A0')})
//│ | | DNF[false] DNF(monoid<>{Monoid#A: (A0' -> A0')})
//│ | | | ty[false] (A0' -> A0')
//│ | | | -> DNF((A0' -> A0'){})
//│ | | | DNF[false] DNF((A0' -> A0'){})
//│ | | | | ty[true] A0'
//│ | | | | | Consider A0' List() List()
//│ | | | | -> DNF(A0')
//│ | | | | DNF[true] DNF(A0')
//│ | | | | | Renewed A0' ~> A1'
//│ | | | | ~> A1'
//│ | | | | ty[false] A0'
//│ | | | | | Consider A0' List() List()
//│ | | | | -> DNF(A0')
//│ | | | | DNF[false] DNF(A0')
//│ | | | | ~> A1'
//│ | | | ~> (A1' -> A1')
//│ | | ~> (monoid<> & {Monoid#A: (A1' -> A1')})
//│ | | ty[false] Monoid[A0']
//│ | | -> DNF(monoid<>{Monoid#A: (A0' -> A0')})
//│ | | DNF[false] DNF(monoid<>{Monoid#A: (A0' -> A0')})
//│ | | | ty[false] (A0' -> A0')
//│ | | | -> DNF((A0' -> A0'){})
//│ | | | DNF[false] DNF((A0' -> A0'){})
//│ | | | | ty[true] A0'
//│ | | | | | Consider A0' List() List()
//│ | | | | -> DNF(A0')
//│ | | | | DNF[true] DNF(A0')
//│ | | | | ~> A1'
//│ | | | | ty[false] A0'
//│ | | | | | Consider A0' List() List()
//│ | | | | -> DNF(A0')
//│ | | | | DNF[false] DNF(A0')
//│ | | | | ~> A1'
//│ | | | ~> (A1' -> A1')
//│ | | ~> (monoid<> & {Monoid#A: (A1' -> A1')})
//│ | ~> (((monoid<> & {Monoid#A: (A1' -> A1')})) & {_1: (monoid<> & {Monoid#A: (A1' -> A1')})})
//│ | ty[true] A0'
//│ | | Consider A0' List() List()
//│ | -> DNF(A0')
//│ | DNF[true] DNF(A0')
//│ | ~> A1'
//│ ~> ((((monoid<> & {Monoid#A: (A1' -> A1')})) & {_1: (monoid<> & {Monoid#A: (A1' -> A1')})}) -> A1')
//│ Canon: ((((monoid<> & {Monoid#A: (A1' -> A1')})) & {_1: (monoid<> & {Monoid#A: (A1' -> A1')})}) -> A1')
//│  where: 
//│ ! true A1' None
//│ ! false A1' None
//│ ! true A1' Some(HashSet(A1'))
//│ ! false A1' Some(HashSet(A1'))
//│ ! true A1' Some(HashSet(A1'))
//│ [occs] LinkedHashMap((true,A1') -> HashSet(A1'), (false,A1') -> HashSet(A1'))
//│ [vars] TreeSet(A1')
//│ [bounds] 
//│ [rec] HashSet()
//│ [v] A1' Some(HashSet(A1')) Some(HashSet(A1'))
//│ [sub] 
//│ Renewed A1' ~> A2'
//│ Type after simplification: ((((monoid<> & {Monoid#A: (A2' -> A2')})) & {_1: (monoid<> & {Monoid#A: (A2' -> A2')})}) -> A2')
//│  where: 
//│ ty[true] ((((monoid<> & {Monoid#A: (A2' -> A2')})) & {_1: (monoid<> & {Monoid#A: (A2' -> A2')})}) -> A2')
//│ -> DNF(((((monoid<> & {Monoid#A: (A2' -> A2')})) & {_1: (monoid<> & {Monoid#A: (A2' -> A2')})}) -> A2'){})
//│ DNF[true] DNF(((((monoid<> & {Monoid#A: (A2' -> A2')})) & {_1: (monoid<> & {Monoid#A: (A2' -> A2')})}) -> A2'){})
//│ | ty[false] (((monoid<> & {Monoid#A: (A2' -> A2')})) & {_1: (monoid<> & {Monoid#A: (A2' -> A2')})})
//│ | -> DNF(((monoid<> & {Monoid#A: (A2' -> A2')})){_1: (monoid<> & {Monoid#A: (A2' -> A2')})})
//│ | DNF[false] DNF(((monoid<> & {Monoid#A: (A2' -> A2')})){_1: (monoid<> & {Monoid#A: (A2' -> A2')})})
//│ | | ty[false] (monoid<> & {Monoid#A: (A2' -> A2')})
//│ | | -> DNF(monoid<>{Monoid#A: (A2' -> A2')})
//│ | | DNF[false] DNF(monoid<>{Monoid#A: (A2' -> A2')})
//│ | | | ty[false] (A2' -> A2')
//│ | | | -> DNF((A2' -> A2'){})
//│ | | | DNF[false] DNF((A2' -> A2'){})
//│ | | | | ty[true] A2'
//│ | | | | | Consider A2' List() List()
//│ | | | | -> DNF(A2')
//│ | | | | DNF[true] DNF(A2')
//│ | | | | | Renewed A2' ~> A3'
//│ | | | | ~> A3'
//│ | | | | ty[false] A2'
//│ | | | | | Consider A2' List() List()
//│ | | | | -> DNF(A2')
//│ | | | | DNF[false] DNF(A2')
//│ | | | | ~> A3'
//│ | | | ~> (A3' -> A3')
//│ | | ~> (monoid<> & {Monoid#A: (A3' -> A3')})
//│ | | ty[false] (monoid<> & {Monoid#A: (A2' -> A2')})
//│ | | -> DNF(monoid<>{Monoid#A: (A2' -> A2')})
//│ | | DNF[false] DNF(monoid<>{Monoid#A: (A2' -> A2')})
//│ | | | ty[false] (A2' -> A2')
//│ | | | -> DNF((A2' -> A2'){})
//│ | | | DNF[false] DNF((A2' -> A2'){})
//│ | | | | ty[true] A2'
//│ | | | | | Consider A2' List() List()
//│ | | | | -> DNF(A2')
//│ | | | | DNF[true] DNF(A2')
//│ | | | | ~> A3'
//│ | | | | ty[false] A2'
//│ | | | | | Consider A2' List() List()
//│ | | | | -> DNF(A2')
//│ | | | | DNF[false] DNF(A2')
//│ | | | | ~> A3'
//│ | | | ~> (A3' -> A3')
//│ | | ~> (monoid<> & {Monoid#A: (A3' -> A3')})
//│ | ~> (((monoid<> & {Monoid#A: (A3' -> A3')})) & {_1: (monoid<> & {Monoid#A: (A3' -> A3')})})
//│ | ty[true] A2'
//│ | | Consider A2' List() List()
//│ | -> DNF(A2')
//│ | DNF[true] DNF(A2')
//│ | ~> A3'
//│ ~> ((((monoid<> & {Monoid#A: (A3' -> A3')})) & {_1: (monoid<> & {Monoid#A: (A3' -> A3')})}) -> A3')
//│ Recanon: ((((monoid<> & {Monoid#A: (A3' -> A3')})) & {_1: (monoid<> & {Monoid#A: (A3' -> A3')})}) -> A3')
//│  where: 
//│ ! true A3' None
//│ ! false A3' None
//│ ! true A3' Some(HashSet(A3'))
//│ ! false A3' Some(HashSet(A3'))
//│ ! true A3' Some(HashSet(A3'))
//│ [occs] LinkedHashMap((true,A3') -> HashSet(A3'), (false,A3') -> HashSet(A3'))
//│ [vars] TreeSet(A3')
//│ [bounds] 
//│ [rec] HashSet()
//│ [v] A3' Some(HashSet(A3')) Some(HashSet(A3'))
//│ [sub] 
//│ Renewed A3' ~> A4'
//│ Resimplified: ((((monoid<> & {Monoid#A: (A4' -> A4')})) & {_1: (monoid<> & {Monoid#A: (A4' -> A4')})}) -> A4')
//│  where: 
//│ Recons: ((Monoid[A4']) -> A4')
//│ Declared Monoid.Empty: Monoid['A] -> 'A
```

Oh, I see. It should be `Monoid[A0']` in `PolymorphicType(0,(((Monoid[A] & Empty.this1),) -> A0'))`.
So we should update `tr`, making its type arguments up-to-date.
~~But why the debug log is very short? Oh it's because my main branch is outdated.~~

## Commit f25facd

Some type variables are leaking...

```
class Addable[A]
  method Add: A -> A
//│ Defined class Addable
//│ Declared Addable.Add: Addable['A] -> 'A -> 'A

class Num: Addable[Num] & { val: int }
  method Add that = Num { val = this.val + that.val }
//│ Defined class Num
//│ Defined Num.Add: Num -> {val: int} -> Num

class Str: Addable[Str] & { val: string }
  method Add that = Str { val = concat this.val that.val }
//│ Defined class Str
//│ Defined Str.Add: Str -> {val: string} -> Str

n = Num { val = 1 }
//│ n: Num & {val: 1}
//│  = Num { val: 1 }

n.Add n
//│ res: Num & {val: 1}
//│    = Num { val: 2 }

s = Str { val = "hey" }
//│ s: Str & {val: "hey"}
//│  = Str { val: 'hey' }

s.Add s
//│ ╔══[ERROR] Type mismatch in field selection:
//│ ║  l.160: 	s.Add s
//│ ║         	^^^^^
//│ ╟── type `Num` is not an instance of type Str
//│ ║  l.138: 	class Num: Addable[Num] & { val: int }
//│ ║         	                   ^^^
//│ ╟── Note: constraint arises from type reference:
//│ ║  l.143: 	class Str: Addable[Str] & { val: string }
//│ ╙──       	                   ^^^
//│ res: error
//│    = Str { val: 'heyhey' }
```

There's no way `Num` is involved in `s`.

**Correct output:**

CONSTRAIN `((Addable[A3],) -> ((A3,) -> A3)) <! (([α0],) -> α2)` where

- `α0 :> [(str<addable> & {Addable#A: (Str -> Str), val: val1})]`,
- `val1 :> ["hey"<string>] <: String`

**Wrong output:**

CONSTRAIN `((this30,) -> ((A3,) -> A3)) <! (([α0],) -> α2)` where

- `α0 :> [(str<addable> & {Addable#A: (Str -> Str), val: val1})]` (this is fine),
- `val1 :> ["hey"<string>] <: String` (this is also fine),
- `A3 :> [[Num]] <: [[Num]]` (what the heck?),
- `A29' :> [[Num]] <: [[Num]]`
- `this30 :> [[[(num<addable> & {Addable#A: (Num -> Num), val: val117})]]] <: Addable[A29']` (the leak should be here),
- `val117 :> [1<int,number>] <: Int`

**Questions**

- Why `A3` has bounds?
- Why `this30` has bounds containing `Num`?

Ohhhhhhh! The 30 in `this30` is changing?
