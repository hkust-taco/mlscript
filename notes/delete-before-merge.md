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
