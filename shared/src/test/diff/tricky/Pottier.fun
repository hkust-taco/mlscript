

// Inspired by [Pottier 98, chap 13.4]

let rec f = x => y => add (f x.tail y) (f x y)
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.5: 	let rec f = x => y => add (f x.tail y) (f x y)
//│ ║       	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α22'  <:  {tail: tail33'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α22'  <:  {tail: tail24''}
//│ f: {tail: {tail: anything}} -> anything -> int

// FIXME? now fails with constrained-arg-gen
let rec f = x => y => add (f x.tail y) (f y x)
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.15: 	let rec f = x => y => add (f x.tail y) (f y x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α41'  <:  {tail: tail52'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α41'  <:  {tail: tail43''}
//│ f: {tail: {tail: anything}} -> {tail: {tail: anything}} -> int

let rec f = x => y => add (f x.tail y) (f x y.tail)
let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
let rec f = x => y => add (f x.tail x) (f y.tail y)
let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.24: 	let rec f = x => y => add (f x.tail y) (f x y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α62'  <:  {tail: tail74'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α62'  <:  {tail: tail69''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.24: 	let rec f = x => y => add (f x.tail y) (f x y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α61'  <:  {tail: tail76'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α61'  <:  {tail: tail63''}
//│ f: {tail: {tail: anything}} -> {tail: {tail: anything}} -> int
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail103'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail105'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail107'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail109'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail111'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail88'' where: α86' <: {tail: tail88''}}›  <:  {tail: tail112'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail88'' where: α86' <: {tail: tail88''}}›  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail113'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail115'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail88'' where: α86' <: {tail: tail88''}}›  <:  {tail: tail116'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail88'' where: α86' <: {tail: tail88''}}›  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail117'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail119'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail121'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail122'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail124'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail126'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail88''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α86'  <:  {tail: tail127'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α86'  <:  {tail: tail95''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail129'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail91'' where: α87' <: {tail: tail91''}}›  <:  {tail: tail130'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail91'' where: α87' <: {tail: tail91''}}›  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail131'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail133'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail91'' where: α87' <: {tail: tail91''}}›  <:  {tail: tail134'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail91'' where: α87' <: {tail: tail91''}}›  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail135'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail137'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail139'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail140'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail142'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail144'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail91''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.25: 	let rec f = x => y => add (f x.tail y.tail) (f x.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α87'  <:  {tail: tail145'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α87'  <:  {tail: tail98''}
//│ f: {tail: {tail: {tail: {tail: anything}}}} -> {tail: {tail: {tail: {tail: anything}}}} -> int
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail194'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail196'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail198'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail200'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail202'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail205'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail207'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail210'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail213'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail215'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail216'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail217'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail219'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail220'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail221'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail224'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail225'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail227'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail228'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail229'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail231'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail232'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail235'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail237'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail238'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail239'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail241'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail242'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail243'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail246'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail247'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail249'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail250'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail251'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail253'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail254'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail257'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail259'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail260'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail261'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail263'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail264'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail265'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail268'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail270'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail271'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail272'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail274'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail275'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail276'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail279'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail281'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail282'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail283'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail285'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail286'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail287'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail290'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail292'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail293'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail294'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail296'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail297'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail298'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail301'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail302'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail304'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail305'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail306'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail308'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail309'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail312'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail313'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail315'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail316'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail317'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail180'' where: α175' <: {tail: tail180''}}›  <:  {tail: tail184''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail319'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail320'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail323'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail325'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail327'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail328'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail330'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail332'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail333'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail336'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail177''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail338'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail340'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail341'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail343'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α175'  <:  {tail: tail345'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α175'  <:  {tail: tail180''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.26: 	let rec f = x => y => add (f x.tail x.tail) (f y.tail y.tail)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α176'  <:  {tail: tail346'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α176'  <:  {tail: tail187''}
//│ f: {tail: {tail: {tail: {tail: {tail: {tail: anything}}}}}} -> {tail: {tail: {tail: {tail: {tail: {tail: {tail: {tail: anything}}}}}}}} -> int
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail454'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail457'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail442'' where: α440' <: {tail: tail442''}}›  <:  {tail: tail458'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail442'' where: α440' <: {tail: tail442''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail460'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail442'' where: α440' <: {tail: tail442''}}›  <:  {tail: tail461'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail442'' where: α440' <: {tail: tail442''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail463'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail465'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail466'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail468'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail469'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail470'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail472'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail473'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail474'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail476'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail477'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail478'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail480'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail481'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail482'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail447'' where: α441' <: {tail: tail447''}}›  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail484'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail485'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail487'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α440'  <:  {tail: tail489'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α440'  <:  {tail: tail442''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.27: 	let rec f = x => y => add (f x.tail x) (f y.tail y)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α441'  <:  {tail: tail490'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α441'  <:  {tail: tail447''}
//│ f: {tail: {tail: {tail: {tail: {tail: {tail: {tail: anything}}}}}}} -> {tail: {tail: {tail: {tail: {tail: {tail: anything}}}}}} -> int
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail526'' where: α520' <: {tail: tail526''}}›  <:  {tail: tail532'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail526'' where: α520' <: {tail: tail526''}}›  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail534'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail536'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail537'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail538'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail540'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail541'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail542'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail544'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail545'}    PolymorphicType  RecordType
//│ ╙──  ... looks like:  ‹∀ 1. {tail521'' where: α519' <: {tail: tail521''}}›  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail546'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail548'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail550'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail551'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail553'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α519'  <:  {tail: tail555'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α519'  <:  {tail: tail521''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.28: 	let rec f = x => y => add (f x.tail y) (f y.tail x)
//│ ║        	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α520'  <:  {tail: tail556'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α520'  <:  {tail: tail526''}
//│ f: {tail: {tail: {tail: {tail: {tail: anything}}}}} -> {tail: {tail: {tail: {tail: {tail: anything}}}}} -> int

let f = x => y => if true then { l: x; r: y } else { l: y; r: x } // 2-crown
//│ f: 'a -> 'a -> {l: 'a, r: 'a}


// Inspired by [Pottier 98, chap 13.5]

let rec f = x => y => if true then x else { t: f x.t y.t }
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.1025: 	let rec f = x => y => if true then x else { t: f x.t y.t }
//│ ║          	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α588'  <:  {t: t601'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α588'  <:  {t: t593''}
//│ ╔══[ERROR] Cyclic-looking constraint while typing binding of lambda expression
//│ ║  l.1025: 	let rec f = x => y => if true then x else { t: f x.t y.t }
//│ ║          	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ ╟── ————————— Additional debugging info: —————————
//│ ╟── this constraint:  α589'  <:  {t: t603'}    TypeVariable  RecordType
//│ ╙──  ... looks like:  α589'  <:  {t: t596''}
//│ f: 'a -> {t: {t: anything}} -> 'a
//│   where
//│     'a :> forall 'a. ('t | {t: 'a}
//│   where
//│     'a <: {t: 't})
//│        <: {t: {t: anything}}


