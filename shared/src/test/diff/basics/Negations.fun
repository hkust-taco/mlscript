
data Wine
//│ Defined class Wine
//│ Wine: Wine


let jesus = neg Wine => Wine
//│ jesus: ~Wine -> Wine

let w = jesus(water: "Evian")
//│ w: Wine


let jesus = (water: neg Wine) => Wine
//│ jesus: (water: ~Wine,) -> Wine

let w = jesus(water: "Evian")
//│ w: Wine

:e
jesus w
jesus(water: w)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.21: 	jesus w
//│ ║        	^^^^^^^
//│ ╟── expression of type `Wine` does not match type `~Wine`
//│ ║  l.14: 	let jesus = (water: neg Wine) => Wine
//│ ║        	                                 ^^^^
//│ ╟── but it flows into reference with expected type `~Wine`
//│ ║  l.21: 	jesus w
//│ ║        	      ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.14: 	let jesus = (water: neg Wine) => Wine
//│ ║        	                    ^^^^^^^^
//│ ╟── from binding:
//│ ║  l.14: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	             ^^^^^^^^^^^^^^^
//│ res: error | Wine
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.22: 	jesus(water: w)
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `Wine` does not match type `~Wine`
//│ ║  l.14: 	let jesus = (water: neg Wine) => Wine
//│ ║        	                                 ^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.14: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ res: error | Wine


(0 | 1) & neg 0
//│ res: 1

(0 | 1) & neg 0 as 1
//│ res: 1

:e
(0 | 1) & neg 0 as 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.58: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `1` does not match type `0`
//│ ║  l.58: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.58: 	(0 | 1) & neg 0 as 0
//│ ╙──      	                   ^
//│ res: 0

(0 | 1) & neg 0 & neg 1 as "wat"
//│ res: "wat"

:e
neg 0 as 1
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.74: 	neg 0 as 1
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `~0` does not match type `1`
//│ ║  l.74: 	neg 0 as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.74: 	neg 0 as 1
//│ ╙──      	         ^
//│ res: 1

1 as neg 0
//│ res: ~0
