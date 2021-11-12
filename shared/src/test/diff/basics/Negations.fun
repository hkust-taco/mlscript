
data Wine
//│ Wine: anything


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
//│ ║  l.20: 	jesus w
//│ ║        	^^^^^^^
//│ ╟── expression of type `anything` does not match type `~Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into reference with expected type `(water: ?a & ~Wine,)`
//│ ║  l.20: 	jesus w
//│ ║        	      ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.13: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ res: Wine | error
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.21: 	jesus(water: w)
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `anything` does not match type `~Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into argument with expected type `(water: ?a & ~Wine,)`
//│ ║  l.21: 	jesus(water: w)
//│ ║        	     ^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.13: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ res: Wine | error


(0 | 1) & neg 0
//│ res: 1

(0 | 1) & neg 0 as 1
//│ res: 1

:e
(0 | 1) & neg 0 as 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.57: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `1` does not match type `0`
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.57: 	(0 | 1) & neg 0 as 0
//│ ╙──      	                   ^
//│ res: 0

(0 | 1) & neg 0 & neg 1 as "wat"
//│ res: "wat"

:e
neg 0 as 1
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.71: 	neg 0 as 1
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `~0` does not match type `1`
//│ ║  l.71: 	neg 0 as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.71: 	neg 0 as 1
//│ ╙──      	         ^
//│ res: 1

1 as neg 0
//│ res: ~0
