
data Wine
//│ Wine: {}

let jesus = (water: neg Wine) => Wine
//│ jesus: (water: neg Wine,) -> Wine

:e // TODO: use generativity info to conclude emptiness...
let w = jesus(water: "Evian")
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.9: 	let w = jesus(water: "Evian")
//│ ║       	        ^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `"Evian"` does not match type `neg Wine`
//│ ║  l.9: 	let w = jesus(water: "Evian")
//│ ║       	                     ^^^^^^^
//│ ╟── but it flows into argument with expected type `(water: ?a & neg Wine,)`
//│ ║  l.9: 	let w = jesus(water: "Evian")
//│ ║       	             ^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.5: 	let jesus = (water: neg Wine) => Wine
//│ ╙──     	                    ^^^^^^^^
//│ w: Wine | error

:e
jesus w
jesus(water: w)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.25: 	jesus w
//│ ║        	^^^^^^^
//│ ╟── expression of type `{}` does not match type `neg Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into reference with expected type `(water: ?a & neg Wine,)`
//│ ║  l.25: 	jesus w
//│ ║        	      ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.5: 	let jesus = (water: neg Wine) => Wine
//│ ╙──     	                    ^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.26: 	jesus(water: w)
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `Wine` does not match type `neg Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into argument with expected type `(water: ?a & neg Wine,)`
//│ ║  l.26: 	jesus(water: w)
//│ ║        	     ^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.5: 	let jesus = (water: neg Wine) => Wine
//│ ╙──     	                    ^^^^^^^^
//│ res: Wine | error
//│ res: Wine | error

(0 | 1) & neg 0
//│ res: (0 | 1) & neg 0

(0 | 1) & neg 0 as 1
//│ res: 1

:e
(0 | 1) & neg 0 as 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.61: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(0 | 1) & neg 0` does not match type `0`
//│ ║  l.61: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.61: 	(0 | 1) & neg 0 as 0
//│ ╙──      	                   ^
//│ res: 0

(0 | 1) & neg 0 & neg 1 as "wat"
//│ res: "wat"

:e // TODO
neg 0 as 1
1 as neg 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.77: 	neg 0 as 1
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `neg 0` does not match type `1`
//│ ║  l.77: 	neg 0 as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.77: 	neg 0 as 1
//│ ╙──      	         ^
//│ ╔══[ERROR] Unsupported pattern shape:
//│ ║  l.78: 	1 as neg 0
//│ ╙──      	     ^^^^^
//│ res: 1
//│ res: error

