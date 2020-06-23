
data Wine
//│ Wine: {}


let jesus = neg Wine => Wine
//│ jesus: neg Wine -> Wine

:e // TODO: use generativity info to conclude emptiness...
let w = jesus(water: "Evian")
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.10: 	let w = jesus(water: "Evian")
//│ ║        	        ^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(water: "Evian",)` does not match type `neg Wine`
//│ ║  l.10: 	let w = jesus(water: "Evian")
//│ ║        	              ^^^^^^^^^^^^^^
//│ ╟── but it flows into argument with expected type `neg Wine`
//│ ║  l.10: 	let w = jesus(water: "Evian")
//│ ║        	             ^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.6: 	let jesus = neg Wine => Wine
//│ ╙──     	            ^^^^^^^^
//│ w: Wine | error


let jesus = (water: neg Wine) => Wine
//│ jesus: (water: neg Wine,) -> Wine

:e // TODO: use generativity info to conclude emptiness...
let w = jesus(water: "Evian")
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.30: 	let w = jesus(water: "Evian")
//│ ║        	        ^^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `"Evian"` does not match type `neg Wine`
//│ ║  l.30: 	let w = jesus(water: "Evian")
//│ ║        	                     ^^^^^^^
//│ ╟── but it flows into argument with expected type `(water: ?a & neg Wine,)`
//│ ║  l.30: 	let w = jesus(water: "Evian")
//│ ║        	             ^^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.26: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ w: Wine | error

:e
jesus w
jesus(water: w)
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.46: 	jesus w
//│ ║        	^^^^^^^
//│ ╟── expression of type `{}` does not match type `neg Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into reference with expected type `(water: ?a & neg Wine,)`
//│ ║  l.46: 	jesus w
//│ ║        	      ^
//│ ╟── Note: constraint arises from application:
//│ ║  l.26: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ ╔══[ERROR] Type mismatch in application:
//│ ║  l.47: 	jesus(water: w)
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── expression of type `{}` does not match type `neg Wine`
//│ ║  l.2: 	data Wine
//│ ║       	     ^^^^
//│ ╟── but it flows into argument with expected type `(water: ?a & neg Wine,)`
//│ ║  l.47: 	jesus(water: w)
//│ ║        	     ^^^^^^^^^^
//│ ╟── Note: constraint arises from application:
//│ ║  l.26: 	let jesus = (water: neg Wine) => Wine
//│ ╙──      	                    ^^^^^^^^
//│ res: Wine | error
//│ res: Wine | error


(0 | 1) & neg 0
//│ res: (0 | 1) & neg 0

(0 | 1) & neg 0 as 1
//│ res: 1

:e
(0 | 1) & neg 0 as 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.83: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^^^^^^
//│ ╟── expression of type `(0 | 1) & neg 0` does not match type `0`
//│ ║  l.83: 	(0 | 1) & neg 0 as 0
//│ ║        	^^^^^^^^^^^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.83: 	(0 | 1) & neg 0 as 0
//│ ╙──      	                   ^
//│ res: 0

(0 | 1) & neg 0 & neg 1 as "wat"
//│ res: "wat"

:e // TODO
neg 0 as 1
1 as neg 0
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.99: 	neg 0 as 1
//│ ║        	^^^^^^^^^^
//│ ╟── expression of type `neg 0` does not match type `1`
//│ ║  l.99: 	neg 0 as 1
//│ ║        	^^^^^
//│ ╟── Note: constraint arises from integer literal:
//│ ║  l.99: 	neg 0 as 1
//│ ╙──      	         ^
//│ ╔══[ERROR] Type mismatch in 'as' binding:
//│ ║  l.100: 	1 as neg 0
//│ ║         	^^^^^^^^^^
//│ ╟── expression of type `1` does not match type `neg 0`
//│ ║  l.100: 	1 as neg 0
//│ ║         	^
//│ ╟── Note: constraint arises from application:
//│ ║  l.100: 	1 as neg 0
//│ ╙──       	     ^^^^^
//│ res: 1
//│ res: neg 0

