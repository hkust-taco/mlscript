# Example 07: Compression Priority Queue

Status: Done

## Source

- Repository path: `sources/examples/compress/fileprio.ml`
- Local clone path:
  `/tmp/caml-light-parser-demo.aWVE6K/camllight/sources/examples/compress/fileprio.ml`

## Original Example

```ocaml
type 'a t = Vide | File of int * 'a * 'a t * 'a t;;
let vide = Vide;;
let rec enleve_sommet = function
  | Vide -> raise File_vide
  | File(prio, elt, Vide, Vide) -> Vide
  | File(prio, elt, gauche, Vide) -> gauche
  | File(prio, elt, Vide, droite) -> droite
  | File(prio, elt, (File(prio_g, elt_g, _, _) as gauche),
                    (File(prio_d, elt_d, _, _) as droite)) ->
      if prio_g < prio_d
      then File(prio_g, elt_g, enleve_sommet gauche, droite)
      else File(prio_d, elt_d, gauche, enleve_sommet droite);;

let extraire = function
  | Vide -> raise File_vide
  | File(prio, elt, _, _) as file -> (prio, elt, enleve_sommet file);;
let rec ajoute file prio elt =
  match file with
  | Vide ->
      File(prio, elt, Vide, Vide)
  | File(prio1, elt1, gauche, droite) ->
      if prio <= prio1
      then File(prio, elt, ajoute droite prio1 elt1, gauche)
      else File(prio1, elt1, ajoute droite prio elt, gauche);;
```

## Adapted Example

```ocaml
type 'a t = Empty | QueueNode of int * 'a * 'a t * 'a t;;
exception Empty_queue;;
let empty = Empty;;
let rec remove_top = function
  | Empty -> raise Empty_queue
  | QueueNode(priority, item, Empty, Empty) -> Empty
  | QueueNode(priority, item, left, Empty) -> left
  | QueueNode(priority, item, Empty, right) -> right
  | QueueNode(priority, item,
              QueueNode(left_priority, left_item, left_left, left_right),
              QueueNode(right_priority, right_item, right_left, right_right)) ->
      if left_priority < right_priority
      then QueueNode(left_priority, left_item,
                     remove_top (QueueNode(left_priority, left_item, left_left, left_right)),
                     QueueNode(right_priority, right_item, right_left, right_right))
      else QueueNode(right_priority, right_item,
                     QueueNode(left_priority, left_item, left_left, left_right),
                     remove_top (QueueNode(right_priority, right_item, right_left, right_right)))
;;
let extract = function
  | Empty -> raise Empty_queue
  | QueueNode(priority, item, left, right) ->
      (priority, item, remove_top (QueueNode(priority, item, left, right)))
;;
let rec add queue priority item =
  match queue with
  | Empty -> QueueNode(priority, item, Empty, Empty)
  | QueueNode(priority1, item1, left, right) ->
      if priority <= priority1
      then QueueNode(priority, item, add right priority1 item1, left)
      else QueueNode(priority1, item1, add right priority item, left)
;;
```

## Adaptation Notes

- Translated French names to English.
- Added a local `Empty_queue` exception declaration because the original uses a
  cross-file exception.
- Replaced `as` patterns with explicit reconstruction of the matched queue
  nodes. Pattern aliases are documented as deferred parser work.

## Parser Fixes

- None.
