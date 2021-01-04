(*Autor: Nicolas Vazquez Cancela*)

type oper = Not
;;

type biOper = Or | And | If | Iff
;;

type prop =
    C of bool
  | V of string
  | Op of oper * prop
  | BiOp of biOper * prop * prop
;;

let opval = function 
    Not -> not
;;

let biopval = function
    Or -> (||)
  | And -> (&&)
  | If -> fun p q -> (not p) || q
  | Iff -> (=)
;;

let rec peval ctx = function
    C b -> b
  | V s -> List.assoc s ctx
  | Op (op, p) -> (opval op) (peval ctx p)
  | BiOp (biop, p1, p2) -> (biopval biop) (peval ctx p1) (peval ctx p2)
;;

let rec vars = function
    C _ -> []
  | V s -> [s]
  | Op (_, p) -> vars p
  | BiOp (_, p1, p2) -> vars p1 @ vars p2
;;

let rec remove_dups = function
    [] -> []
  | h::t -> 
      if List.mem h t then remove_dups t
      else h :: (remove_dups t)
;;

let pvars p =
  remove_dups (vars p)
;;

let rec ctxs = function
    [] -> [[]]
  | h::t ->
      let cs = ctxs t in
      (List.map (function c -> (h,true)::c) cs) @
      (List.map (function c -> (h,false)::c) cs)
;;

let is_tau p =
  let cs = ctxs (pvars p) in
  List.for_all (function c -> peval c p) cs
;;


(* Ejemplos *)

(*   (p -> q) <=> (not p or q)   es tautologia   *)
let p1 = BiOp (Iff, BiOp (If, V "p", V "q"), BiOp (Or, Op (Not, V "p"), V "q"))
;;

(*   ((p -> q) and (q -> r)) -> (p -> r)   es tautologia   *)
let p2 = BiOp (If, BiOp (And, BiOp (If, V "p", V "q"), BiOp (If, V "q", V "r")), BiOp (If, V "p", V "r"))
;;

(*   ((p -> q) and (not q)) -> (not p)   es el modus tollens y es tautologia   *)
let p3 = BiOp (If, BiOp (And, BiOp (If, V "p", V "q"), Op (Not, V "q")), Op (Not, V "p"))
;;

(*   (p or q) -> p   no es tautologia   *)
let p4 = BiOp (If, BiOp (Or, V "p", V "q"), V "p")
;;


(*   (((p or q) -> not c) and ((not n) -> (not p)) and (not q) and (not n)) -> c   no es tautologia *)
(*   ver https://es.wikipedia.org/wiki/%C3%81rbol_sem%C3%A1ntico   *)

let p5 = BiOp (If, BiOp (And, BiOp (If, BiOp (Or, V "p",
                                                  V "q"),
                                        Op (Not, V "c")),
                              BiOp (And, BiOp (If, Op (Not, V "n"),
                                                   Op (Not, V "p")),
                                         BiOp (And, Op (Not, V "q"),
                                                    Op (Not, V "n")))),
                   V "c")
;;


(*   not (p and q) <=> not p or not q   es una ley de De Morgan y es tautologia *)
let p6 = BiOp (Iff, Op (Not, BiOp (And, V "p", V "q")),
                    BiOp (Or, Op (Not, V "p"), Op (Not, V "q")))
;;

(*   not (p or q) <=> not p and not q   es una ley de De Morgan y es tautologia *)
let p7 = BiOp (Iff, Op (Not, BiOp (Or, V "p", V "q")),
                    BiOp (And, Op (Not, V "p"), Op (Not, V "q")))
;;

(*Tabla semantica:*)
type log_tree =
	Empty
	|
	Node of prop * log_tree * log_tree
;;

(*
Funcion para poner un arbol en las hojas del primero,
necesario para la proposicion "And".
*)
let tree_concat t ts =
	let rec aux = function
		Empty -> ts
		|
		Node(prop, tl, Empty) -> Node(prop, (aux tl), Empty)
		|
		Node(prop, tl, tr) -> Node(prop, (aux tl), (aux tr))
	in aux t
;;

(*Funcion para crear el arbol que representa la tabla semantica.*)
let rec tabla_sem prop = match prop with
	C _ | V _ -> Node(prop, Empty, Empty)
	|
	Op(op, p) -> (match (op, p) with
		(Not, (C b)) -> Node(prop, (tabla_sem (C (not b))), Empty)
		|
		(Not, (V _)) -> Node(prop, Empty, Empty)
		|
		(Not, (Op(Not, p))) -> Node(prop, (tabla_sem p), Empty)
		|
		(Not, (BiOp(biop, p1, p2))) -> (match biop with
			Or -> Node(prop, 
				(tree_concat (tabla_sem (Op(Not, p1))) (tabla_sem (Op(Not, p2)))), Empty)
			|
			And -> Node(prop, (tabla_sem (Op(Not, p1))), (tabla_sem (Op(Not, p2))))
			|
			If -> Node(prop, (tree_concat (tabla_sem p1) (tabla_sem (Op(Not, p2)))), Empty)
			|
			Iff -> Node(prop, (tree_concat (tabla_sem p1) (tabla_sem (Op(Not, p2)))),
				(tree_concat (tabla_sem (Op(Not, p1))) (tabla_sem p2)))))
	|
	BiOp(biop, p1, p2) -> (match biop with
		Or -> Node(prop, (tabla_sem p1), (tabla_sem p2))
		|
		And -> Node(prop, (tree_concat (tabla_sem p1) (tabla_sem p2)), Empty)
		|
		If -> Node(prop, (tabla_sem (Op(Not, p1))), (tabla_sem p2))
		|
		Iff -> Node(prop, (tree_concat (tabla_sem p1) (tabla_sem p2)),
			(tree_concat (tabla_sem (Op(Not, p1))) (tabla_sem (Op(Not, p2))))))
;;

let is_tau_2 =
	let rec buscar vars = function
		Empty -> false
		|
		Node(C false, _, _) -> true
		|
		Node(V s, t, Empty) -> (try not(List.assoc s vars) || 
				buscar vars t with
			Not_found -> buscar ((s,true)::vars) t)
		|
		Node(V s, tl, tr) -> (try not(List.assoc s vars) ||
				(buscar vars tl && buscar vars tr) with
			Not_found -> let vars = (s,true)::vars in
				(buscar vars tl) && (buscar vars tr))
		|
		Node(Op(Not, V s), t, Empty) -> (try List.assoc s vars || 
				buscar vars t with
			Not_found -> buscar ((s,false)::vars) t)
		|
		Node(Op(Not, V s), tl, tr) -> (try List.assoc s vars || 
				(buscar vars tl && buscar vars tr) with
			Not_found -> let vars = (s,false)::vars in
				(buscar vars tl) && (buscar vars tr))
		|
		Node(prop, t, Empty) -> buscar vars t
		|
		Node(prop, tl, tr) -> (buscar vars tl) && (buscar vars tr)
	in fun
		prop -> buscar [] (tabla_sem (Op(Not, prop)))
;;