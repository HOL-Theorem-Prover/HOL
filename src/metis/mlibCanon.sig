(* ========================================================================= *)
(* FIRST-ORDER LOGIC CANONICALIZATION                                        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibCanon =
sig

type term    = mlibTerm.term
type formula = mlibTerm.formula

(* Simplification *)
val simplify : formula -> formula

(* Negation normal form *)
val nnf : formula -> formula

(* Prenex normal form *)
val prenex : formula -> formula
val pnf    : formula -> formula

(* Skolemization *)
val skolemize      : formula -> formula
val full_skolemize : formula -> formula

(* A tautology filter for clauses *)
val tautologous : formula list -> bool

(* Conjunctive normal form *)
val clausal   : formula -> formula list list
val purecnf   : formula -> formula
val cnf       : formula -> formula  (* simp + nnf + skolemize + purecnf *)
val is_clause : formula -> bool
val is_cnf    : formula -> bool

(* Categorizing sets of clauses *)
datatype prop = Propositional | Effectively_propositional | Non_propositional
datatype equal = Non_equality | Equality | Pure_equality
datatype horn = Trivial | Unit | Both_horn | Horn | Negative_horn | Non_horn
type category = {prop : prop, equal : equal, horn : horn}

val categorize_clauses : formula list -> category
val category_to_string : category -> string

end
