(* ========================================================================= *)
(* FIRST-ORDER LOGIC CANONICALIZATION                                        *)
(* Created by Joe Hurd, September 2001                                       *)
(* Partly ported from the CAML-Light code accompanying John Harrison's book  *)
(* ========================================================================= *)

signature mlibCanon =
sig

type term    = mlibTerm.term
type formula = mlibTerm.formula
type thm     = mlibThm.thm

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
val purecnf : formula -> formula
val cnf     : formula -> formula
val is_cnf  : formula -> bool

(* Converting to clauses *)
val clausal       : formula -> formula list list
val axiomatize    : formula -> thm list
val eq_axioms     : formula -> thm list
val eq_axiomatize : formula -> thm list    (* Adds equality axioms if needed *)

(* Categorizing sets of clauses *)
datatype prop = Propositional | Effectively_propositional | Non_propositional
datatype equal = Non_equality | Equality | Pure_equality
datatype horn = Trivial | Unit | Both_horn | Horn | Negative_horn | Non_horn
type category = {prop : prop, equal : equal, horn : horn}

val categorize_cnf     : formula list -> category
val categorize_goal    : formula -> category
val category_to_string : category -> string

end
