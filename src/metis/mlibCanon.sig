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
val purecnf        : formula -> formula list list
val simpcnf        : formula -> formula list list
val clausal        : formula -> formula list list
val cnf            : formula -> formula
val is_cnf         : formula -> bool
val axiomatize     : formula -> thm list
val eq_axiomatize  : formula -> thm list          (* Adds equality axioms *)
val eq_axiomatize' : formula -> thm list          (* Adds if equality occurs *)

end