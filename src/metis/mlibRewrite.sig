(* ========================================================================= *)
(* ORDERED REWRITING                                                         *)
(* Created by Joe Hurd, June 2003                                            *)
(* ========================================================================= *)

signature mlibRewrite =
sig

type 'a pp = 'a mlibUseful.pp
type term  = mlibTerm.term
type thm   = mlibThm.thm

type rewrs

(* Basic operations *)
val empty : (term * term -> order option) -> rewrs
val reset : rewrs -> rewrs
val peek  : rewrs -> int -> thm option
val size  : rewrs -> int
val eqns  : rewrs -> (int * thm) list

(* Add an equation into the system *)
val add : int * thm -> rewrs -> rewrs

(* Rewriting (the order must be a refinement of the initial order) *)
val rewrite : rewrs -> (term * term -> order option) -> int * thm -> thm

(* Inter-reduce the equations in the system *)
val reduce : rewrs -> rewrs

(* Pretty-printing *)
val pp_rewrs        : rewrs pp
val rewrs_to_string : rewrs -> string

(* Rewriting as a derived rule *)
val REWRITE     : thm list -> thm -> thm
val ORD_REWRITE : (term * term -> order option) -> thm list -> thm -> thm

end
