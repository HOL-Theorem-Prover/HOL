(* ========================================================================= *)
(* ORDERED REWRITING                                                         *)
(* Copyright (c) 2003-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibRewrite =
sig

type 'a pp = 'a mlibUseful.pp
type term  = mlibTerm.term
type thm   = mlibThm.thm

type rewrs
datatype orient = LtoR | RtoL | Both

(* Basic operations *)
val empty : (term * term -> order option) -> rewrs
val reset : rewrs -> rewrs
val peek  : rewrs -> int -> (thm * orient) option
val size  : rewrs -> int
val eqns  : rewrs -> thm list

(* Add an equation into the system *)
val add : int * thm -> rewrs -> rewrs

(* Rewriting (the order must be a refinement of the initial order) *)
val rewrite : rewrs -> (term * term -> order option) -> int * thm -> thm

(* Inter-reduce the equations in the system *)
val reduced : rewrs -> bool
val reduce' : rewrs -> rewrs * int list          (* also returns new redexes *)
val reduce  : rewrs -> rewrs

(* Pretty-printing *)
val pp_rewrs        : rewrs pp
val rewrs_to_string : rewrs -> string

(* Rewriting as a derived rule *)
val REWRITE     : thm list -> thm -> thm
val ORD_REWRITE : (term * term -> order option) -> thm list -> thm -> thm

end
