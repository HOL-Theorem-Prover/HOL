(* ========================================================================= *)
(* KEEPING TRACK OF TERM ORDERING CONSTRAINTS                                *)
(* The underlying term order is the Knuth-Bendix order                       *)
(* Created by Joe Hurd, November 2002                                        *)
(* ========================================================================= *)

signature mlibTermorder =
sig

type 'a pp = 'a mlibUseful.pp
type term  = mlibTerm.term
type subst = mlibSubst.subst

(* Parameters *)
type parameters =
  {weight     : string * int -> int,
   precedence : (string * int) * (string * int) -> order,
   approx     : int}       (* How close the approximation is: one of {0,1,2} *)

val defaults      : parameters
val update_approx : (int -> int) -> parameters -> parameters

(* The termorder type *)
type termorder

(*  Basic operations *)
val empty    : parameters -> termorder
val null     : termorder -> bool
val vars     : termorder -> string list
val add_leqs : (term * term) list -> termorder -> termorder
val subst    : subst -> termorder -> termorder
val merge    : termorder -> termorder -> termorder

(* Query *)
val consistent : termorder -> termorder option
val subsumes   : termorder -> termorder -> bool
val compare    : termorder -> term * term -> order option

(* Pretty-printing *)
val pp_termorder : termorder pp

end
