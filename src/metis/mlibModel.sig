(* ========================================================================= *)
(* FINITE MODELS                                                             *)
(* Copyright (c) 2003-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibModel =
sig

type 'a pp   = 'a mlibUseful.pp
type formula = mlibTerm.formula

(* Parameters *)
type parameters = {size : int}        (* The number of elements in the model *)

val defaults     : parameters
val update_size  : (int -> int) -> parameters -> parameters

(* The type of finite models *)
type model

(* Basic operations *)
val new  : parameters -> model
val size : model -> int

(* Check whether a random grounding of a formula is satisfied by the model *)
val check  : model -> formula -> bool
val checkn : model -> formula -> int -> int
val count  : model -> formula -> int * int  (* num of satisfying groundings *)

(* Try to make formulas true by applying random perturbations to the model *)
val perturb : formula list -> int -> model -> model

(* Pretty-printing *)
val pp_model : model pp

end
