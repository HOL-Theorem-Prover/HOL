(* ========================================================================= *)
(* FINITE MODELS                                                             *)
(* Created by Joe Hurd, October 2003                                         *)
(* ========================================================================= *)

signature mlibModel =
sig

type 'a pp   = 'a mlibUseful.pp
type formula = mlibTerm.formula

(* Parameters *)
type parameters =
  {size  : int,       (* mlibModel size: the number of elements in the domain *)
   perts : int * int} (* Number of perturbations tried when adding formulas *)

val defaults     : parameters
val update_size  : (int -> int) -> parameters -> parameters
val update_perts : (int * int -> int * int) -> parameters -> parameters

(* The type of finite models *)
type model

(* Basic operations *)
val new   : parameters -> formula list -> model
val size  : model -> int
val perts : model -> int * int

(* Check whether a random grounding of a formula is satisfied by the model *)
val check  : model -> formula -> bool
val checkn : model -> formula -> int -> int

(* Integrate formulas by applying random perturbations to the model *)
val add : formula list -> model -> model

(* Pretty-printing *)
val pp_model : model pp

end
