(* ========================================================================= *)
(* FINITE MODELS                                                             *)
(* Copyright (c) 2003-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibModel =
sig

type 'a pp   = 'a mlibUseful.pp
type term    = mlibTerm.term
type formula = mlibTerm.formula

(* The parts of the model that are fixed and cannot be perturbed *)
(* Note: a model of size N has integer elements 0...N-1 *)
type fix = int -> {func : (string * int list) -> int option,
                   pred : (string * int list) -> bool option}
val fix_merge  : fix -> fix -> fix
val fix_mergel : fix list -> fix
val map_fix    : (string -> string option) -> fix -> fix
val pure_fix   : fix  (* = *)
val basic_fix  : fix  (* id fst snd #1 #2 #3 <> *)
val modulo_fix : fix  (* 0 1 2 suc pre ~ + - * exp mod *)
                      (* < <= > >= is_0 divides odd even *)
val heap_fix   : fix  (* 0 1 2 suc pre + - * exp < <= > >= is_0 *)
val set_fix    : fix  (* empty univ union inter compl card in subset *)

(* Parameters *)
type parameters = {size : int, fix : fix}
val defaults    : parameters
val update_size : (int -> int) -> parameters -> parameters
val update_fix  : (fix -> fix) -> parameters -> parameters

(* The type of finite models *)
type model

(* Basic operations *)
val new  : parameters -> model
val size : model -> int

(* Evaluate ground terms and sentences *)
val evaluate_term    : model -> term -> int
val evaluate_formula : model -> formula -> bool

(* Check whether a random grounding of a formula is satisfied by the model *)
val check  : model -> formula -> bool
val checkn : model -> formula -> int -> int
val count  : model -> formula -> int * int  (* num of satisfying groundings *)

(* Try to make formulas true by applying random perturbations to the model *)
val perturb : formula list -> int -> model -> model

(* Pretty-printing *)
val pp_model          : model pp
val term_to_string    : model -> term -> string
val formula_to_string : model -> formula -> string

end
