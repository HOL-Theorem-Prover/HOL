(* ========================================================================= *)
(* THE MESON PROOF PROCEDURE                                                 *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibMeson =
sig

type solver_node = mlibSolver.solver_node

(* Tuning parameters *)
type parameters =
  {ancestor_pruning : bool,
   ancestor_cutting : bool,
   state_simplify   : bool,
   cache_cutting    : bool,
   divide_conquer   : bool,
   unit_lemmaizing  : bool,
   sort_literals    : int,                        (* In the range [0..2] *)
   sort_rules       : bool}

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults                : parameters
val update_ancestor_pruning : bool Parmupdate
val update_ancestor_cutting : bool Parmupdate
val update_state_simplify   : bool Parmupdate
val update_cache_cutting    : bool Parmupdate
val update_divide_conquer   : bool Parmupdate
val update_unit_lemmaizing  : bool Parmupdate
val update_sort_literals    : int Parmupdate
val update_sort_rules       : bool Parmupdate

(* The meson solver *)
val meson' : string * parameters -> solver_node
val meson  : solver_node                          (* Uses defaults *)

(* The delta preprocessor as a solver *)
val delta' : string * parameters -> solver_node
val delta  : solver_node                          (* Uses defaults *)

(* The prolog solver *)
val prolog' : string * parameters -> solver_node
val prolog  : solver_node                         (* Uses defaults *)

end
