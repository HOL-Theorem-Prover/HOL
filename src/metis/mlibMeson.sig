(* ========================================================================= *)
(* THE MESON PROOF PROCEDURE                                                 *)
(* Created by Joe Hurd, November 2001                                        *)
(* Partly ported from the CAML-Light code accompanying John Harrison's book  *)
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
   unit_lemmaizing  : bool}

val defaults                : parameters
val update_ancestor_pruning : (bool -> bool) -> parameters -> parameters
val update_ancestor_cutting : (bool -> bool) -> parameters -> parameters
val update_state_simplify   : (bool -> bool) -> parameters -> parameters
val update_cache_cutting    : (bool -> bool) -> parameters -> parameters
val update_divide_conquer   : (bool -> bool) -> parameters -> parameters
val update_unit_lemmaizing  : (bool -> bool) -> parameters -> parameters

(* The meson solver *)
val meson' : parameters -> solver_node
val meson  : solver_node                          (* Uses defaults *)

(* The delta preprocessor as a solver *)
val delta' : parameters -> solver_node
val delta  : solver_node                          (* Uses defaults *)

(* The prolog solver *)
val prolog' : parameters -> solver_node
val prolog  : solver_node                         (* Uses defaults *)

end