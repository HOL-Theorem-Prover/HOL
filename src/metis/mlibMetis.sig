(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibMetis =
sig

(* mlibMetis trace levels:
   0: No output
   1: Status information during proof search
   2: More status information
   3: More detailed prover information: slice by slice
   4: High-level proof search information
   5: Log of every inference during proof search
   6: mlibSupport infrastructure such as mlibTermorder *)

type formula     = mlibTerm.formula
type thm         = mlibThm.thm
type limit       = mlibMeter.limit
type solver      = mlibSolver.solver
type solver_node = mlibSolver.solver_node

(* Tuning parameters *)
datatype prover =
  mlibResolution of mlibResolution.parameters
| mlibMeson of mlibMeson.parameters
| Delta of mlibMeson.parameters
type prover_parameters = prover * mlibSolver.sos_filter option * mlibSolver.cost_fn
type parameters = prover_parameters list

val default_resolution   : prover_parameters
val ordered_resolution   : prover_parameters
val default_meson        : prover_parameters
val default_delta        : prover_parameters
val defaults             : parameters
val parameters_to_string : parameters -> string

(* The metis combination of solvers *)
val metis' : parameters -> solver_node
val metis  : solver_node                (* Uses defaults *)

(* A user-friendly interface *)
val settings : parameters ref           (* Initially defaults *)
val limit    : limit ref                (* Initially unlimited *)
val prove    : formula -> thm option    (* Axiomatizes, then runs metis *)
val query    : formula -> solver        (* Axiomatizes, then runs prolog *)

end
