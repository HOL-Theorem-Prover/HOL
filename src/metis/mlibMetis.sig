(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibMetis =
sig

(* Metis trace levels:
   0: No output
   1: Status information during proof search
   2: More detailed prover information: slice by slice
   3: High-level proof search information
   4: Log of every inference during proof search *)

type formula     = mlibTerm.formula
type thm         = mlibThm.thm
type limit       = mlibMeter.limit
type solver      = mlibSolver.solver
type solver_node = mlibSolver.solver_node

(* Tuning parameters *)
type Mparm = mlibMeson.parameters
type Rparm = mlibResolution.parameters
type parameters =
  {resolution      : bool,
   meson           : bool,
   delta           : bool,
   resolution_parm : Rparm,
   meson_parm      : Mparm}

val defaults                    : parameters
val update_parm_resolution      : (bool -> bool) -> parameters -> parameters
val update_parm_meson           : (bool -> bool) -> parameters -> parameters
val update_parm_delta           : (bool -> bool) -> parameters -> parameters
val update_parm_resolution_parm : (Rparm -> Rparm) -> parameters -> parameters
val update_parm_meson_parm      : (Mparm -> Mparm) -> parameters -> parameters

(* The metis combination of solvers *)
val metis' : parameters -> solver_node
val metis  : solver_node                (* Uses defaults *)

(* A user-friendly interface *)
val settings : parameters ref           (* Initialially defaults *)
val limit    : limit ref                (* Initialially unlimited *)
val prove    : formula -> thm option    (* Adds eq axioms, converts to CNF *)
val query    : formula -> solver        (* Prolog query engine *)

end