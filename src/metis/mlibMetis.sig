(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibMetis =
sig

type formula     = mlibTerm.formula
type thm         = mlibThm.thm
type limit       = mlibMeter.limit
type solver      = mlibSolver.solver
type solver_node = mlibSolver.solver_node

(* Tuning parameters *)
type Mparm = mlibMeson.parameters
type Rparm = mlibResolution.parameters
type parameters =
  {meson           : bool,
   delta           : bool,
   resolution      : bool,
   meson_parm      : Mparm,
   resolution_parm : Rparm}

val defaults                    : parameters
val update_parm_meson           : (bool -> bool) -> parameters -> parameters
val update_parm_delta           : (bool -> bool) -> parameters -> parameters
val update_parm_resolution      : (bool -> bool) -> parameters -> parameters
val update_parm_meson_parm      : (Mparm -> Mparm) -> parameters -> parameters
val update_parm_resolution_parm : (Rparm -> Rparm) -> parameters -> parameters

(* The metis combination of solvers *)
val metis' : parameters -> solver_node
val metis  : solver_node                (* Uses defaults *)

(* A user-friendly interface *)
val settings  : parameters ref          (* Starts off as defaults *)
val limit     : limit ref               (* Starts off as 10 seconds *)
val raw_prove : formula -> thm option   (* Expects a ==> b ==> F *)
val prove     : formula -> thm option   (* Adds eq axioms, converts to CNF *)
val query     : formula -> solver       (* Prolog query engine *)

end