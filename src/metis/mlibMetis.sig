(* ========================================================================= *)
(* THE METIS COMBINATION OF PROOF PROCEDURES FOR FIRST-ORDER LOGIC           *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibMetis =
sig

(* mlibMetis trace levels:
   0: No output
   1: Status information during proof search
   2: More detailed prover information: slice by slice
   3: High-level proof search information
   4: Log of every inference during proof search
   5: mlibSupport infrastructure such as mlibTermorder *)

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
type parameters = (mlibSolver.cost_fn * prover) list

val defaults             : parameters
val parameters_to_string : parameters -> string

(* The metis combination of solvers *)
val metis' : parameters -> solver_node
val metis  : solver_node                (* Uses defaults *)

(* A user-friendly interface *)
val settings : parameters ref           (* Initially defaults *)
val limit    : limit ref                (* Initially unlimited *)
val options  : mlibUseful.Opt list          (* Command-line options *)
val prove    : formula -> thm option    (* Adds eq axioms, converts to CNF *)
val query    : formula -> solver        (* Prolog query engine *)

end
