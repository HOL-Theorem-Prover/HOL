(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

signature mlibResolution =
sig

type 'a pp  = 'a mlibUseful.pp
type clause = mlibClause.clause

type parameters =
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   set_parm    : mlibClauseset.parameters,
   sos_parm    : mlibSupport.parameters}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults           : parameters
val update_restart     : int option parmupdate
val update_clause_parm : mlibClause.parameters parmupdate
val update_set_parm    : mlibClauseset.parameters parmupdate
val update_sos_parm    : mlibSupport.parameters parmupdate

(* mlibResolution *)
type resolution
type components = {iter : int, set : mlibClauseset.clauseset, sos : mlibSupport.sos}
val new       : parameters -> resolution
val dest      : resolution -> components
val overlay   : components -> resolution -> resolution
val size      : resolution -> {used : int, waiting : int, rewrites : int}
val add       : clause list -> resolution -> resolution
val check     : resolution -> bool       (* checks weight against max weight *)
val calibrate : (int -> int) -> resolution -> resolution  (* sets max weight *)
val restart   : resolution -> resolution
val select    : resolution -> ((real * clause) * resolution) option
val deduce    : (real * clause) * resolution -> resolution
val advance   : resolution -> resolution option     (* check, select, deduce *)
val pp_resolution : resolution pp

(* The resolution procedure as a solver_node *)
val resolution' : parameters -> mlibSolver.solver_node
val resolution  : mlibSolver.solver_node                        (* uses defaults *)

end
