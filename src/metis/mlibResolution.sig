(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

signature mlibResolution =
sig

type solver_node = mlibSolver.solver_node

(* Tuning parameters *)
type parameters =
  {subsumption_checking : int,                    (* in the range 0..3 *)
   positive_refinement  : bool,
   theap_parm           : mlibTheap.parameters}

val defaults : parameters

(* Resolution *)
val resolution' : parameters -> solver_node
val resolution  : solver_node                     (* Uses defaults *)

end