(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

signature mlibResolution =
sig

type parameters =
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   sos_parm    : mlibSupport.parameters,
   set_parm    : mlibClauseset.parameters}

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults           : parameters
val update_restart     : int option Parmupdate
val update_clause_parm : mlibClause.parameters Parmupdate
val update_sos_parm    : mlibSupport.parameters Parmupdate
val update_set_parm    : mlibClauseset.parameters Parmupdate

(* An ugly way to get hold of the current state *)
val current_state : mlibClauseset.clauseset ref

(* The resolution procedure as a solver_node *)
val resolution' : parameters -> mlibSolver.solver_node
val resolution  : mlibSolver.solver_node             (* Uses defaults *)

end