(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Created by Joe Hurd, November 2001                                        *)
(* ========================================================================= *)

signature mlibResolution =
sig

type parameters =
  {restart     : int option,
   clause_parm : mlibClause.parameters,
   sos_parm    : mlibSupport.parameters}
val defaults : parameters

val resolution' : parameters -> mlibSolver.solver_node
val resolution  : mlibSolver.solver_node             (* Uses defaults *)

end