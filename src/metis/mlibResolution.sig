(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibResolution =
sig

type 'a pp    = 'a mlibUseful.pp
type thm      = mlibThm.thm
type units    = mlibUnits.units
type clause   = mlibClause.clause
type distance = mlibSupport.distance

type parameters =
  {clause_parm : mlibClause.parameters,
   set_parm    : mlibClauseset.parameters,
   sos_parm    : mlibSupport.parameters}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults           : parameters
val update_clause_parm : mlibClause.parameters parmupdate
val update_set_parm    : mlibClauseset.parameters parmupdate
val update_sos_parm    : mlibSupport.parameters parmupdate

(* mlibResolution *)
type resolution
val new       : parameters * units * thm list * thm list -> resolution
val dest      : resolution -> {set : mlibClauseset.clauseset, sos : mlibSupport.sos}
val size      : resolution -> {used : int, waiting : int, rewrites : int}
val units     : resolution -> units
val new_units : units -> resolution -> resolution
val select    : resolution -> ((distance * clause) * resolution) option
val deduce    : clause -> resolution -> clause list
val factor    : clause list -> resolution -> clause list * resolution
val add       : distance * clause list -> resolution -> resolution
val advance   : resolution -> resolution option  (* select deduce factor add *)
val pp_resolution : resolution pp

(* The resolution procedure as a solver_node *)
val resolution' : string * parameters -> mlibSolver.solver_node
val resolution  : mlibSolver.solver_node                        (* uses defaults *)

end
