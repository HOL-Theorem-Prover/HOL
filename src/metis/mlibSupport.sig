(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibSupport =
sig

type 'a pp   = 'a mlibUseful.pp
type formula = mlibTerm.formula
type clause  = mlibClause.clause

type parameters =
  {size_power    : real,
   literal_power : real,
   model_power   : real,
   model_perts   : int,
   model_checks  : int,
   model_parms   : mlibModel.parameters list}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults             : parameters
val update_size_power    : real parmupdate
val update_literal_power : real parmupdate
val update_model_power   : real parmupdate
val update_model_perts   : int parmupdate
val update_model_checks  : int parmupdate
val update_model_parms   : mlibModel.parameters list parmupdate

(* The set of support type *)
type sos
type distance

(* Basic operations *)
val new     : parameters -> formula list -> clause list -> sos
val size    : sos -> int
val to_list : sos -> clause list
val pp_sos  : sos pp

(* Adding new clauses *)
val add : distance * clause list -> sos -> sos

(* Removing the lightest clause *)
val remove : sos -> ((distance * clause) * sos) option

end
