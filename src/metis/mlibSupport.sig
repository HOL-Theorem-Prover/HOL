(* ========================================================================= *)
(* THE SET OF SUPPORT                                                        *)
(* Created by Joe Hurd, April 2002                                           *)
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
   model_checks  : int,
   model_parms   : mlibModel.parameters list}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults             : parameters
val update_size_power    : real parmupdate
val update_literal_power : real parmupdate
val update_model_power   : real parmupdate
val update_model_checks  : int parmupdate
val update_model_parms   : mlibModel.parameters list parmupdate

(* The set of support type *)
type sos

(* Basic operations *)
val empty   : parameters -> formula list -> sos
val size    : sos -> int
val to_list : sos -> clause list
val pp_sos  : sos pp

(* Adding new clauses *)
val add : real * clause list -> sos -> sos

(* Removing the lightest clause *)
val remove : sos -> ((real * clause) * sos) option

(* Registering clauses in the models *)
val register : clause list -> sos -> sos

end
