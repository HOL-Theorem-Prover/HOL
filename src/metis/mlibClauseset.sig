(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibClauseset =
sig

type 'a pp  = 'a mlibUseful.pp
type clause = mlibClause.clause

type filter = {subsumption : bool, simplification : int, splitting : bool}
type parameters = {prefactoring : filter, postfactoring : filter}

val defaults              : parameters
val update_subsumption    : (bool -> bool) -> filter -> filter
val update_simplification : (int -> int) -> filter -> filter
val update_splitting      : (bool -> bool) -> filter -> filter
val update_prefactoring   : (filter -> filter) -> parameters -> parameters
val update_postfactoring  : (filter -> filter) -> parameters -> parameters

(* mlibClause sets *)
type clauseset
val empty     : mlibClause.parameters * parameters -> clauseset
val parm      : clauseset -> mlibClause.parameters * parameters
val size      : clauseset -> int
val units     : clauseset -> mlibUnits.units
val rewrites  : clauseset -> mlibClause.rewrs
val clauses   : clauseset -> clause list
val new_units : mlibUnits.units -> clauseset -> clauseset

(* Simplify and strengthen clauses *)
val simplify   : clauseset -> clause -> clause
val strengthen : clauseset -> clause -> clause option

(* Forward subsumption checking *)
val subsumed : clauseset -> clause -> bool

(* Add a clause into the set *)
val add : clause -> clauseset -> clauseset

(* Derive (unfactored) consequences of a clause *)
val deduce : clauseset -> clause -> clause list

(* Factor clauses *)
val factor : clause list -> clauseset -> clause list * clauseset

(* Pretty-printing *)
val pp_clauseset : clauseset pp

end
