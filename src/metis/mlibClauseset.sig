(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Created by Joe Hurd, October 2002                                         *)
(* ========================================================================= *)

signature mlibClauseset =
sig

type 'a pp  = 'a mlibUseful.pp
type clause = mlibClause.clause

type parameters =
  {subsumption    : int,                (* Takes values 0..2 *)
   simplification : int,                (* Takes values 0..2 *)
   splitting      : int}                (* Takes values 0..2 *)

val defaults              : parameters
val update_subsumption    : (int -> int) -> parameters -> parameters
val update_simplification : (int -> int) -> parameters -> parameters
val update_splitting      : (int -> int) -> parameters -> parameters

(* mlibClause sets *)
type clauseset
val empty     : mlibClause.parameters * parameters -> clauseset
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

(* Derive consequences of a clause *)
val deduce : clauseset -> clause -> clause list

(* Initialize derived clauses *)
val initialize : clause list -> clauseset -> clause list * clauseset

(* Pretty-printing *)
val pp_clauseset : clauseset pp

end
