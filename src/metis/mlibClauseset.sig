(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Created by Joe Hurd, October 2002                                         *)
(* ========================================================================= *)

signature mlibClauseset =
sig

type 'a pp  = 'a mlibUseful.pp
type units  = mlibUnits.units
type clause = mlibClause.clause

type parameters =
  {subsumption    : int,                (* Takes values 0..2 *)
   simplification : int}                (* Takes values 0..2 *)

val defaults              : parameters
val update_subsumption    : (int -> int) -> parameters -> parameters
val update_simplification : (int -> int) -> parameters -> parameters

(* id_clauses are clauses stamped with an id number *)
type id_clause
val dest_id_clause       : id_clause -> int * clause
val empty_id_clause      : id_clause -> clause option
val pp_id_clause         : id_clause pp
val id_clause_to_string  : id_clause -> string
val id_clauses_to_string : id_clause list -> string

(* Basic operations on clausesets *)
type clauseset
val empty    : mlibClause.parameters * parameters -> clauseset
val reset    : clauseset -> id_clause list * clauseset
val size     : clauseset -> int
val rewrites : clauseset -> mlibThm.thm list
val clauses  : clauseset -> mlibThm.thm list

(* Simplify and strengthen clauses *)
val simplify   : clauseset -> id_clause -> id_clause
val strengthen : clauseset -> units -> id_clause -> id_clause option

(* Forward subsumption checking *)
val subsumed : clauseset -> id_clause -> bool

(* Initialize clauses *)
val initialize : clause list*clauseset*units -> id_clause list*clauseset*units

(* Add a clause into the set and derive consequences *)
val add : clauseset -> units -> id_clause -> clause list * clauseset

(* Pretty-printing *)
val pp_clauseset : clauseset pp

end
