(* ========================================================================= *)
(* PROCESSING SETS OF CLAUSES AT A TIME                                      *)
(* Created by Joe Hurd, October 2002                                         *)
(* ========================================================================= *)

signature mlibClauseset1 =
sig

type 'a pp  = 'a mlibUseful.pp
type units  = mlibUnits.units
type clause = mlibClause.clause

type clauseset

val empty        : clauseset
val reset        : clauseset -> clauseset
val size         : clauseset -> int
val add          : clause -> clauseset -> clauseset
val addl         : clause list -> clauseset -> clauseset
val simplify     : clauseset -> clause -> clause
val subsumed     : clauseset -> clause -> bool
val initialize   : clauseset -> units -> clause list -> clause list
val deduce       : clauseset -> units -> clause -> clause list
val pp_clauseset : clauseset pp

end