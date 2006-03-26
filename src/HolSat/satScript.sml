
open Globals HolKernel Parse 

open Drule Thm boolTheory tautLib

val _ = new_theory "sat";

val AND_IMP = save_thm("AND_IMP",TAUT_PROVE ``!A B C. A /\ B ==> C = A ==> B ==> C``) 
val NOT_NOT = save_thm("NOT_NOT",GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))) 
val AND_INV = save_thm("AND_INV",TAUT_PROVE ``!A. ~A /\ A = F``) 
val AND_INV_IMP = save_thm("AND_INV_IMP",TAUT_PROVE ``!A. A ==> ~A ==> F``) 
val OR_DUAL = save_thm("OR_DUAL", TAUT_PROVE ``(~(A \/ B) ==> F) = (~A ==> ~B ==> F)``) 

val _ = export_theory();
