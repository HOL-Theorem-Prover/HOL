
open Globals HolKernel Parse 

open Drule Thm boolTheory tautLib

val _ = new_theory "sat";

val AND_IMP = save_thm("AND_IMP",TAUT_PROVE ``!A B C. A /\ B ==> C = A ==> B ==> C``) 
val NOT_NOT = save_thm("NOT_NOT",GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))) 
val AND_INV = save_thm("AND_INV",TAUT_PROVE ``!A. ~A /\ A = F``) 
val AND_INV_IMP = save_thm("AND_INV_IMP",TAUT_PROVE ``!A. A ==> ~A ==> F``) 
val OR_DUAL = save_thm("OR_DUAL", TAUT_PROVE ``(~(A \/ B) ==> F) = (~A ==> ~B ==> F)``) 
val OR_DUAL2 = save_thm("OR_DUAL2",TAUT_PROVE ``(~(A \/ B) ==> F) = ((A==>F) ==> ~B ==> F)``)
val OR_DUAL3 = save_thm("OR_DUAL3",TAUT_PROVE ``(~(~A \/ B) ==> F) = (A ==> ~B ==> F)``)
val AND_INV2 = save_thm("AND_INV2",TAUT_PROVE ``(~A ==> F) ==> (A==>F) ==> F``)
val NOT_ELIM2 = save_thm("NOT_ELIM2",TAUT_PROVE ``(~A ==> F) = A``)

(* for def_cnf.sml *)
val dc_eq = save_thm("dc_eq",tautLib.TAUT_PROVE ``(p = (q = r)) = 
(p \/ q \/ r) /\ (p \/ ~r \/ ~q) /\ (q \/ ~r \/ ~p) /\ (r \/ ~q \/ ~p)``)

val dc_conj = save_thm("dc_conj",tautLib.TAUT_PROVE ``(p = (q /\ r)) = (p \/ ~q \/ ~r) /\ (q \/ ~p) /\ (r \/ ~p)``)

val dc_disj = save_thm("dc_disj",tautLib.TAUT_PROVE ``(p = (q \/ r)) = (p \/ ~q) /\ (p \/ ~r) /\ (q \/ r \/ ~p)``) 

val dc_imp = save_thm("dc_imp",tautLib.TAUT_PROVE ``(p = (q ==> r)) = (p \/ q) /\ (p \/ ~r) /\ (~q \/ r \/ ~p)``) 

val dc_neg = save_thm("dc_neg",tautLib.TAUT_PROVE ``(p = ~q) = (p \/ q) /\ (~q \/ ~p)``)

val _ = export_theory();
