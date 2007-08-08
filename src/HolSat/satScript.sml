
(* random theorems used here, there, everywhere by HolSatLib *)

open Globals HolKernel Parse Drule Thm boolTheory Tactical Tactic Rewrite

val _ = new_theory "sat";

(* gross truth table method for proving propositional tautologies *)
(* used to bootstrap HolSatLib *)
fun TT_TAUT_PROVE tm = 
    let val (qv,tm) = boolSyntax.strip_forall tm
	val fv = free_vars tm
    in GENL qv (prove(tm,(MAP_EVERY BOOL_CASES_TAC fv) THEN REWRITE_TAC [])) end

val AND_IMP = save_thm("AND_IMP",TT_TAUT_PROVE ``!A B C. A /\ B ==> C = A ==> B ==> C``) 
val NOT_NOT = save_thm("NOT_NOT",GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))) 
val AND_INV = save_thm("AND_INV",TT_TAUT_PROVE ``!A. ~A /\ A = F``) 
val AND_INV_IMP = save_thm("AND_INV_IMP",TT_TAUT_PROVE ``!A. A ==> ~A ==> F``) 
val OR_DUAL = save_thm("OR_DUAL", TT_TAUT_PROVE ``(~(A \/ B) ==> F) = (~A ==> ~B ==> F)``) 
val OR_DUAL2 = save_thm("OR_DUAL2",TT_TAUT_PROVE ``(~(A \/ B) ==> F) = ((A==>F) ==> ~B ==> F)``)
val OR_DUAL3 = save_thm("OR_DUAL3",TT_TAUT_PROVE ``(~(~A \/ B) ==> F) = (A ==> ~B ==> F)``)
val AND_INV2 = save_thm("AND_INV2",TT_TAUT_PROVE ``(~A ==> F) ==> (A==>F) ==> F``)
val NOT_ELIM2 = save_thm("NOT_ELIM2",TT_TAUT_PROVE ``(~A ==> F) = A``)

(* for satTools.sml *)
val EQT_Imp1 = save_thm("EQT_Imp1",TT_TAUT_PROVE ``!b. b ==> (b=T)``)
val EQF_Imp1 = save_thm("EQF_Imp1",TT_TAUT_PROVE ``!b. (~b) ==> (b=F)``)

(* for def_cnf.sml *)
val dc_eq = save_thm("dc_eq",TT_TAUT_PROVE ``(p = (q = r)) = 
(p \/ q \/ r) /\ (p \/ ~r \/ ~q) /\ (q \/ ~r \/ ~p) /\ (r \/ ~q \/ ~p)``)

val dc_conj = save_thm("dc_conj",TT_TAUT_PROVE ``(p = (q /\ r)) = (p \/ ~q \/ ~r) /\ (q \/ ~p) /\ (r \/ ~p)``)

val dc_disj = save_thm("dc_disj",TT_TAUT_PROVE ``(p = (q \/ r)) = (p \/ ~q) /\ (p \/ ~r) /\ (q \/ r \/ ~p)``) 

val dc_imp = save_thm("dc_imp",TT_TAUT_PROVE ``(p = (q ==> r)) = (p \/ q) /\ (p \/ ~r) /\ (~q \/ r \/ ~p)``) 

val dc_neg = save_thm("dc_neg",TT_TAUT_PROVE ``(p = ~q) = (p \/ q) /\ (~q \/ ~p)``)

val dc_cond = save_thm("dc_cond",TT_TAUT_PROVE ``(p = (if q then r else s)) =
       (p \/ q \/ ~s) /\ (p \/ ~r \/ ~q) /\ (p \/ ~r \/ ~s) /\
       (~q \/ r \/ ~p) /\ (q \/ s \/ ~p)``);

val [pth_ni1, pth_ni2, pth_no1, pth_no2, pth_an1, pth_an2, pth_nn] = 
	    (CONJUNCTS o TT_TAUT_PROVE)
	     ``(~(p ==> q) ==> p)  /\ (~(p ==> q) ==> ~q) 
	    /\ (~(p \/ q)  ==> ~p) /\ (~(p \/ q)  ==> ~q) 
	    /\ ((p /\ q)   ==> p)  /\ ((p /\ q)   ==> q) 
	    /\ ((~ ~p)     ==> p)`` 
val _ = List.map save_thm (ListPair.zip(["pth_ni1", "pth_ni2", "pth_no1", "pth_no2", "pth_an1", "pth_an2", "pth_nn"],[pth_ni1, pth_ni2, pth_no1, pth_no2, pth_an1, pth_an2, pth_nn]));

val _ = export_theory();
