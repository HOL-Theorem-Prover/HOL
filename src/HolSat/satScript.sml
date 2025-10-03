
(* random theorems used here, there, everywhere by HolSatLib *)
Theory sat[bare]
Ancestors
  bool
Libs
  Globals HolKernel Parse Drule Thm Tactical Tactic Rewrite


(* gross truth table method for proving propositional tautologies *)
(* used to bootstrap HolSatLib *)
fun TT_TAUT_PROVE tm =
    let val (qv,tm) = boolSyntax.strip_forall tm
        val fv = free_vars tm
    in GENL qv (prove(tm,(MAP_EVERY BOOL_CASES_TAC fv) THEN REWRITE_TAC [])) end

Theorem AND_IMP =
  TT_TAUT_PROVE ``!A B C. A /\ B ==> C <=> A ==> B ==> C``
Theorem NOT_NOT =
  GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))
Theorem AND_INV = TT_TAUT_PROVE ``!A. ~A /\ A <=> F``
Theorem AND_INV_IMP = TT_TAUT_PROVE ``!A. A ==> ~A ==> F``
Theorem OR_DUAL =
  TT_TAUT_PROVE ``(~(A \/ B) ==> F) = (~A ==> ~B ==> F)``
Theorem OR_DUAL2 =
  TT_TAUT_PROVE ``(~(A \/ B) ==> F) = ((A==>F) ==> ~B ==> F)``
Theorem OR_DUAL3 =
  TT_TAUT_PROVE ``(~(~A \/ B) ==> F) = (A ==> ~B ==> F)``
Theorem AND_INV2 =
  TT_TAUT_PROVE ``(~A ==> F) ==> (A==>F) ==> F``
Theorem NOT_ELIM2 = TT_TAUT_PROVE ``(~A ==> F) = A``

(* for satTools.sml *)
Theorem EQT_Imp1 = TT_TAUT_PROVE ``!b. b ==> (b=T)``
Theorem EQF_Imp1 = TT_TAUT_PROVE ``!b. (~b) ==> (b=F)``

(* for def_cnf.sml *)
Theorem dc_eq =
   TT_TAUT_PROVE “(p = (q = r)) <=>
                    (p \/ q \/ r) /\ (p \/ ~r \/ ~q) /\ (q \/ ~r \/ ~p) /\
                    (r \/ ~q \/ ~p)”

Theorem dc_conj =
  TT_TAUT_PROVE “(p = (q /\ r)) <=> (p \/ ~q \/ ~r) /\ (q \/ ~p) /\ (r \/ ~p)”

Theorem dc_disj =
  TT_TAUT_PROVE “(p = (q \/ r)) <=> (p \/ ~q) /\ (p \/ ~r) /\ (q \/ r \/ ~p)”

Theorem dc_imp =
  TT_TAUT_PROVE “(p = (q ==> r)) <=> (p \/ q) /\ (p \/ ~r) /\ (~q \/ r \/ ~p)”

Theorem dc_neg = TT_TAUT_PROVE “(p = ~q) <=> (p \/ q) /\ (~q \/ ~p)”

Theorem dc_cond =
  TT_TAUT_PROVE “(p = (if q then r else s)) <=>
                   (p \/ q \/ ~s) /\ (p \/ ~r \/ ~q) /\ (p \/ ~r \/ ~s) /\
                   (~q \/ r \/ ~p) /\ (q \/ s \/ ~p)”

val [pth_ni1, pth_ni2, pth_no1, pth_no2, pth_an1, pth_an2, pth_nn] =
            (CONJUNCTS o TT_TAUT_PROVE)
             ``(~(p ==> q) ==> p)  /\ (~(p ==> q) ==> ~q)
            /\ (~(p \/ q)  ==> ~p) /\ (~(p \/ q)  ==> ~q)
            /\ ((p /\ q)   ==> p)  /\ ((p /\ q)   ==> q)
            /\ ((~ ~p)     ==> p)``
val _ = List.map save_thm (
  ListPair.zip(["pth_ni1", "pth_ni2", "pth_no1", "pth_no2", "pth_an1",
                "pth_an2", "pth_nn"],
               [pth_ni1, pth_ni2, pth_no1, pth_no2, pth_an1, pth_an2, pth_nn]));

