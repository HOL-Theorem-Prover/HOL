open HolKernel boolLib Parse BasicProvers metisLib

open simpLib boolSimps

val _ = new_theory "TermRewriting"

(* simple results about things like confluence and normalisation *)

open relationTheory

(* definitions *)

val diamond_def = new_definition(
  "diamond_def",
  ``diamond (R:'a->'a->bool) = !x y z. R x y /\ R x z ==> ?u. R y u /\ R z u``)

val rcdiamond_def = new_definition( (* reflexive closure half diamond *)
  "rcdiamond_def",
  ``rcdiamond (R:'a->'a->bool) =
      !x y z. R x y /\ R x z ==> ?u. RC R y u /\ RC R z u``);

val CR_def = new_definition( (* Church-Rosser *)
  "CR_def",
  ``CR R = diamond (RTC R)``);

val WCR_def = new_definition( (* weakly Church-Rosser *)
  "WCR_def",
  ``WCR R = !x y z. R x y /\ R x z ==> ?u. RTC R y u /\ RTC R z u``);

val SN_def = new_definition( (* strongly normalising *)
  "SN_def",
  ``SN R = WF (inv R)``);

val nf_def = new_definition( (* normal-form *)
  "nf_def",
  ``nf R x = !y. ~R x y``)

(* results *)

(* that proving rcdiamond R is equivalent to establishing diamond (RC R) *)
val rcdiamond_diamond = store_thm(
  "rcdiamond_diamond",
  ``!R. rcdiamond R = diamond (RC R)``,
  SRW_TAC [][rcdiamond_def, diamond_def, RC_DEF] THEN
  METIS_TAC []); (* PROVE_TAC can't cope with this *)

val diamond_RC_diamond = store_thm(
  "diamond_RC_diamond",
  ``!R. diamond R ==> diamond (RC R)``,
  SRW_TAC [][diamond_def, RC_DEF] THEN METIS_TAC []);

val diamond_TC_diamond = store_thm(
  "diamond_TC_diamond",
  ``!R. diamond R ==> diamond (TC R)``,
  REWRITE_TAC [diamond_def] THEN GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!x y. TC R x y ==> !z. TC R x z ==> ?u. TC R y u /\ TC R z u` THEN1
        METIS_TAC [] THEN
  HO_MATCH_MP_TAC TC_INDUCT_LEFT1 THEN
  Q.SUBGOAL_THEN
    `!x y. TC R x y ==> !z. R x z ==> ?u. TC R y u /\ TC R z u`
    ASSUME_TAC
  THENL [
    HO_MATCH_MP_TAC TC_INDUCT_LEFT1 THEN PROVE_TAC [TC_RULES],
    ALL_TAC (* METIS_TAC very slow in comparison on line above *)
  ] THEN PROVE_TAC [TC_RULES]);

val RTC_eq_TCRC = prove(
  ``RTC R = TC (RC R)``,
  REWRITE_TAC [TC_RC_EQNS]);

val establish_CR = store_thm(
  "establish_CR",
  ``!R. (rcdiamond R ==> CR R) /\ (diamond R ==> CR R)``,
  REWRITE_TAC [CR_def, RTC_eq_TCRC] THEN
  PROVE_TAC [diamond_RC_diamond, rcdiamond_diamond, diamond_TC_diamond]);

fun (g by tac) =
    Q.SUBGOAL_THEN g STRIP_ASSUME_TAC THEN1 tac

val Newmans_lemma = store_thm(
  "Newmans_lemma",
  ``!R. WCR R /\ SN R ==> CR R``,
  REPEAT STRIP_TAC THEN
  `WF (TC (inv R))` by PROVE_TAC [WF_TC, SN_def] THEN
  REWRITE_TAC [CR_def, diamond_def] THEN
  POP_ASSUM (HO_MATCH_MP_TAC o MATCH_MP WF_INDUCTION_THM) THEN
  SRW_TAC [][inv_MOVES_OUT, inv_DEF] THEN
  `(x = y) \/ ?y1. R x y1 /\ RTC R y1 y` by PROVE_TAC [RTC_CASES1] THENL [
    SRW_TAC [][] THEN PROVE_TAC [RTC_RULES],
    ALL_TAC
  ] THEN
  `(x = z) \/ ?z1. R x z1 /\ RTC R z1 z` by PROVE_TAC [RTC_CASES1] THENL [
    SRW_TAC [][] THEN PROVE_TAC [RTC_RULES],
    ALL_TAC
  ] THEN
  `?x0. RTC R y1 x0 /\ RTC R z1 x0` by PROVE_TAC [WCR_def] THEN
  `TC R x y1 /\ TC R x z1` by PROVE_TAC [TC_RULES] THEN
  `?y2. RTC R y y2 /\ RTC R x0 y2` by PROVE_TAC [] THEN
  `?z2. RTC R z z2 /\ RTC R x0 z2` by PROVE_TAC [] THEN
  `TC R x x0` by PROVE_TAC [EXTEND_RTC_TC] THEN
  PROVE_TAC [RTC_RTC]);



val _ = export_theory()