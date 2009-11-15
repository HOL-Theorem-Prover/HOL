open HolKernel Parse boolLib bossLib

open churchDBTheory
open churchnumTheory
open pred_setTheory
open chap3Theory
open normal_orderTheory
open reductionEval

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = set_trace "Unicode" 1

val _ = new_theory "recfuns"


(* Phi lifts all possible lambda-terms into the space of num->num option,
   indexing into the lambda-terms with the enumeration.  The NONE result
   corresponds to a divergence. *)
val Phi_def = Define`
  Phi n m = OPTION_MAP force_num (bnf_of (toTerm (numdB n) @@ church m))
`;

val UM_def = Define`
  UM =
  LAM "nm"
    (cbnf_ofk @@ cforce_num @@ (cdAPP @@ (cnumdB @@ (cnfst @@ VAR "nm"))
                                      @@ (cchurch @@ (cnsnd @@ VAR "nm"))))
`;

val FV_UM = Store_thm(
  "FV_UM",
  ``FV UM = {}``,
  SRW_TAC [][UM_def, EXTENSION]);

val PhiSOME_UM_I = store_thm(
  "PhiSOME_UM_I",
  ``(Phi n m = SOME p) ⇒ UM @@ church (n ⊗ m) -n->* church p``,
  SRW_TAC [][Phi_def, UM_def] THEN
  SIMP_TAC (bsrw_ss()) [cnfst_behaviour, cnumdB_behaviour, cnsnd_behaviour,
                        cchurch_behaviour, cdAPP_behaviour] THEN
  IMP_RES_TAC cbnf_of_works1 THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  ASM_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour]);

val PhiNONE_UM = store_thm(
  "PhiNONE_UM",
  ``(Phi n m = NONE) ⇔ ¬has_bnf (UM @@ church (n ⊗ m))``,
  EQ_TAC THENL [
    SRW_TAC [][Phi_def] THEN REPEAT STRIP_TAC THEN
    `∃M. UM @@ church (n ⊗ m) == M ∧ bnf M`
      by METIS_TAC [has_bnf_thm, betastar_lameq_bnf] THEN
    Q.PAT_ASSUM `X == Y` MP_TAC THEN
    SIMP_TAC (bsrw_ss()) [UM_def, cnfst_behaviour, cnsnd_behaviour,
                          cdAPP_behaviour, cnumdB_behaviour,
                          cchurch_behaviour] THEN
    STRIP_TAC THEN
    `cbnf_ofk @@ cforce_num @@ cDB (dAPP (numdB n) (fromTerm (church m)))
       -n->* M`
      by METIS_TAC [betastar_lameq_bnf, nstar_betastar_bnf] THEN
    IMP_RES_TAC cbnf_ofk_works2 THEN
    FULL_SIMP_TAC (srw_ss()) [],

    Cases_on `Phi n m` THEN SRW_TAC [][] THEN
    IMP_RES_TAC PhiSOME_UM_I THEN
    METIS_TAC [nstar_betastar, bnf_church, has_bnf_thm]
  ]);

(* effectively the other case for PhiSOME_UM *)
val UM_bnf = store_thm(
  "UM_bnf",
  ``UM @@ church (n ⊗ m) == M ∧ bnf M ⇒
    ∃p. (Phi n m = SOME p) ∧ (M = church p)``,
  REPEAT STRIP_TAC THEN Cases_on `Phi n m` THEN SRW_TAC [][] THENL [
    METIS_TAC [PhiNONE_UM, has_bnf_thm, betastar_lameq_bnf],
    `UM @@ church (n ⊗ m) == church x`
      by METIS_TAC [PhiSOME_UM_I, nstar_lameq] THEN
    METIS_TAC [betastar_lameq_bnf,  bnf_reduction_to_self, bnf_triangle,
               bnf_church]
  ]);

val PhiSOME_UM = store_thm(
  "PhiSOME_UM",
  ``(Phi n m = SOME p) ⇔ UM @@ church (n ⊗ m) -n->* church p``,
  EQ_TAC THEN SRW_TAC [][PhiSOME_UM_I] THEN
  MATCH_MP_TAC
    (UM_bnf |> Q.INST [`M` |-> `church p`] |> SIMP_RULE (srw_ss()) []) THEN
  ASM_SIMP_TAC (bsrw_ss()) []);

(* Phi and its connection to cbnf_ofk *)
val cbnf_of_works1' =
    cbnf_of_works1 |> Q.INST [`M` |-> `toTerm dM`, `N` |-> `toTerm dN`]
                   |> SIMP_RULE (srw_ss()) []

val PhiSOME_cbnf_ofk = store_thm(
  "PhiSOME_cbnf_ofk",
  ``(Phi N e = SOME z) ⇒
    ∃v.
      (∀k. cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e))) ==
           k @@ cDB v) ∧
      (z = force_num (toTerm v))``,
  STRIP_TAC THEN
  `UM @@ church (N ⊗ e) -n->* church z`
    by FULL_SIMP_TAC (srw_ss()) [PhiSOME_UM] THEN
  FULL_SIMP_TAC (bsrw_ss()) [UM_def, cnfst_behaviour,
                             cchurch_behaviour, cnsnd_behaviour,
                             cnumdB_behaviour, cdAPP_behaviour] THEN
  `∃z'. (bnf_of (toTerm (dAPP (numdB N) (fromTerm (church e)))) =
         SOME (toTerm z')) ∧
        cforce_num @@ cDB z' -n->* church z`
      by METIS_TAC [cbnf_ofk_works2, bnf_church, nstar_betastar_bnf,
                    chap3Theory.betastar_lameq_bnf] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC (bsrw_ss()) [cforce_num_behaviour] THEN STRIP_TAC THEN
  IMP_RES_TAC cbnf_of_works1' THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  METIS_TAC [chap2Theory.lameq_refl]);

val optlemma = prove(
  ``(x ≠ NONE) ⇔ ∃z. x = SOME z``,
  Cases_on `x` THEN SRW_TAC [][]);

val PhiNONE_cbnf_ofk = store_thm(
  "PhiNONE_cbnf_ofk",
  ``(Phi N e = NONE) ⇒
    (bnf_of (cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e)))) =
     NONE)``,
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [optlemma] THEN
  `cbnf_ofk @@ k @@ cDB (dAPP (numdB N) (fromTerm (church e))) -n->* z ∧
   bnf z`
     by METIS_TAC [bnf_of_SOME] THEN
  `∃v. (bnf_of (toTerm (dAPP (numdB N) (fromTerm (church e)))) =
        SOME (toTerm v)) ∧
       k @@ cDB v -n->* z`
     by METIS_TAC [cbnf_ofk_works2] THEN
  SRW_TAC [][Phi_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val bnf_of_UM = store_thm(
  "bnf_of_UM",
  ``bnf_of (UM @@ church n) =
    OPTION_MAP (church o force_num)
               (bnf_of (toTerm (numdB (nfst n)) @@ church (nsnd n)))``,
  SIMP_TAC (bsrw_ss()) [UM_def, cnsnd_behaviour, cchurch_behaviour,
                        cnumdB_behaviour, cnfst_behaviour, cdAPP_behaviour] THEN
  Cases_on `bnf_of (toTerm (numdB (nfst n)) @@ church (nsnd n))` THENL [
    IMP_RES_TAC bnfNONE_cbnf_ofk_fails THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [bnf_of_NONE],

    IMP_RES_TAC cbnf_of_works1 THEN
    FULL_SIMP_TAC (bsrw_ss()) [cforce_num_behaviour, bnf_bnf_of]
  ]);

val _ = export_theory()
