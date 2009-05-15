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


val _ = export_theory()
