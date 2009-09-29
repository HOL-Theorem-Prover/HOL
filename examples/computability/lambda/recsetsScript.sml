open HolKernel Parse bossLib boolLib

val _ = new_theory "recsets"

open recfunsTheory

val _ = set_trace "Unicode" 1

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val recursive_def = Define`
  recursive s = ∃M. ∀e. Phi M e = SOME (if e ∈ s then 1 else 0)
`;

(*
val bnf_of_lameq_CONG = store_thm(
  "bnf_of_lameq_CONG",
  ``M₁ == M₂ ⇒ (bnf_of M₁ = bnf_of M₂)``,
  Cases_on `bnf_of M₂` THENL [
    FULL_SIMP_TAC (srw_ss()) [normal_orderTheory.bnf_of_NONE,
                              chap2Theory.has_bnf_def] THEN
    METIS_TAC [chap2Theory.lam_eq_rules],
    IMP_RES_TAC normal_orderTheory.bnf_of_SOME THEN
    STRIP_TAC THEN
    `M₁ == x` by METIS_TAC [chap2Theory.lam_eq_rules,
                            normal_orderTheory.nstar_lameq] THEN
    `M₁ -n->* x` by

    `has_bnf M₂` by METIS_TAC [normal_orderTheory.has_bnf_of] THEN
    STRIP_TAC THEN
    Q_TAC SUFF_TAC `has_bnf M₂

    FULL_SIMP_TAC (srw_ss()) [

  SRW_TAC [][normal_orderTheory.has_bnf_of] THEN
*)

val empty_recursive = Store_thm(
  "empty_recursive",
  ``recursive {}``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 0)))` THEN
  SRW_TAC [][normal_orderTheory.bnf_of_def] THEN
  SRW_TAC [][Ntimes whileTheory.OWHILE_THM 2, normal_orderTheory.noreduct_thm,
             termTheory.lemma14b]);

val univ_recursive = Store_thm(
  "univ_recursive",
  ``recursive UNIV``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 1)))` THEN
  SRW_TAC [][normal_orderTheory.bnf_of_def] THEN
  SRW_TAC [][Ntimes whileTheory.OWHILE_THM 2, normal_orderTheory.noreduct_thm,
             termTheory.lemma14b]);


(*val union_recursive_I = Store_thm(
  "union_recursive_I",
  ``recursive s₁ ∧ recursive s₂ ⇒ recursive (s₁ ∪ s₂)``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm
              (LAM v (cmod @@ (cplus @@ (toTerm (numdB M) @@ VAR v)
                                     @@ (toTerm (numdB M') @@ VAR v))
                           @@ church 2)))` THEN
  SRW_TAC [][]
*)

val _ = export_theory ()
