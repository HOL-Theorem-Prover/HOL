(* theory stub about uncountable ordinals *)
open HolKernel Parse boolLib bossLib

open lcsymtacs
open pred_setTheory
open ordinalTheory cardinalTheory

open boolSimps

val _ = new_theory "ucord"

val _ = type_abbrev("ucinf", ``:('a + (num -> bool)) inf``)
val _ = type_abbrev("ucord", ``:('a + (num -> bool)) ordinal``)

val countable_cardeq = store_thm(
  "countable_cardeq",
  ``s ≈ t ⇒ (countable s ⇔ countable t)``,
  simp[countable_def, cardeq_def, EQ_IMP_THM] >>
  metis_tac [INJ_COMPOSE, BIJ_DEF, BIJ_LINV_BIJ]);

val UNIV_FUN_TO_BOOL = store_thm(
  "UNIV_FUN_TO_BOOL",
  ``univ(:'a -> bool) = POW univ(:'a)``,
  SIMP_TAC (srw_ss()) [EXTENSION, IN_POW]);

val ucinf_uncountable = store_thm(
  "ucinf_uncountable",
  ``¬countable 𝕌(:'a ucinf)``,
  simp[SUM_UNIV, UNIV_FUN_TO_BOOL, infinite_pow_uncountable]);



(*
val sup_exists_lemma = prove(
  ``{ a:'a ucord | countableOrd a } ≼ univ(:'a ucinf)``,
  spose_not_then assume_tac >> fs[cardlt_iso_REFL] >>
  `∃f. INJ f 𝕌(:'a ucinf) {a:'a ucord | countableOrd a}`
     by metis_tac[cardleq_def] >>
  `(∀u. countableOrd (f u)) ∧ (∀u v. f u = f v ⇒ u = v)`
      by fs[INJ_DEF] >>
  `¬SURJ f 𝕌(:'a ucinf) { a | countableOrd a}`
    by metis_tac [cardeq_def, BIJ_DEF] >>
  qabbrev_tac `fU = IMAGE f 𝕌(:'a ucinf)` >>
  `fU ≼ 𝕌(:'a ucinf)` by simp[Abbr`fU`, IMAGE_cardleq] >>
  first_assum (ASSUME_TAC o MATCH_MP (GEN_ALL sup_thm)) >>
  Cases_on `countableOrd (sup fU)`
  >- (`∀u. f u ≤ sup fU`
        by (gen_tac >> match_mp_tac suple_thm >> simp[Abbr`fU`]) >>
      qsuff_tac `𝕌(:'a ucinf) ≼ preds (sup fU)`
      >- (strip_tac >>
          `preds (sup fU) ≼ 𝕌(:num)` by fs[countable_thm] >>
          metis_tac[countable_thm, ucinf_uncountable, cardleq_TRANS]) >>
      Cases_on `∃u. f u = sup fU`
      >- (pop_assum strip_assume_tac >>
          `∀v. v ≠ u ⇒ f v < sup fU` by metis_tac[ordle_lteq] >>
          qabbrev_tac `U0 = 𝕌(:'a ucinf) DELETE u` >>
          `𝕌(:'a ucinf) = u INSERT U0` by metis_tac[INSERT_DELETE, IN_UNIV] >>
          `U0 ≈ 𝕌(:'a ucinf)`
             by metis_tac[finite_countable, FINITE_DELETE, ucinf_uncountable,
                          cardeq_SYM, CARDEQ_INSERT_RWT] >>
          `𝕌(:'a ucinf) DELETE u ≈ 𝕌(:'a ucinf)` >>
          qsuff_tac `U0 ≼ preds (sup fU)`
          >- metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
          simp[cardleq_def] >> qexists_tac `f` >>
          simp[INJ_DEF, Abbr`U0`]) >>
      pop_assum (fn th => `∀u. f u < sup fU` by metis_tac[ordle_lteq, th]) >>
      simp[cardleq_def] >> qexists_tac `f` >> simp[INJ_DEF]) >>
  `{ a:'a ucord | countableOrd a } ≼ preds (sup fU)`
    by (match_mp_tac SUBSET_CARDLEQ >> simp[SUBSET_DEF] >>
        qx_gen_tac `c` >> strip_tac >>
        spose_not_then assume_tac >>
        `sup fU ≤ c` by metis_tac[] >>
        `preds (sup fU) ⊆ preds c`
          by (simp[SUBSET_DEF] >> metis_tac [ordlte_TRANS]) >>
        metis_tac [subset_countable]) >>
  qsuff_tac `preds (sup fU) ≼ 𝕌(:'a ucinf)`
  >- metis_tac [cardleq_ANTISYM, cardleq_TRANS] >>
  simp[preds_sup, dclose_BIGUNION] >>
  match_mp_tac CARD_BIGUNION >>
  asm_simp_tac (srw_ss() ++ DNF_ss) []
*)
val _ = export_theory()
