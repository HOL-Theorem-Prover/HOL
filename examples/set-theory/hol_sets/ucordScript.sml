(* theory stub about uncountable ordinals *)
open HolKernel Parse boolLib bossLib

open lcsymtacs
open pred_setTheory
open ordinalTheory cardinalTheory

open boolSimps

val _ = new_theory "ucord"

val _ = type_abbrev("ucinf", ``:('a + (num -> bool)) inf``)
val _ = type_abbrev("ucord", ``:('a + (num -> bool)) ordinal``)

val dsimp = asm_simp_tac(srw_ss() ++ DNF_ss)

val ucinf_uncountable = store_thm(
  "ucinf_uncountable",
  ``¬countable 𝕌(:'a ucinf)``,
  simp[SUM_UNIV, UNIV_FUN_TO_BOOL, infinite_pow_uncountable]);

val Unum_cardlt_ucinf = store_thm(
  "Unum_cardlt_ucinf",
  ``𝕌(:num) ≺ 𝕌(:'a ucinf)``,
  simp[cardlt_lenoteq] >> conj_tac
  >- (simp[cardleq_def] >> qexists_tac `INL` >> simp[INJ_INL]) >>
  strip_tac >> imp_res_tac countable_cardeq >>
  fs[ucinf_uncountable, num_countable])

val Unum_cardle_ucinf = store_thm(
  "Unum_cardle_ucinf",
  ``𝕌(:num) ≼ 𝕌(:'a ucinf)``,
  simp[cardleq_lteq, Unum_cardlt_ucinf]);

val ucord_sup_exists_lemma = store_thm(
  "ucord_sup_exists_lemma",
  ``{ a:'a ucord | countableOrd a } ≼ univ(:'a ucinf)``,
  spose_not_then assume_tac >> fs[cardlt_lenoteq] >>
  `∃f. INJ f 𝕌(:'a ucinf) {a:'a ucord | countableOrd a}`
     by metis_tac[cardleq_def] >>
  `(∀u. countableOrd (f u)) ∧ (∀u v. f u = f v ⇒ u = v)`
      by fs[INJ_DEF] >>
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
  dsimp[IMAGE_cardleq_rwt] >>
  dsimp[Abbr`fU`] >>
  metis_tac[countable_thm, cardleq_TRANS, Unum_cardle_ucinf])

val omega1_def = Define`
  omega1 : 'a ucord = sup { a | countableOrd a }
`;
val _ = overload_on ("ω₁", ``omega1``)

val x_lt_omega1_countable = store_thm(
  "x_lt_omega1_countable",
  ``x < ω₁ ⇔ countableOrd x``,
  simp[omega1_def, sup_thm, ucord_sup_exists_lemma, EQ_IMP_THM] >>
  rpt strip_tac >- metis_tac[countableOrds_dclosed] >>
  qexists_tac `x⁺` >> simp[preds_ordSUC]);

(* |- ¬countableOrd ω₁ *)
val omega1_not_countable = save_thm(
  "omega1_not_countable",
  x_lt_omega1_countable |> Q.INST[`x` |-> `ω₁`] |> SIMP_RULE (srw_ss()) []);

val _ = export_theory()
