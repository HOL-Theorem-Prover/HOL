open HolKernel Parse boolLib bossLib

open ordinalTheory cardinalTheory ordinalNotationTheory

open lcsymtacs

val _ = new_theory "ordNotationSemantics"

val _ = export_rewrites ["ordinalNotation.finp_def", "ordinalNotation.tail_def",
                         "ordinalNotation.is_ord_equations",
                         "ordinalNotation.osyntax_size_def",
                         "ordinalNotation.oless_equations",
                         "ordinalNotation.expt_def"]

val ordModel_def = Define`
  (ordModel (End n) = &n) ∧
  (ordModel (Plus e c t) = &c * ω ** ordModel e + ordModel t)
`
val _ = export_rewrites ["ordModel_def"]

val _ = add_rule {fixity = Closefix, term_name = "ordModel",
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,2)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟦", TM, TOK "⟧"]}

val osyntax_EQ_0 = store_thm(
  "osyntax_EQ_0",
  ``∀a. is_ord a ⇒ ((⟦a⟧ = 0) ⇔ (a = End 0))``,
  Induct_on `is_ord` THEN SRW_TAC [][ordModel_def] THEN
  `k ≠ 0` by DECIDE_TAC THEN SRW_TAC [][ordEXP_EQ_0]);

val CNF_nat = store_thm(
  "CNF_nat",
  ``CNF &n = if n = 0 then [] else [(&n,0)]``,
  rw[] >> match_mp_tac polyform_UNIQUE >> rw[is_polyform_def] >> decide_tac);

(* val ordModel_11 = store_thm(
  "ordModel_11",
  ``is_ord m ∧ is_ord n ⇒ ((⟦m⟧ = ⟦n⟧) ⇔ (m = n))``,
  qsuff_tac `∀m. is_ord m ⇒ ∀n. is_ord n ∧ (⟦m⟧ = ⟦n⟧) ⇒ (m = n)`
  >- metis_tac[] >> Induct_on `is_ord` >> simp[] >> conj_tac
  >- (map_every qx_gen_tac [`k`, `n`] >>
      `(∃k2. n = End k2) ∨ ∃c e t. n = Plus e c t`
        by (Cases_on `n` >> simp[])
      >- simp[] >>
      strip_tac >> rw[] >> fs[] >>
      `&k < ω` by simp[] >>
      `ω ≤ ω ** ⟦e⟧`
        by (simp_tac bool_ss [SimpR ``ordlt``, Once (GSYM ordEXP_1R)] >>
            match_mp_tac ordEXP_le_MONO_R >> simp[] >> strip_tac >>
            `⟦e⟧ = 0` by metis_tac [IFF_ZERO_lt] >> metis_tac [osyntax_EQ_0]) >>
      `ω ** ⟦e⟧ ≤ &c * ω ** ⟦e⟧` by simp[] >>
      `&c * ω ** ⟦e⟧ ≤ &c * ω ** ⟦e⟧ + ⟦t⟧` by simp[] >>
      metis_tac [ordlte_TRANS, ordle_TRANS, ordlt_REFL]) >>
  map_every qx_gen_tac [`e`, `c`, `t`] >> strip_tac
*)

val oless_0 = store_thm(
  "oless_0",
  ``∀n. oless n (End 0) = F``,
  Cases_on `n` >> simp[]);
val _ = export_rewrites ["oless_0"]

val oless_0a = store_thm(
  "oless_0a",
  ``oless (End 0) n ⇔ n ≠ End 0``,
  Cases_on `n` >> simp[]);
val _ = export_rewrites ["oless_0a"]

val oless_x_End = store_thm(
  "oless_x_End",
  ``oless x (End n) ⇔ ∃m. (x = End m) ∧ m < n``,
  Cases_on `x` >> simp[]);

val is_ord_expt = store_thm(
  "is_ord_expt",
  ``is_ord e ⇒ is_ord (expt e)``,
  Cases_on `e` >> simp[]);

val polyform_eval_poly = store_thm(
  "polyform_eval_poly",
  ``1 < α ∧ is_polyform α β ⇒ (polyform α (eval_poly α β) = β)``,
  strip_tac >> match_mp_tac polyform_UNIQUE >> simp[]);

(*
val notation_exists = store_thm(
  "notation_exists",
  ``∀α. α < ε₀ ⇒
        ∃n. is_ord n ∧ (⟦n⟧ = α) ∧
            (α ≠ 0 ⇒ (⟦expt n⟧ = SND (HD (CNF α)))) ∧
            ∀b. is_ord b ⇒ (oless b n ⇔ ⟦b⟧ < α)``,
  ho_match_mp_tac ord_induction >> rpt strip_tac >>
  `(CNF α = []) ∨ ∃c e t. (CNF α = (c,e)::t)`
    by metis_tac [listTheory.list_CASES, pairTheory.pair_CASES]
  >- (fs[polyform_EQ_NIL] >> qexists_tac `End 0` >> simp[]) >>
  `(eval_poly ω ((c,e)::t) = α) ∧ is_polyform ω ((c,e)::t)`
    by metis_tac [polyform_def, fromNat_lt_omega] >>
  fs[] >>
  `c < ω ∧ 0 < c ∧ is_polyform ω t`
    by (imp_res_tac is_polyform_CONS_E >> simp[]) >>
  `eval_poly ω t < α`
    by (rw[] >> match_mp_tac ordlte_TRANS >>
        qexists_tac `ω ** e` >> conj_tac
        >- (match_mp_tac (GEN_ALL is_polyform_head_dominates_tail) >>
            metis_tac[fromNat_lt_omega]) >>
        match_mp_tac ordle_TRANS >> qexists_tac `c * ω ** e` >> simp[] >>
        qsuff_tac `c ≠ 0` >- simp[] >> strip_tac >> fs[]) >>
  `∃tn. is_ord tn ∧ (⟦tn⟧ = eval_poly ω t) ∧
        (eval_poly ω t ≠ 0 ⇒ (⟦expt tn⟧ = SND (HD (CNF (eval_poly ω t))))) ∧
        ∀b. is_ord b ⇒ (oless b tn ⇔ ⟦b⟧ < eval_poly ω t)`
    by (first_x_assum (qspec_then `eval_poly ω t` mp_tac) >> simp[] >>
        disch_then match_mp_tac >> metis_tac [ordlt_TRANS]) >>
  `∃cn. c = &cn` by metis_tac[lt_omega] >>
  `e < α`
    by (spose_not_then strip_assume_tac >>
        `c * ω ** e ≤ α` by rw[] >>
        `ω ** e ≤ c * ω ** e` by (simp[] >> qsuff_tac `cn ≠ 0` >- simp[] >>
                                  strip_tac >> fs[]) >>
        `ω ** e ≤ e` by metis_tac [ordle_TRANS] >>
        `ε₀ ≤ e` by metis_tac [epsilon0_least_fixpoint] >>
        `α < e` by metis_tac [ordlte_TRANS] >>
        `e ≤ ω ** e` by simp[x_le_ordEXP_x] >>
        metis_tac [ordlt_REFL, ordlte_TRANS, ordle_TRANS]) >>
    Cases_on `e = 0`
    >- (qexists_tac `End cn` >> simp[] >> fs[] >>
        `&cn = α`
          by (qsuff_tac `t = []` >- (strip_tac >> fs[]) >>
              spose_not_then strip_assume_tac >>
              `∃c' e' t'. t = (c',e')::t'`
                by metis_tac [listTheory.list_CASES, pairTheory.pair_CASES] >>
              fs[is_polyform_def]) >>
        simp[] >> rw[] >> simp[oless_x_End] >> eq_tac >- (rw[] >> rw[]) >>
        pop_assum mp_tac >>
        `(∃m. b = End m) ∨ ∃e c t. b = Plus e c t` by (Cases_on `b` >> simp[])
        >- simp[] >>
        simp[] >> strip_tac >>
        match_mp_tac ordle_TRANS >> qexists_tac `ω` >> simp[] >>
        conj_tac >- simp[ordle_lteq] >>
        match_mp_tac ordle_TRANS >> qexists_tac `&c * ω ** ⟦e⟧` >> simp[] >>
        match_mp_tac ordle_TRANS >> qexists_tac `ω ** ⟦e⟧` >> simp[] >>
        match_mp_tac ordle_TRANS >> qexists_tac `ω ** 1` >> simp[] >>
        strip_tac >> metis_tac [osyntax_EQ_0, IFF_ZERO_lt]) >>
    `∃en. is_ord en ∧ (⟦en⟧ = e) ∧
          ∀b. is_ord b ⇒ (oless b en ⇔ ⟦b⟧ < e)` by metis_tac[ordlt_TRANS] >>
    `en ≠ End 0` by (strip_tac >> fs[]) >>
    qexists_tac `Plus en cn tn` >> simp[] >>
    rpt strip_tac
    >- (rw[] >> fs[])
    >- (`(t = []) ∨ ∃c2 e2 t2. t = (c2,e2)::t2`
          by metis_tac [listTheory.list_CASES, pairTheory.pair_CASES]
        >- (fs[] >>
            `tn = End 0` by metis_tac [osyntax_EQ_0] >> fs[] >>
            metis_tac [IFF_ZERO_lt]) >>
        `CNF (eval_poly ω t) = t` by simp[polyform_eval_poly] >>
        pop_assum SUBST_ALL_TAC >>
        `eval_poly ω t ≠ 0`
          by (fs[is_polyform_def, ordEXP_EQ_0] >>
              imp_res_tac is_polyform_CONS_E >> metis_tac [IFF_ZERO_lt]) >>
        simp[is_ord_expt] >> fs[is_polyform_def])
    >- rw[] >>
    `(∃m. b = End m) ∨ (∃e0 c0 t0. b = Plus e0 c0 t0)`
      by (Cases_on `b` >> simp[])
    >- (simp[] >> rw[] >>
        match_mp_tac ordlte_TRANS >> qexists_tac `ω` >> simp[] >>
        match_mp_tac ordle_TRANS >> qexists_tac `&cn * ω ** ⟦en⟧` >> simp[]>>
        match_mp_tac ordle_TRANS >> qexists_tac `ω ** ⟦en⟧` >>
        simp[ordEXP_EQ_0]>> conj_tac
        >- (match_mp_tac ordle_TRANS >> qexists_tac `ω ** 1` >> simp[] >>
            metis_tac [IFF_ZERO_lt]) >>
        fs[] >> decide_tac) >>
    simp[] >> fs[] >>
    Cases_on `e0 = en`
    >- (simp[] >> Cases_on `c0 = cn` >> simp[] >> rw[] >>






        Cases_on `en` >> fs[]
        >- (`0 < n` by decide_tac >> simp[oless_rules]) >>
        simp[oless_rules]) >>


*)


val ordModel_lt_epsilon0 = store_thm(
  "ordModel_lt_epsilon0",
  ``∀a. ⟦a⟧ < ε₀``,
  Induct_on `a` THEN
  SRW_TAC [][ordMUL_under_epsilon0, ordEXP_under_epsilon0,
             ordADD_under_epsilon0, ordModel_def]);

val ordpolyform_def = Define`
  (ordpolyform (End n) = [(&n:'a ordinal,&0:'a ordinal)]) ∧
  (ordpolyform (Plus e c t) = (&c,⟦e⟧)::ordpolyform t)
`;
val _ = export_rewrites ["ordpolyform_def"]

val ordpolyform_correct = store_thm(
  "ordpolyform_correct",
  ``eval_poly ω (ordpolyform e) = ⟦e⟧``,
  Induct_on `e` >> rw[ordModel_def]);

val asimp = asm_simp_tac (srw_ss() ++ ARITH_ss)
val bsimp = asm_simp_tac bool_ss
val dsimp = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss)

val ord_less_models_ordlt = store_thm(
  "ord_less_models_ordlt",
  ``∀x. is_ord x ⇒
        (∀y. oless x y ∧ is_ord y ⇒ ⟦x⟧ :α ordinal < ⟦y⟧) ∧
        (¬finp x ⇒ ⟦tail x⟧ < ω ** ⟦expt x⟧ :α ordinal)``,
  completeInduct_on `osyntax_size x` THEN
  RULE_ASSUM_TAC
    (SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [AND_IMP_INTRO]) >> fs[] >>
  gen_tac >>
  `(∃m. x = End m) ∨ (∃e c t. x = Plus e c t)` by (Cases_on `x` >> simp[])
  >- (simp[] >> strip_tac >> qx_gen_tac `y` >>
      `(∃n. y = End n) ∨ (∃e c t. y = Plus e c t)` by (Cases_on `y` >> simp[])>>
      simp[] >> strip_tac >>
      match_mp_tac ordlte_TRANS >> qexists_tac `ω` >> rw[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `&c * ω ** ⟦e⟧` >> rw[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `ω ** ⟦e⟧` >>
      asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
      SIMP_TAC bool_ss [Once (GSYM ordEXP_1R), SimpR ``ordlt``] THEN
      MATCH_MP_TAC ordEXP_le_MONO_R THEN simp[] >>
      metis_tac [IFF_ZERO_lt, osyntax_EQ_0]) >>
  simp[] >> disch_then SUBST_ALL_TAC >> strip_tac >>
  REVERSE conj_tac
  >- (`ω ** ⟦e⟧ = ⟦Plus e 1 (End 0)⟧` by simp[] >> pop_assum SUBST1_TAC >>
      first_assum match_mp_tac >> simp[] >> Cases_on `t` >> fs[]) >>
  qx_gen_tac `y` >>
  `(∃n. y = End n) ∨ (∃e2 c2 t2. y = Plus e2 c2 t2)`
    by (Cases_on `y` >> simp[]) >> simp[] >> strip_tac
  >- (`⟦t⟧ < ⟦Plus e 1 (End 0)⟧`
        by (first_assum match_mp_tac >> asimp[] >> Cases_on `t` >> fs[]) >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      match_mp_tac ordlt_TRANS >> qexists_tac `&(SUC c) * ω ** ⟦e⟧` >>
      conj_tac
      >- (match_mp_tac ordlte_TRANS >>
          qexists_tac `&c * ω ** ⟦e⟧ + ω ** ⟦e⟧` >> simp[]) >>
      match_mp_tac ordlte_TRANS >> qexists_tac `ω ** ⟦e2⟧` >> REVERSE conj_tac
      >- (match_mp_tac ordle_TRANS >> qexists_tac `&c2 * ω ** ⟦e2⟧` >>
          simp[]) >>
      `&SUC c * ω ** ⟦e⟧ = eval_poly ω [(&SUC c, ⟦e⟧)]` by simp[] >>
      pop_assum SUBST1_TAC >>
      match_mp_tac (GEN_ALL is_polyform_head_dominates_tail) >>
      simp[is_polyform_def] >> qexists_tac `1` >> simp[])
  >- (simp[] >>
      `⟦t⟧ < ⟦Plus e 1 (End 0)⟧`
        by (first_assum match_mp_tac >> asimp[] >> Cases_on `t` >> fs[]) >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      match_mp_tac ordlte_TRANS >> qexists_tac `&(SUC c) * ω ** ⟦e2⟧` >>
      conj_tac >- simp[] >>
      match_mp_tac ordle_TRANS >> qexists_tac `&c2 * ω ** ⟦e2⟧` >> simp[]) >>
  simp[]);

val oless_total = store_thm(
  "oless_total",
  ``∀m n. oless m n ∨ oless n m ∨ (m = n)``,
  Induct
  >- (map_every qx_gen_tac [`i`, `n`] >>
      `(∃j. n = End j) ∨ (∃e2 c2 t2. n = Plus e2 c2 t2)`
        by (Cases_on `n` >> simp[]) >> simp[]) >>
  map_every qx_gen_tac [`i`, `n`] >>
  qmatch_abbrev_tac `oless (Plus e1 i t1) n ∨ FOO` >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  `(∃j. n = End j) ∨ (∃e2 j t2. n = Plus e2 j t2)`
    by (Cases_on `n` >> simp[]) >> simp[] >>
  `oless e1 e2 ∨ oless e2 e1 ∨ (e2 = e1)` by metis_tac[] >> rw[] >>
  `oless t1 t2 ∨ oless t2 t1 ∨ (t2 = t1)` by metis_tac[] >> rw[] >>
  metis_tac [DECIDE ``x:num < y ∨ y < x ∨ (x = y)``]);

val ord_less_modelled = store_thm(
  "ord_less_modelled",
  ``ord_less x y ⇔ is_ord x ∧ is_ord y ∧ ⟦x⟧ < ⟦y⟧``,
  metis_tac [ord_less_def, ord_less_models_ordlt, ordlt_REFL, ordlt_TRANS,
             oless_total])

val oless_modelled = store_thm(
  "oless_modelled",
  ``is_ord x ∧ is_ord y ⇒ (oless x y ⇔ ⟦x⟧ < ⟦y⟧)``,
  metis_tac [ord_less_def, ord_less_modelled]);

val WF_ord_less = store_thm(
  "WF_ord_less",
  ``WF ord_less``,
  match_mp_tac relationTheory.WF_SUBSET >>
  qexists_tac `inv_image ordlt ordModel` >>
  simp[relationTheory.WF_inv_image, ordlt_WF] >>
  simp[ord_less_modelled, relationTheory.inv_image_def]);

(* |- ⟦expt t⟧ < ⟦e⟧ ∧ is_ord e ∧ is_ord t ⇒ ⟦t⟧ < ω ** ⟦e⟧ *)
val neqend0_lemma = prove(
  ``x < ⟦e⟧ ⇒ e ≠ End 0``,
  rpt strip_tac >> fs[]);

val tail_dominated = save_thm(
  "tail_dominated",
  ord_less_models_ordlt
    |> Q.SPEC `Plus e 1 t`
    |> SIMP_RULE (srw_ss() ++ boolSimps.CONJ_ss)
                 [oless_modelled, is_ord_expt]
    |> REWRITE_RULE [neqend0_lemma |> Q.INST [`x` |-> `⟦expt t⟧`] |> UNDISCH]
    |> REWRITE_RULE [ASSUME ``⟦expt t⟧ < ⟦e⟧ :α ordinal``]
    |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]);

val sup_eq_sup = store_thm(
  "sup_eq_sup",
  ``(s1:α ordinal set) ≼ univ(:α inf) ∧
    (s2:α ordinal set) ≼ univ(:α inf) ∧
    (∀a. a ∈ s1 ⇒ ∃b. b ∈ s2 ∧ a ≤ b) ∧
    (∀b. b ∈ s2 ⇒ ∃a. a ∈ s1 ∧ b ≤ a) ⇒ (sup s1 = sup s2)``,
  strip_tac >> match_mp_tac ordle_ANTISYM >> simp[sup_thm] >>
  metis_tac [suple_thm, ordle_TRANS]);

val addL_disappears = store_thm(
  "addL_disappears",
  ``∀e a. a < ω ** e ⇒ (a + ω ** e = ω ** e)``,
  ho_match_mp_tac simple_ord_induction >> simp[] >> rpt conj_tac
  >- (qx_gen_tac `a` >> strip_tac >> `a = 0` by metis_tac [IFF_ZERO_lt] >>
      simp[])
  >- (simp[omega_islimit] >> qx_gen_tac `e` >> strip_tac >> qx_gen_tac `a` >>
      dsimp[sup_thm, IMAGE_cardleq_rwt, preds_inj_univ] >> qx_gen_tac `c` >>
      strip_tac >>
      `IMAGE (λy. y * ω ** e) (preds ω) ≠ ∅`
        by simp[pred_setTheory.EXTENSION] >>
      simp[ordADD_continuous, IMAGE_cardleq_rwt, preds_inj_univ] >>
      simp[GSYM pred_setTheory.IMAGE_COMPOSE, combinTheory.o_ABS_R] >>
      match_mp_tac sup_eq_sup >> dsimp[IMAGE_cardleq_rwt, preds_inj_univ] >>
      conj_tac
      >- (qx_gen_tac `d` >>
          disch_then (Q.X_CHOOSE_THEN `dn` STRIP_ASSUME_TAC o
                      SIMP_RULE (srw_ss()) [lt_omega]) >>
          `(dn = 0) ∨ ∃dn0. dn = SUC dn0` by (Cases_on `dn` >> simp[])
          >- (rw[] >> qexists_tac `c` >> simp[ordle_lteq]) >>
          `dn = 1 + dn0` by decide_tac >>
          Q.UNDISCH_THEN `dn = SUC dn0` (K ALL_TAC) >> rw[] >>
          SIMP_TAC bool_ss [GSYM ordADD_fromNat, ordMULT_RDISTRIB] >>
          simp[] >>
          `0 < c` by (spose_not_then strip_assume_tac >> fs[]) >>
          `0 < ω ** e` by (spose_not_then strip_assume_tac >> fs[]) >>
          qspecl_then [`a`, `ω ** e`] mp_tac ordDIVISION >>
          qabbrev_tac `q = a / ω ** e` >> qabbrev_tac `r = a % ω ** e` >>
          simp[] >> strip_tac >>
          `q * ω ** e + r + (ω ** e + &dn0 * ω ** e) =
           q * ω ** e + ω ** e + &dn0 * ω ** e`
            by metis_tac [ordADD_ASSOC] >>
          simp[] >>
          `q < c`
            by (spose_not_then strip_assume_tac >>
                `c * ω ** e ≤ q * ω ** e` by simp[] >>
                `q * ω ** e ≤ q * ω ** e + r` by simp[] >>
                metis_tac [ordlte_TRANS, ordle_TRANS, ordlt_REFL]) >>
          `q < ω` by metis_tac [ordlt_TRANS] >>
          qexists_tac `q + 1 + &dn0` >>
          simp[ordMULT_RDISTRIB] >> fs[lt_omega]) >>
      qx_gen_tac `d` >> strip_tac >> qexists_tac `d` >> simp[]) >>
  qx_gen_tac `e` >> strip_tac >>
  `IMAGE ($** ω) (preds e) ≠ ∅`
    by (simp[pred_setTheory.EXTENSION] >> strip_tac >> fs[]) >>
  dsimp[sup_thm, ordADD_continuous, IMAGE_cardleq_rwt, preds_inj_univ,
        GSYM pred_setTheory.IMAGE_COMPOSE] >>
  map_every qx_gen_tac [`a`, `x`] >> strip_tac >>
  match_mp_tac sup_eq_sup >> dsimp[IMAGE_cardleq_rwt, preds_inj_univ] >>
  conj_tac
  >- (qx_gen_tac `y` >> strip_tac >>
      `(x = y) ∨ x < y ∨ y < x` by metis_tac [ordlt_trichotomy]
      >- metis_tac[ordlt_REFL]
      >- (`ω ** x < ω ** y` by simp[] >>
          `a < ω ** y` by metis_tac [ordlt_TRANS] >>
          metis_tac [ordlt_REFL]) >>
      metis_tac [ordlt_CANCEL, ordEXP_lt_IFF, lt_omega, ordle_lteq]) >>
  qx_gen_tac `y` >> strip_tac >>
  `(x = y) ∨ x < y ∨ y < x` by metis_tac [ordlt_trichotomy]
  >- metis_tac [ordlt_REFL]
  >- (`ω ** x < ω ** y` by simp[] >>
      `a < ω ** y` by metis_tac [ordlt_TRANS] >>
      metis_tac [ordlt_REFL]) >>
  metis_tac [ordlt_CANCEL, ordEXP_lt_IFF, lt_omega, ordle_lteq]);

val add_nat1_disappears = store_thm(
  "add_nat1_disappears",
  ``ω ≤ α ⇒ (&n + α = α)``,
  rpt strip_tac >> fs [ordle_EXISTS_ADD] >>
  qspecl_then  [`1`, `&n`] mp_tac addL_disappears >> simp[ordADD_ASSOC]);

val add_nat1_disappears_kexp = store_thm(
  "add_nat1_disappears_kexp",
  ``e ≠ 0 ∧ 0 < k ⇒ (&n + &k * ω ** e = &k * ω ** e)``,
  strip_tac >> match_mp_tac add_nat1_disappears >> match_mp_tac ordle_TRANS >>
  qexists_tac `ω ** e` >> simp[] >>
  match_mp_tac ordle_TRANS >> qexists_tac `ω ** 1` >> simp[] >>
  metis_tac [IFF_ZERO_lt]);

val add_disappears_kexp = store_thm(
  "add_disappears_kexp",
  ``e ≠ 0 ∧ 0 < k ∧ a < ω ** e ⇒ (a + &k * ω ** e = &k * ω ** e)``,
  strip_tac >>
  `(k = 0) ∨ ∃k0. k = SUC k0` by (Cases_on `k` >> simp[]) >- fs[] >>
  `k = 1 + k0` by decide_tac >> pop_assum SUBST1_TAC >>
  bsimp[GSYM ordADD_fromNat, ordMULT_RDISTRIB] >>
  simp[ordADD_ASSOC, addL_disappears]);


(* |- e1 < e2 ⇒ &k * ω ** e1 < ω ** e2 *)
val kexp_lt = let
  val zero_ltk_or_eqzero = DECIDE ``0n < k ∨ (k = 0)``
  val zero_ltk =
    is_polyform_head_dominates_tail
      |> Q.INST [`a` |-> `ω`, `t` |-> `[(&k,e1)]`, `c` |-> `1`, `e` |-> `e2`]
      |> SIMP_RULE (srw_ss()) [is_polyform_def, ASSUME ``e1:'a ordinal < e2``]
      |> UNDISCH_ALL
  val eqzero = prove(``&k * ω ** e1 < ω ** e2``,
                     simp[ASSUME ``k = 0n``] >> spose_not_then assume_tac >>
                     fs[ordEXP_EQ_0])
in
  save_thm("kexp_lt",
           DISJ_CASES zero_ltk_or_eqzero zero_ltk eqzero |> DISCH_ALL)
end

val ord_add_correct = store_thm(
  "ord_add_correct",
  ``∀x y. is_ord x ∧ is_ord y ⇒ (⟦ord_add x y⟧ = ⟦x⟧ + ⟦y⟧)``,
  ho_match_mp_tac ord_add_ind >>
  simp_tac (srw_ss() ++ boolSimps.CONJ_ss)
    [ord_add_def, oless_modelled, AND_IMP_INTRO, is_ord_expt, ordADD_ASSOC] >>
  rw[add_nat1_disappears_kexp, osyntax_EQ_0]
  >- (AP_THM_TAC >> AP_TERM_TAC >> simp[Once EQ_SYM_EQ] >>
      match_mp_tac (add_disappears_kexp |> GEN_ALL) >>
      simp[osyntax_EQ_0] >> match_mp_tac ordlt_TRANS >>
      qexists_tac `&(SUC k1) * ω ** ⟦e1⟧` >> simp[kexp_lt, tail_dominated])
  >- (AP_THM_TAC >> AP_TERM_TAC >> simp[GSYM ordADD_ASSOC] >>
      simp[add_disappears_kexp, tail_dominated, osyntax_EQ_0] >>
      bsimp[GSYM ordADD_fromNat, ordMULT_RDISTRIB]) >>
  simp[ordADD_ASSOC]);

val _ = export_theory()
