open HolKernel boolLib Parse bossLib

open vbgsetTheory vbgnatsTheory
open boolSimps

val _ = new_theory "ordinal"

val poc_def = Define`
  poc A R ⇔
    (∀x. x ∈ A ⇒ R x x) ∧
    (∀x y z. x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ R x y ∧ R y z ⇒ R x z) ∧
    (∀x y. x ∈ A ∧ y ∈ A ∧ R x y ∧ R y x ⇒ (x = y))
`;

val chain_def = Define`
  chain A R C ⇔ C ⊆ A ∧ ∀x y. x ∈ C ∧ y ∈ C ⇒ R x y ∨ R y x
`

val totalR_def = Define`
  totalR A R ⇔ poc A R ∧ ∀x y. x ∈ A ∧ y ∈ A ⇒ R x y ∨ R y x
`;

val iseg_def = Define`
  iseg A R x = SPEC0 (λy. y ∈ A ∧ R y x ∧ x ≠ y ∧ x ∈ A)
`;

val iseg_SUBSET = store_thm(
  "iseg_SUBSET",
  ``∀x y. x ∈ A ∧ y ∈ A ∧ poc A R ∧ R x y ⇒ iseg A R x ⊆ iseg A R y``,
  rpt strip_tac >>
  `∀x y z. x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ R x y ∧ R y z ⇒ R x z` by fs[poc_def] >>
  rw[iseg_def, SUBSET_def, SPEC0] >- metis_tac [] >>
  `R u y` by metis_tac [] >>
  strip_tac >> srw_tac [][] >>
  `∀x y. x ∈ A ∧ y ∈ A ∧ R x y ∧ R y x ⇒ (x = y)` by fs[poc_def] >>
  metis_tac[]);

val woclass_def = Define`
  woclass A R ⇔
     totalR A R ∧
     ∀B. B ⊆ A ∧ B ≠ {} ⇒ ∃e. e ∈ B ∧ ∀d. d ∈ B ⇒ R e d
`;

val Nats_SETs = prove(``n ∈ Nats ⇒ SET n``, metis_tac [SET_def])
val _ = augment_srw_ss [rewrites [Nats_SETs]]

val Nats_wo = store_thm(
  "Nats_wo",
  ``woclass Nats (λx y. x ≤ y)``,
  rw[woclass_def, totalR_def, poc_def, LE_ANTISYM]
    >- metis_tac [LE_TRANS]
    >- metis_tac [LE_TOTAL] >>
  `∃e. e ∈ B` by (fs[EXTENSION] >> metis_tac[]) >>
  metis_tac [Nats_least_element]);

val ordinal_def = Define`
  ordinal α ⇔ SET α ∧ transitive α ∧
              (∀x y. x ∈ α ∧ y ∈ α ⇒ x ∈ y ∨ y ∈ x ∨ (x = y))
`;

val Ord_def = Define`Ord = SPEC0 (λs. ordinal s)`

val _ = clear_overloads_on "<="

val ordle_def = Define`
  ordle x y ⇔ x ∈ y ∨ (x = y)
`;

val _ = overload_on ("<=", ``ordle``)

val ordle_REFL = store_thm(
  "ordle_REFL",
  ``x:vbgc ≤ x``,
  rw[ordle_def])
val _ = export_rewrites ["ordle_REFL"]

val woclass_thm = store_thm(
  "woclass_thm",
  ``woclass A R ⇔ (∀x y. x ∈ A ∧ y ∈ A ∧ R x y ∧ R y x ⇒ (x = y)) ∧
                  ∀B. B ⊆ A ∧ B ≠ {} ⇒ ∃e. e ∈ B ∧ ∀d. d ∈ B ⇒ R e d``,
  rw[woclass_def, EQ_IMP_THM]
    >- fs[totalR_def, poc_def] >>
  rw[totalR_def, poc_def]
    >- ((* reflexivity *)
        first_x_assum (qspec_then `{x}` mp_tac) >>
        `{x} ≠ {}`
           by (rw[Once EXTENSION] >> metis_tac [SET_def]) >>
        srw_tac [CONJ_ss][SUBSET_def])
    >- ((* transitivity *)
        first_x_assum (qspec_then `{x;y;z}` mp_tac) >>
        `SET x ∧ SET y ∧ SET z` by metis_tac [SET_def] >>
        `{x;y;z} ≠ {}`
           by rw[Once EXTENSION, EXISTS_OR_THM] >>
        srw_tac[CONJ_ss, DNF_ss][SUBSET_def] >> metis_tac [])
    >- ((* totality *)
        first_x_assum (qspec_then `{x;y}` mp_tac) >>
        `SET x ∧ SET y` by metis_tac [SET_def] >>
        `{x;y} ≠ {}`
           by rw[Once EXTENSION, EXISTS_OR_THM] >>
        srw_tac[CONJ_ss, DNF_ss][SUBSET_def]))

val EMPTY_ordinal = store_thm(
  "EMPTY_ordinal",
  ``ordinal {}``,
  rw[ordinal_def, transitive_def])
val _ = export_rewrites ["EMPTY_ordinal"]

val ORDINALS_CONTAIN_ORDINALS = store_thm(
  "ORDINALS_CONTAIN_ORDINALS",
  ``∀α β. ordinal α ∧ β ∈ α ⇒ ordinal β``,
  rw[ordinal_def]
    >- metis_tac [SET_def]
    >- (fs[transitive_def] >>
        `∀e. e ∈ β ⇒ e ∈ α` by metis_tac [SUBSET_def] >>
        qx_gen_tac `x` >> rw[] >>
        simp[SUBSET_def] >> SPOSE_NOT_THEN MP_TAC >>
        DISCH_THEN (Q.X_CHOOSE_THEN `u` STRIP_ASSUME_TAC) >>
        `x ∈ α` by metis_tac [] >>
        `u ∈ α` by metis_tac [SUBSET_def] >>
        `u ∈ β ∨ β ∈ u ∨ (β = u)` by metis_tac [] >>
        metis_tac [IN3_ANTISYM, IN_ANTISYM])
   >- metis_tac [transitive_def, SUBSET_def])

val ORD_INDUCTION = store_thm(
  "ORD_INDUCTION",
  ``(∀a. ordinal a ∧ (∀x. x ∈ a ⇒ P x) ⇒ P a) ⇒ ∀a. ordinal a ⇒ P a``,
  strip_tac >>
  qsuff_tac `∀a. SET a ⇒ ordinal a ⇒ P a`
    >- metis_tac [SET_def, ordinal_def] >>
  Induct_on `SET a` >> rw[] >> metis_tac [ORDINALS_CONTAIN_ORDINALS]);
val _ = IndDefLib.export_rule_induction "ORD_INDUCTION"

val EMPTY_LE_ORDS = store_thm(
  "EMPTY_LE_ORDS",
  ``∀α. ordinal α ⇒ {} ≤ α``,
  Induct_on `ordinal α` >> rw[] >>
  Cases_on `α = {}` >> rw[] >>
  `∃β. β ∈ α` by metis_tac [EMPTY_UNIQUE] >>
  `{} ≤ β` by metis_tac [] >>
  fs[ordle_def] >> metis_tac [transitive_ALT, ordinal_def]);

val ords_segs = store_thm(
  "ords_segs",
  ``∀α. ordinal α ⇒ (iseg Ord ordle α = α)``,
  rw[Ord_def, ordinal_def, iseg_def] >> rw[Once EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    fs[ordle_def],
    metis_tac [SET_def],
    metis_tac [SET_def],
    metis_tac [SET_def],
    fs[transitive_ALT] >> metis_tac [IN_REFL, IN_ANTISYM, IN3_ANTISYM],
    metis_tac [transitive_ALT],
    rw[ordle_def],
    metis_tac [IN_REFL]
  ])

val ords_segs2 = store_thm(
  "ords_segs2",
  ``ordinal α ∧ e ∈ α ⇒ (iseg α ordle e = e)``,
  rw[ordinal_def, iseg_def] >> rw[Once EXTENSION] >>
  EQ_TAC >- srw_tac[CONJ_ss][ordle_def] >>
  metis_tac [SET_def, ordle_def, IN_REFL, transitive_ALT]);


val orderiso_def = Define`
  orderiso A B R ⇔ ∃f. (∀x. x ∈ A ⇒ f x ∈ B) ∧
                       (∀x1 x2. x1 ∈ A ∧ x2 ∈ A ⇒
                                ((f x1 = f x2)  ⇔ (x1 = x2))) ∧
                       (∀y. y ∈ B ⇒ ∃x. x ∈ A ∧ (f x = y)) ∧
                       (∀x1 x2. x1 ∈ A ∧ x2 ∈ A ∧ R x1 x2 ⇒ R (f x1) (f x2))
`;

val ordle_wo = store_thm(
  "ordle_wo",
  ``ordinal α ⇒ woclass α ordle``,
  rw[woclass_thm, Ord_def]
    >- ((* antisymmetry *)
        fs[ordinal_def, transitive_def] >>
        Cases_on `x = y` >- rw[] >>
        `x ∈ y ∧ y ∈ x` by metis_tac [ordle_def] >>
        metis_tac [IN_ANTISYM])
    >- ((* existence of least members *)
        `∃x. x ∈ B ∧ (x ∩ B = {})` by metis_tac [FOUNDATION3] >>
        qexists_tac `x` >> rw[] >>
        `d ∉ x` by (fs [Once EXTENSION] >> metis_tac [SET_def]) >>
        metis_tac [ordinal_def, ordle_def, SUBSET_def]));

val wlog_seteq = store_thm(
  "wlog_seteq",
  ``(∀a b. Q a b ⇒ Q b a) ∧ (∀a b. Q a b ⇒ a ⊆ b) ⇒
    (∀a b. Q a b ⇒ (a = b))``,
  rpt strip_tac >>
  qsuff_tac `a ⊆ b ∧ b ⊆ a` >- metis_tac[SUBSET_def, EXTENSION] >>
  metis_tac []);

val orderiso_ordinals = store_thm(
  "orderiso_ordinals",
  ``∀α β. ordinal α ∧ ordinal β ∧ orderiso α β $<= ⇒ (α = β)``,
  ho_match_mp_tac wlog_seteq >> conj_tac
    >- (rw[orderiso_def]>>
        `∀a. a ∈ α ⇒ ∃!b. b ∈ β ∧ (a = f b)` by metis_tac [] >>
        qabbrev_tac `g = λa. @b. b ∈ β ∧ (a = f b)` >>
        qexists_tac `g` >> qunabbrev_tac `g` >> rw[] >| [
          SELECT_ELIM_TAC >> rw[] >> metis_tac [],
          SELECT_ELIM_TAC >> conj_tac >- metis_tac [] >> rw[] >>
          SELECT_ELIM_TAC >> metis_tac [],
          qexists_tac `f y` >> rw[] >> SELECT_ELIM_TAC >>
          srw_tac [CONJ_ss][],
          SELECT_ELIM_TAC >> conj_tac >- metis_tac [] >> rw[] >>
          SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
          qx_gen_tac `b` >> rw[] >>
          `x ∈ b ∨ (x = b) ∨ b ∈ x` by metis_tac [ordinal_def] >| [
             rw[ordle_def],
             rw[ordle_def],
             `b ≤ x` by rw[ordle_def] >>
             `f b ≤ f x` by metis_tac[] >>
             pop_assum mp_tac >> simp_tac (srw_ss()) [ordle_def] >>
             rw[] >> fs[ordle_def] >> metis_tac [IN_ANTISYM, IN_REFL]
          ]
        ]) >>
  rpt strip_tac >>
  spose_not_then assume_tac >>
  `∃x. x ∈ α ∧ x ∉ β` by metis_tac [SUBSET_def] >>
  fs[orderiso_def] >>
  `f x ≠ x` by metis_tac []>>
  qabbrev_tac `E = SPEC0 (λy. y ∈ α ∧ y ≠ f y)` >>
  `E ≠ {}` by (rw[Once EXTENSION, Abbr`E`] >> metis_tac[SET_def]) >>
  `E ⊆ α` by rw[SUBSET_def, Abbr`E`] >>
  `∃e. e ∈ E ∧ ∀d. d ∈ E ⇒ e ≤ d` by metis_tac [ordle_wo, woclass_def] >>
  `e ∈ α ∧ f e ∈ β` by metis_tac [SUBSET_def] >>
  `e ≠ f e` by fs[Abbr`E`] >>
  `∀d. d ∈ e ⇒ (f d = d)`
     by (qx_gen_tac `d` >> strip_tac >>
         `¬(e ≤ d)` by metis_tac [IN_REFL, IN_ANTISYM, ordle_def] >>
         `d ∈ α`
           by metis_tac [SUBSET_def, ordinal_def, transitive_def] >>
         `d ∉ E` by metis_tac [] >>
         pop_assum mp_tac >> qunabbrev_tac `E` >>
         simp[] >> metis_tac [SET_def]) >>
  `ordinal e ∧ ordinal (f e)`
     by metis_tac [ORDINALS_CONTAIN_ORDINALS, SUBSET_def] >>
  `iseg α $<= e = SPEC0 (λx. ∃y. y ∈ iseg α $<= e ∧ (x = f y))`
     by (rw[iseg_def] >> simp[Once EXTENSION] >>
         qx_gen_tac `e'` >> EQ_TAC >> rw[] >-
           (qexists_tac `e'` >> fs[ordle_def]) >>
         fs[ordle_def]) >>
  `_ = iseg β $<= (f e)`
     by (rw[iseg_def] >> simp[Once EXTENSION] >>
         qx_gen_tac `b` >> EQ_TAC >>
         asm_simp_tac (srw_ss() ++ DNF_ss) [] >>
         strip_tac >>
         `∃b0. b0 ∈ α ∧ (f b0 = b)` by metis_tac [] >>
         qexists_tac `b0` >> simp[] >> BasicProvers.VAR_EQ_TAC >>
         `SET b0` by metis_tac [SET_def] >>
         `e ∈ α` by metis_tac [SUBSET_def] >>
         `e ≠ b0` by metis_tac [] >> simp[ordle_def] >>
         `e ∈ b0 ∨ b0 ∈ e` by metis_tac [ordinal_def] >>
         `f e ≤ f b0` by metis_tac [ordle_def] >>
         metis_tac [ordle_def, IN_REFL, IN_ANTISYM]) >>
  `_ = f e` by metis_tac [ords_segs2] >>
  `iseg α ordle e = e` by metis_tac [ords_segs2] >>
  metis_tac [])




val _ = export_theory()



