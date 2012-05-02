open HolKernel Parse boolLib bossLib

open boolSimps pred_setTheory set_relationTheory
open lcsymtacs

val _ = new_theory "cardinal"

val cardeq_def = Define`
  cardeq s1 s2 <=> ?f. BIJ f s1 s2
`

val _ = set_fixity "=~" (Infix(NONASSOC, 450))
val _ = set_mapped_fixity {tok = "≈", term_name = "=~",
                           fixity = Infix(NONASSOC, 450)}

val _ = overload_on("=~", ``cardeq``)


val cardeq_REFL = store_thm(
  "cardeq_REFL",
  ``!s. s =~ s``,
  rw[cardeq_def] >> qexists_tac `\x. x` >> rw[BIJ_IFF_INV] >>
  qexists_tac `\x. x` >> simp[]);

val cardeq_SYMlemma = prove(
  ``!s t. s =~ t ==> t =~ s``,
  rw[cardeq_def] >> metis_tac [BIJ_LINV_BIJ]);


val cardeq_SYM = store_thm(
  "cardeq_SYM",
  ``!s:'a set t:'b set. s =~ t <=> t =~ s``,
  metis_tac [cardeq_SYMlemma]);

val cardeq_TRANS = store_thm(
  "cardeq_TRANS",
  ``!s t u. s =~ t ∧ t =~ u ⇒ s =~ u``,
  metis_tac [BIJ_COMPOSE, cardeq_def]);

(* less-or-equal *)
val cardleq_def = Define`
  cardleq s1 s2 <=> ∃f. INJ f s1 s2
`;

val _ = overload_on ("<<=", ``cardleq``)

val cardleq_REFL = store_thm(
  "cardleq_REFL",
  ``∀s:'a set. s ≼ s``,
  rw[cardleq_def] >> qexists_tac `\x. x` >> rw[INJ_ID]);

val cardleq_TRANS = store_thm(
  "cardleq_TRANS",
  ``∀s:'a set t:'b set u:'c set. s ≼ t ∧ t ≼ u ⇒ s ≼ u``,
  rw[cardleq_def] >> metis_tac [INJ_COMPOSE]);

val INJ_BIJ_SUBSET = store_thm(
  "INJ_BIJ_SUBSET",
  ``s0 ⊆ s ∧ INJ f s t ⇒ BIJ f s0 (IMAGE f s0)``,
  rw[SUBSET_DEF, INJ_DEF, IMAGE_SURJ, BIJ_DEF] >> metis_tac[]);

(* Schroder-Bernstein *)
val cardleq_ANTISYM = store_thm(
  "cardleq_ANTISYM",
  ``∀s t. s ≼ t ∧ t ≼ s ⇒ s ≈ t``,
  rpt gen_tac >> simp[cardleq_def, cardeq_def] >>
  disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `f` assume_tac)
                              (Q.X_CHOOSE_THEN `g` assume_tac)) >>
  qabbrev_tac `a0 = { x | x ∈ s ∧ ∀y. y ∈ t ⇒ g y ≠ x }` >>
  qabbrev_tac `A = PRIM_REC a0 (λs n. IMAGE (g o f) s)` >>
  qabbrev_tac `Aa = BIGUNION { A i | i | T }` >>
  `(A 0 = a0) ∧ ∀n. A (SUC n) = IMAGE (g o f) (A n)`
     by simp[Abbr`A`, prim_recTheory.PRIM_REC_THM] >>
  `∀n a. a ∈ A n ⇒ a ∈ s`
     by (Induct >> simp[Abbr`a0`] >> rw[] >> metis_tac [INJ_DEF]) >>
  qabbrev_tac `b0 = { y | y ∈ t ∧ ∀x. x ∈ s ⇒ f x ≠ y }` >>
  qabbrev_tac `B = PRIM_REC b0 (λs n. IMAGE (f o g) s)` >>
  qabbrev_tac `Bb = BIGUNION { B i | i | T }` >>
  qabbrev_tac `Ab = IMAGE g Bb` >>
  `(B 0 = b0) ∧ ∀n. B (SUC n) = IMAGE (f o g) (B n)`
     by simp[Abbr`B`, prim_recTheory.PRIM_REC_THM] >>
  Q.RM_ABBREV_TAC `A` >> Q.RM_ABBREV_TAC `B` >>
  `∀n y. y ∈ B n ⇒ y ∈ t`
     by (Induct >> simp[Abbr`b0`] >> metis_tac [INJ_DEF]) >>
  `∀y n. y ∈ t ∧ f (g y) ∈ B n ⇒ y ∈ B (n - 1)`
      by (Cases_on `n` >> simp[]
            >- (simp[Abbr`b0`] >> metis_tac [INJ_DEF]) >>
          metis_tac [INJ_DEF]) >>
  `∀x. x ∈ s ∧ g (f x) ∈ Ab ⇔ x ∈ Ab`
     by (asm_simp_tac (srw_ss() ++ DNF_ss)[Abbr`Ab`, Abbr`Bb`] >>
         qx_gen_tac `x` >> eq_tac >| [
           disch_then (Q.X_CHOOSE_THEN `y` (Q.X_CHOOSE_THEN `i` mp_tac)) >>
           Cases_on `i`
             >- (simp[Abbr`b0`] >> metis_tac [INJ_DEF]) >>
           simp[] >> metis_tac [INJ_DEF],
           strip_tac >> map_every qexists_tac [`f x`, `SUC i`] >>
           simp[] >> metis_tac [INJ_DEF]
         ]) >>
  `∀x n. x ∈ s ∧ f x IN B n ⇒ ∃y. y ∈ B (n - 1) ∧ (x = g y)`
     by (Cases_on `n` >> simp[Abbr`b0`] >> metis_tac [INJ_DEF]) >>
  `Aa ∩ Ab = ∅`
     by (qsuff_tac `∀i j. A i ∩ IMAGE g (B j) = ∅`
           >- (simp[Once EXTENSION, Abbr`Ab`, Abbr`Aa`, Abbr`Bb`] >>
               simp[Once EXTENSION] >> metis_tac[]) >>
         simp[Once EXTENSION,
              METIS_PROVE[]``(∀x. ¬P x ∨ Q x) ⇔ (∀x. P x ⇒ Q x)``] >>
         asm_simp_tac (srw_ss() ++ DNF_ss)[] >>
         qho_match_abbrev_tac `∀i j y. g y ∈ A i ⇒ y ∉ B j` >>
         Induct_on `i` >| [
           simp[Abbr`a0`] >> metis_tac[],
           asm_simp_tac (srw_ss() ++ DNF_ss)[] >>
           rpt strip_tac >> `y = f x` by metis_tac [INJ_DEF] >>
           pop_assum SUBST_ALL_TAC >>
           Cases_on `i`
             >- (Q.UNDISCH_THEN `x ∈ A 0` MP_TAC >> simp[Abbr`a0`] >>
                 metis_tac[]) >>
           Q.UNDISCH_THEN `x ∈ A (SUC n)` mp_tac >>
           simp[] >> qx_gen_tac `x0` >> Cases_on `x0 IN A n` >> simp[] >>
           strip_tac >>
           `f x0 ∈ B (j - 1)` by metis_tac [INJ_DEF] >>
           `g (f x0) ∉ A (SUC n)` by metis_tac[] >>
           pop_assum mp_tac >> simp[] >> metis_tac[]
         ]) >>
  `∀x. x ∈ Aa ⇒ x ∈ s` by (simp[Abbr`Aa`] >> metis_tac[]) >>
  `∀x. x ∈ Ab ⇒ x ∈ s` by (simp[Abbr`Ab`, Abbr`Bb`] >> metis_tac[INJ_DEF]) >>
  qabbrev_tac `Ainf = s DIFF Aa DIFF Ab` >>
  `BIJ g Bb Ab`
     by (simp[Abbr`Ab`] >> match_mp_tac (GEN_ALL INJ_BIJ_SUBSET) >>
         simp[SUBSET_DEF, Abbr`Bb`] >> metis_tac[]) >>
  `BIJ (LINV g Bb) Ab Bb` by metis_tac [BIJ_LINV_BIJ] >>
  qabbrev_tac `g' = LINV g Bb` >>
  `BIJ f Ainf (IMAGE f Ainf)`
     by (match_mp_tac INJ_BIJ_SUBSET >> simp[Abbr`Ainf`, SUBSET_DEF]) >>
  `BIJ f Aa (IMAGE f Aa)`
     by (match_mp_tac INJ_BIJ_SUBSET >> simp[Abbr`Aa`, SUBSET_DEF]) >>
  qexists_tac `λe. if e ∈ Aa ∨ e ∈ Ainf then f e else g' e` >>
  `∀y. y ∈ Bb ⇒ y ∈ t` by (simp[Abbr`Bb`] >> metis_tac[]) >>
  `IMAGE f Ainf ∩ Bb = ∅`
     by (simp[EXTENSION] >> qx_gen_tac `y` >> Cases_on `y ∈ Bb` >> simp[] >>
         qx_gen_tac `x` >> Cases_on `y = f x` >> simp[] >>
         simp[Abbr`Ainf`] >> Cases_on `x ∈ s` >> simp[] >>
         qsuff_tac `x ∈ Ab` >- rw[] >>
         `∃i. f x ∈ B i`
            by (Q.UNDISCH_THEN `y ∈ Bb` mp_tac >> simp[Abbr`Bb`] >>
                metis_tac[]) >>
         `∃y0. y0 ∈ B (i - 1) ∧ (x = g y0)` by metis_tac[] >>
         simp[Abbr`Ab`, Abbr`Bb`] >> metis_tac[]) >>
  `IMAGE f Aa ∩ Bb = ∅`
     by (simp[EXTENSION] >> qx_gen_tac `y` >> Cases_on `y ∈ Bb` >> simp[] >>
         qx_gen_tac `x` >> Cases_on `y = f x` >> simp[] >>
         Tactical.REVERSE (Cases_on `x ∈ s`) >- metis_tac[] >>
         qsuff_tac `x ∈ Ab` >- (fs[EXTENSION] >> metis_tac[]) >>
         `∃i. f x ∈ B i`
            by (Q.UNDISCH_THEN `y ∈ Bb` mp_tac >> simp[Abbr`Bb`] >>
                metis_tac[]) >>
         `∃y0. y0 ∈ B (i - 1) ∧ (x = g y0)` by metis_tac[] >>
         simp[Abbr`Ab`, Abbr`Bb`] >> metis_tac[]) >>
  qabbrev_tac `FF = λe. if e ∈ Aa ∨ e ∈ Ainf then f e else g' e` >>
  `∀x. x ∈ s ⇒ FF x ∈ t`
    by (rw[Abbr`FF`] >- metis_tac [INJ_DEF] >- metis_tac [INJ_DEF] >>
        metis_tac [BIJ_DEF, INJ_DEF, IN_DIFF]) >>
  simp[BIJ_DEF] >> conj_tac >| [
    simp[INJ_DEF] >>
    map_every qx_gen_tac [`x1`, `x2`] >> strip_tac >>
    Cases_on `x1 ∈ Aa ∨ x1 ∈ Ainf` >| [
      simp[Abbr`FF`] >> Cases_on `x2 ∈ Aa ∨ x2 ∈ Ainf` >> simp[]
        >- metis_tac [INJ_DEF] >>
      `x2 ∈ Ab` by metis_tac[IN_DIFF] >>
      `g' x2 ∈ Bb` by metis_tac [BIJ_IFF_INV] >>
      metis_tac[BIJ_IFF_INV, IN_INTER, NOT_IN_EMPTY],
      simp[Abbr`FF`] >>
      `x1 ∈ Ab` by metis_tac [IN_DIFF] >>
      `g' x1 ∈ Bb` by metis_tac [BIJ_IFF_INV] >>
      Tactical.REVERSE (Cases_on `x2 ∈ Aa ∨ x2 ∈ Ainf`) >> simp[]
        >- (`x2 ∈ Ab` by metis_tac [IN_DIFF] >>
            metis_tac[BIJ_DEF, INJ_DEF]) >>
      metis_tac [BIJ_IFF_INV, IN_INTER, NOT_IN_EMPTY]
    ],
    simp[SURJ_DEF] >> qx_gen_tac `y` >> strip_tac >>
    Cases_on `y ∈ Bb` >-
      (qexists_tac `g y` >> conj_tac >- metis_tac [INJ_DEF] >>
       simp[Abbr`FF`] >>
       `g y ∈ Ab` by (simp[Abbr`Ab`] >> metis_tac[]) >>
       `g y ∉ Aa ∧ g y ∉ Ainf` by metis_tac [IN_DIFF, NOT_IN_EMPTY, IN_INTER] >>
       simp[Abbr`g'`] >> metis_tac [LINV_DEF, BIJ_DEF]) >>
    Cases_on `y ∈ IMAGE f Aa` >-
      (`∃x. x ∈ Aa ∧ (y = f x)` by (fs[] >> metis_tac[]) >>
       qexists_tac `x` >> simp[Abbr`FF`]) >>
    Cases_on `∃x. x ∈ s ∧ (y = f x)` >-
      (fs[] >> `x ∉ Aa` by metis_tac[] >>
       `x ∉ Ab`
          by (simp[Abbr`Ab`] >> qx_gen_tac `y0` >>
              Cases_on `y0 ∈ Bb` >> simp[] >>
              `∃j. y0 ∈ B j` by (fs[Abbr`Bb`] >> metis_tac[]) >>
              `f (g y0) ∈ B (SUC j)` by (simp[] >> metis_tac[]) >>
              `f (g y0) ∈ Bb` by (simp[Abbr`Bb`] >> metis_tac[]) >>
              metis_tac[]) >>
       `x ∈ Ainf` by metis_tac [IN_DIFF] >>
       qexists_tac `x` >> simp[Abbr`FF`]) >>
    fs[] >>
    `y ∈ B 0` by (simp[Abbr`b0`] >> metis_tac[]) >>
    `y ∈ Bb` by (simp_tac (srw_ss()) [Abbr`Bb`] >> metis_tac[])
  ]);

val CARDEQ_FINITE = store_thm(
  "CARDEQ_FINITE",
  ``s1 ≈ s2 ⇒ (FINITE s1 ⇔ FINITE s2)``,
  metis_tac [cardeq_def, BIJ_FINITE, BIJ_LINV_BIJ]);

val CARDEQ_CARD = store_thm(
  "CARDEQ_CARD",
  ``s1 ≈ s2 ∧ FINITE s1 ⇒ (CARD s1 = CARD s2)``,
  metis_tac [cardeq_def, FINITE_BIJ_CARD_EQ, CARDEQ_FINITE]);

val CARDEQ_0 = store_thm(
  "CARDEQ_0",
  ``(x ≈ ∅ ⇔ (x = ∅)) ∧ ((∅ ≈ x) ⇔ (x = ∅))``,
  rw[cardeq_def, BIJ_EMPTY]);

val CARDEQ_INSERT = store_thm(
  "cardeq_INSERT",
  ``(x INSERT s) ≈ s ⇔ x ∈ s ∨ INFINITE s``,
  simp[EQ_IMP_THM] >> conj_tac
    >- (Cases_on `FINITE s` >> simp[] >> strip_tac >>
        `CARD (x INSERT s) = CARD s` by metis_tac [CARDEQ_CARD, cardeq_SYM] >>
        pop_assum mp_tac >> srw_tac[ARITH_ss][]) >>
  Cases_on `x ∈ s` >- metis_tac [ABSORPTION, cardeq_REFL] >> rw[] >>
  match_mp_tac cardleq_ANTISYM >> Tactical.REVERSE conj_tac
    >- (rw[cardleq_def] >> qexists_tac `λx. x` >> rw[INJ_DEF]) >>
  rw[cardleq_def] >> fs[infinite_num_inj] >>
  qexists_tac `λe. if e = x then f 0
                   else case some n. e = f n of
                          NONE => e
                        | SOME n => f (n + 1)` >>
  fs[INJ_DEF] >>
  `∀x y. (f x = f y) ⇔ (x = y)` by metis_tac[] >> rw[] >| [
    rw[optionTheory.option_case_compute],
    DEEP_INTRO_TAC optionTheory.some_intro >> rw[] >>
    metis_tac [DECIDE ``0 ≠ x + 1``],
    DEEP_INTRO_TAC optionTheory.some_intro >> rw[] >>
    metis_tac [DECIDE ``0 ≠ x + 1``],
    pop_assum mp_tac >>
    DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
    DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
  ]);

(* ∀s. INFINITE s ⇒ x INSERT s ≈ s

   more useful then CARDEQ_INSERT as a (conditional) "rewrite", when
   working with the ≈ congruence (rather than equality) *)
val CARDEQ_INSERT_RWT = save_thm(
  "CARDEQ_INSERT_RWT",
  ``INFINITE (s:'a set)`` |> ASSUME |> DISJ2 ``(x:'a) ∈ s``
                          |> EQ_MP (SYM CARDEQ_INSERT) |> DISCH_ALL
                          |> Q.GEN `s`)

val _ = export_theory()










