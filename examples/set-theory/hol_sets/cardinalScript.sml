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
val _ = export_rewrites ["cardleq_REFL"]

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

val EMPTY_CARDLEQ = store_thm(
  "EMPTY_CARDLEQ",
  ``{} ≼ t``,
  simp[cardleq_def, INJ_EMPTY]);  (* export_rewrites for pred_set *)
val _ = export_rewrites ["EMPTY_CARDLEQ"]

val FINITE_CLE_INFINITE = store_thm(
  "FINITE_CLE_INFINITE",
  ``FINITE s ∧ INFINITE t ==> s ≼ t``,
  qsuff_tac `INFINITE t ⇒ ∀s. FINITE s ⇒ s ≼ t` >- metis_tac[] >>
  strip_tac >> Induct_on `FINITE` >> conj_tac >- simp[] >>
  simp[cardleq_def] >> gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                              (Q.X_CHOOSE_THEN `f` assume_tac)) >>
  qx_gen_tac `e` >> strip_tac >>
  `FINITE (IMAGE f s)` by simp[] >>
  `∃y. y ∈ t ∧ y ∉ IMAGE f s` by metis_tac [IN_INFINITE_NOT_FINITE] >>
  qexists_tac `λx. if x = e then y else f x` >>
  fs[INJ_DEF] >> asm_simp_tac (srw_ss() ++ DNF_ss) [] >> rw[] >> metis_tac[])

val FORALL_PROD = pairTheory.FORALL_PROD
val CARDEQ_CROSS = store_thm(
  "CARDEQ_CROSS",
  ``s1 ≈ s2 ∧ t1 ≈ t2 ⇒ (s1 × t1 ≈ s2 × t2)``,
  simp[cardeq_def] >>
  disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `f` assume_tac)
                              (Q.X_CHOOSE_THEN `g` assume_tac)) >>
  qexists_tac `f ## g` >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, FORALL_PROD,
       pairTheory.EXISTS_PROD] >>
  fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >> metis_tac []);

val SURJ_INJ_INV = store_thm(
  "SURJ_INJ_INV",
  ``SURJ f s t ⇒ ∃g. INJ g t s ∧ (∀y. y ∈ t ⇒ (f (g y) = y))``,
  simp[SURJ_DEF, INJ_DEF] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                (assume_tac o
                 SIMP_RULE (srw_ss() ++ DNF_ss)
                           [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])) >>
  metis_tac[]);

val CARDEQ_SUBSET_CARDLEQ = store_thm(
  "CARDEQ_SUBSET_CARDLEQ",
  ``s ≈ t ⇒ s ≼ t``,
  rw[cardeq_def, cardleq_def, BIJ_DEF] >> metis_tac[])

val CARDEQ_CARDLEQ = store_thm(
  "CARDEQ_CARDLEQ",
  ``s1 ≈ s2 ∧ t1 ≈ t2 ⇒ (s1 ≼ t1 ⇔ s2 ≼ t2)``,
  metis_tac[cardeq_SYM, CARDEQ_SUBSET_CARDLEQ, cardleq_TRANS])

val _ = type_abbrev ("inf", ``:num + 'a``)

val INFINITE_UNIV_INF = store_thm(
  "INFINITE_UNIV_INF",
  ``INFINITE univ(:'a inf)``,
  simp[INFINITE_UNIV] >> qexists_tac `SUC ++ I` >>
  simp[sumTheory.FORALL_SUM] >> qexists_tac `INL 0` >> simp[]);
val _ = export_rewrites ["INFINITE_UNIV_INF"]

val IMAGE_cardleq = store_thm(
  "IMAGE_cardleq",
  ``IMAGE f s ≼ s``,
  simp[cardleq_def] >> metis_tac [SURJ_IMAGE, SURJ_INJ_INV]);
val _ = export_rewrites ["IMAGE_cardleq"]

val CARDLEQ_CROSS_CONG = store_thm(
  "CARDLEQ_CROSS_CONG",
  ``x1 ≼ x2 ∧ y1 ≼ y2 ⇒ x1 CROSS y1 ≼ x2 CROSS y2``,
  simp[cardleq_def] >>
  disch_then (CONJUNCTS_THEN2 (Q.X_CHOOSE_THEN `f1` assume_tac)
                              (Q.X_CHOOSE_THEN `f2` assume_tac)) >>
  fs [INJ_DEF] >>
  qexists_tac `λ(x,y). (f1 x, f2 y)` >>
  simp[FORALL_PROD]);

val SUBSET_CARDLEQ = store_thm(
  "SUBSET_CARDLEQ",
  ``x ⊆ y ⇒ x ≼ y``,
  simp[SUBSET_DEF, cardleq_def] >> strip_tac >> qexists_tac `I` >>
  simp[INJ_DEF]);

open wellorderTheory
val cardleq_dichotomy = store_thm(
  "cardleq_dichotomy",
  ``s ≼ t ∨ t ≼ s``,
  `(∃w1. elsOf w1 = s) ∧ (∃w2. elsOf w2 = t)`
    by metis_tac [allsets_wellorderable] >>
  `orderlt w1 w2 ∨ orderiso w1 w2 ∨ orderlt w2 w1`
    by metis_tac [orderlt_trichotomy]
  >| [
    `∃f x. BIJ f s (elsOf (wobound x w2))`
      by metis_tac[orderlt_def, orderiso_thm] >>
    `elsOf (wobound x w2) ⊆ t`
      by (simp[elsOf_wobound, SUBSET_DEF] >> metis_tac [WIN_elsOf]) >>
    rw[] >> qsuff_tac `elsOf w1 ≼ elsOf w2` >- simp[] >>
    simp[cardleq_def] >> qexists_tac `f` >>
    fs[BIJ_DEF, INJ_DEF, SUBSET_DEF],

    `∃f. BIJ f s t` by metis_tac [orderiso_thm] >>
    fs[BIJ_DEF, cardleq_def] >> metis_tac[],

    `∃f x. BIJ f t (elsOf (wobound x w1))`
      by metis_tac[orderlt_def, orderiso_thm] >>
    `elsOf (wobound x w1) ⊆ s`
      by (simp[elsOf_wobound, SUBSET_DEF] >> metis_tac [WIN_elsOf]) >>
    rw[] >> qsuff_tac `elsOf w2 ≼ elsOf w1` >- simp[] >>
    simp[cardleq_def] >> qexists_tac `f` >>
    fs[BIJ_DEF, INJ_DEF, SUBSET_DEF]
  ]);

val _ = set_fixity "≺" (Infix(NONASSOC, 450))
val _ = overload_on ("≺", ``λ(s1:'a set) s2. ¬(s2 ≼ s1)``)

val cardleq_lteq = store_thm(
  "cardleq_lteq",
  ``s1 ≼ s2 ⇔ s1 ≺ s2 ∨ (s1 ≈ s2)``,
  metis_tac [cardleq_ANTISYM, cardleq_dichotomy, CARDEQ_SUBSET_CARDLEQ]);

val cardlt_REFL = store_thm(
  "cardlt_REFL",
  ``~(s ≺ s)``,
  simp[cardleq_REFL]);

val cardlt_lenoteq = store_thm(
  "cardlt_iso_REFL",
  ``s ≺ t ⇔ s ≼ t ∧ ¬(s ≈ t)``,
  metis_tac [cardleq_dichotomy, CARDEQ_SUBSET_CARDLEQ, cardeq_SYM,
             cardleq_ANTISYM, cardeq_REFL]);

val cardlt_TRANS = store_thm(
  "cardlt_TRANS",
  ``∀s t u:'a set. s ≺ t ∧ t ≺ u ⇒ s ≺ u``,
  metis_tac [cardleq_TRANS, cardleq_ANTISYM, CARDEQ_SUBSET_CARDLEQ,
             cardeq_SYM, cardlt_lenoteq]);

val better_BIJ = BIJ_DEF |> SIMP_RULE (srw_ss() ++ CONJ_ss) [INJ_DEF, SURJ_DEF]

fun unabbrev_in_goal s = let
  fun check th = let
    val c = concl th
    val _ = match_term ``Abbrev b`` c
    val (v,ty) = c |> rand |> lhand |> dest_var
  in
    if v = s then let
        val th' = PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
      in
        SUBST1_TAC th'
      end
    else NO_TAC
  end
in
  first_assum check
end

val set_binomial2 = store_thm(
  "set_binomial2",
  ``((A ∪ B) × (A ∪ B) = A × A ∪ A × B ∪ B × A ∪ B × B)``,
  simp[EXTENSION, FORALL_PROD] >>
  simp_tac (srw_ss() ++ DNF_ss) [DISJ_ASSOC]);

val lemma1 = prove(
  ``INFINITE M ∧ M ≈ M × M ⇒
    M ≈ {T;F} × M ∧
    ∀A B. DISJOINT A B ∧ A ≈ M ∧ B ≈ M ⇒ A ∪ B ≈ M``,
  strip_tac >> CONJ_ASM1_TAC
  >- (match_mp_tac cardleq_ANTISYM >> conj_tac
      >- (simp[cardleq_def] >> qexists_tac `λx. (T,x)` >> simp[INJ_DEF]) >>
     `M × M ≼ M` by metis_tac [CARDEQ_CARDLEQ, cardleq_REFL, cardeq_REFL] >>
     qsuff_tac `{T;F} × M ≼ M × M` >- metis_tac [cardleq_TRANS] >>
     match_mp_tac CARDLEQ_CROSS_CONG >> simp[FINITE_CLE_INFINITE]) >>
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  `(∃f1. BIJ f1 A M) ∧ (∃f2. BIJ f2 B M)` by metis_tac[cardeq_def] >>
  qsuff_tac `A ∪ B ≈ {T;F} × M`
  >- metis_tac [cardeq_TRANS, cardeq_SYM] >>
  simp[cardeq_def] >>
  qexists_tac `λx. if x ∈ A then (T,f1 x) else (F,f2 x)` >>
  simp[better_BIJ] >> rpt conj_tac
  >- (fs[better_BIJ] >> rw[])
  >- (map_every qx_gen_tac [`a`, `b`] >> strip_tac >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF, pairTheory.PAIR_EQ]) >>
  simp[FORALL_PROD] >> map_every qx_gen_tac [`test`, `m`] >> strip_tac >>
  Cases_on `test`
  >- (`∃a. a ∈ A ∧ (f1 a = m)` by metis_tac [BIJ_DEF, SURJ_DEF] >>
      qexists_tac `a` >> simp[]) >>
  `∃b. b ∈ B ∧ (f2 b = m)` by metis_tac [BIJ_DEF, SURJ_DEF] >>
  qexists_tac `b` >> simp[] >> metis_tac[]);

fun PRINT_TAC s gl = (print ("** " ^ s ^ "\n"); ALL_TAC gl)

val SET_SQUARED_CARDEQ_SET = store_thm(
  "SET_SQUARED_CARDEQ_SET",
  ``INFINITE s ⇒ (s × s ≈ s)``,
  PRINT_TAC "beginning s × s ≈ s proof" >>
  strip_tac >>
  qabbrev_tac `A = { (As,f) | INFINITE As ∧ As ⊆ s ∧ BIJ f As (As × As) ∧
                              ∀x. x ∉ As ⇒ (f x = ARB) }` >>
  qabbrev_tac `
    rr = {((s1:'a set,f1),(s2,f2)) | (s1,f1) ∈ A ∧ (s2,f2) ∈ A ∧ s1 ⊆ s2 ∧
              ∀x. x ∈ s1 ⇒ (f1 x = f2 x)}
  ` >>
  `partial_order rr A`
     by (simp[partial_order_def] >> rpt conj_tac
         >- (simp[domain_def, Abbr`rr`, SUBSET_DEF] >> rw[] >> rw[])
         >- (simp[range_def, Abbr`rr`, SUBSET_DEF] >> rw[] >> rw[])
         >- (simp[transitive_def, Abbr`rr`] >> rw[] >>
             metis_tac [SUBSET_TRANS, SUBSET_DEF])
         >- simp[reflexive_def, Abbr`rr`, FORALL_PROD] >>
         simp[antisym_def, Abbr`rr`, FORALL_PROD] >>
         map_every qx_gen_tac [`s1`, `f1`, `s2`, `f2`] >>
         strip_tac >> `s1 = s2` by metis_tac [SUBSET_ANTISYM] >>
         fs[Abbr`A`] >> simp[FUN_EQ_THM] >> metis_tac[]) >>
  `A ≠ ∅`
    by (`∃Nf. INJ Nf univ(:num) s` by metis_tac [infinite_num_inj] >>
        qabbrev_tac `
           Nfn = λa. case some m. Nf m = a of
                           NONE => ARB
                         | SOME m => (Nf (nfst m), Nf (nsnd m))` >>
        `(IMAGE Nf univ(:num), Nfn) ∈ A`
           by (`∀x y. (Nf x = Nf y) = (x = y)`
                 by metis_tac [INJ_DEF, IN_UNIV] >>
               simp[Abbr`A`] >> conj_tac
               >- (fs[SUBSET_DEF, INJ_DEF] >> metis_tac[]) >>
               simp[better_BIJ] >>
               asm_simp_tac (srw_ss() ++ DNF_ss) [FORALL_PROD] >>
               simp[Abbr`Nfn`] >> conj_tac
               >- (map_every qx_gen_tac [`m`, `p`] >> strip_tac >>
                   map_every (fn q => qspec_then q (SUBST1_TAC o SYM)
                                                 numpairTheory.npair)
                             [`m`, `p`] >> simp[]) >>
               simp[FORALL_PROD] >>
               map_every qx_gen_tac [`m`, `p`] >> qexists_tac `m ⊗ p` >>
               simp[]) >>
        strip_tac >> fs[]) >>
  `∀t. chain t rr ⇒ upper_bounds t rr ≠ {}`
     by (PRINT_TAC "beginning proof that chains have upper bound" >>
         gen_tac >>
         simp[chain_def] >> strip_tac >>
         `∀s0 f. (s0,f) ∈ t ⇒ BIJ f s0 (s0 × s0) ∧ s0 ⊆ s ∧ (s0,f) ∈ A ∧
                              ∀x. x ∉ s0 ⇒ (f x = ARB)`
            by (rpt gen_tac >> strip_tac >>
                pop_assum (fn th => first_x_assum (fn impth =>
                  mp_tac (MATCH_MP impth (CONJ th th)))) >>
                rw[Abbr`rr`, Abbr`A`]) >>
         simp[upper_bounds_def] >> simp[EXTENSION] >>
         `∀s1 f1 s2 f2 x. (s1,f1) ∈ t ∧ (s2,f2) ∈ t ∧ x ∈ s1 ∧ x ∈ s2 ⇒
                          (f1 x = f2 x)`
            by (rpt strip_tac >>
                Q.UNDISCH_THEN `(s1,f1) ∈ t` (fn th1 =>
                   Q.UNDISCH_THEN `(s2,f2) ∈ t` (fn th2 =>
                    first_x_assum (fn impth =>
                                      mp_tac
                                          (MATCH_MP impth (CONJ th1 th2))))) >>
                simp[Abbr`rr`] >> rw[] >> rw[]) >>
         qabbrev_tac `BigSet = BIGUNION (IMAGE FST t)` >>
         qabbrev_tac `BigF = (λa. case some (s,f). (s,f) ∈ t ∧ a ∈ s of
                                    NONE => ARB
                                  | SOME (_, f) => f a)` >>
         Cases_on `t = ∅`
         >- (simp[range_def] >>
             `∃x. x ∈ A` by (fs[EXTENSION] >> metis_tac[]) >>
             map_every qexists_tac [`x`, `x`] >>
             simp[Abbr`rr`] >> Cases_on `x` >> simp[]) >>
         `(BigSet,BigF) ∈ A` by
            (unabbrev_in_goal "A" >> simp[] >> rpt conj_tac
             >- (simp[Abbr`BigSet`] >> DISJ2_TAC >>
                 simp[pairTheory.EXISTS_PROD] >>
                 `∃pr. pr ∈ t` by simp[MEMBER_NOT_EMPTY] >>
                 Cases_on `pr` >> res_tac >> fs[Abbr`A`] >> metis_tac[])
             >- (simp_tac (srw_ss() ++ DNF_ss)
                          [BIGUNION_SUBSET, FORALL_PROD, Abbr`BigSet`] >>
                 metis_tac[])
             >- ((* showing function is a bijection *)
                 asm_simp_tac (srw_ss() ++ DNF_ss)
                              [better_BIJ, FORALL_PROD, Abbr`BigF`,
                               Abbr`BigSet`, pairTheory.EXISTS_PROD] >>
                 rpt conj_tac
                 >- ((* function hits target set *)
                     map_every qx_gen_tac [`a`, `ss`, `sf`] >>
                     strip_tac >>
                     map_every qexists_tac [`ss`, `sf`, `ss`, `sf`] >>
                     simp[] >>
                     qmatch_abbrev_tac `FST XX ∈ ss ∧ SND XX ∈ ss` >>
                     `XX = sf a`
                        by (simp[Abbr`XX`] >>
                            DEEP_INTRO_TAC optionTheory.some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     `BIJ sf ss (ss × ss)` by metis_tac[] >> simp[] >>
                     pop_assum mp_tac >> simp_tac (srw_ss())[better_BIJ] >>
                     simp[])
                 >- ((* function is injective *)
                     map_every qx_gen_tac
                               [`a1`, `a2`, `s1`, `f1`, `s2`, `f2`] >>
                     strip_tac >>
                     qmatch_abbrev_tac `(XX1 = XX2) ⇒ (a1 = a2)` >>
                     `XX1 = f1 a1`
                        by (simp[Abbr`XX1`] >>
                            DEEP_INTRO_TAC optionTheory.some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     `XX2 = f2 a2`
                        by (simp[Abbr`XX2`] >>
                            DEEP_INTRO_TAC optionTheory.some_intro >>
                            simp[FORALL_PROD] >> metis_tac[]) >>
                     map_every markerLib.RM_ABBREV_TAC ["XX1", "XX2"] >>
                     rw[] >>
                     Q.UNDISCH_THEN `(s1,f1) ∈ t` (fn th1 =>
                        (Q.UNDISCH_THEN `(s2,f2) ∈ t` (fn th2 =>
                           (first_x_assum (fn impth =>
                              mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                     simp[Abbr`rr`, Abbr`A`] >> rw[]
                     >- (`f1 a1 = f2 a1` by metis_tac[] >>
                         `a1 ∈ s2` by metis_tac [SUBSET_DEF] >>
                         metis_tac [BIJ_DEF, INJ_DEF]) >>
                     `f2 a2 = f1 a2` by metis_tac[] >>
                     `a2 ∈ s1` by metis_tac [SUBSET_DEF] >>
                     metis_tac [BIJ_DEF, INJ_DEF]) >>
                 (* function is surjective *)
                 map_every qx_gen_tac [`a`, `b`, `s1`, `f1`, `s2`, `f2`] >>
                 strip_tac >>
                 Q.UNDISCH_THEN `(s1,f1) ∈ t` (fn th1 =>
                    (Q.UNDISCH_THEN `(s2,f2) ∈ t` (fn th2 =>
                       (first_assum (fn impth =>
                          mp_tac (MATCH_MP impth (CONJ th1 th2)) >>
                          assume_tac th1 >> assume_tac th2))))) >>
                 unabbrev_in_goal "rr" >> simp_tac(srw_ss())[] >> rw[]
                 >- (`a ∈ s2` by metis_tac [SUBSET_DEF] >>
                     `(a,b) ∈ s2 × s2` by simp[] >>
                     `∃x. x ∈ s2 ∧ (f2 x = (a,b))`
                       by metis_tac [SURJ_DEF, BIJ_DEF] >>
                     map_every qexists_tac [`x`, `s2`, `f2`] >>
                     simp[] >> DEEP_INTRO_TAC optionTheory.some_intro >>
                     simp[FORALL_PROD] >>
                     Tactical.REVERSE conj_tac >- metis_tac[] >>
                     map_every qx_gen_tac [`s3`, `f3`] >> strip_tac >>
                     Q.UNDISCH_THEN `(s2,f2) ∈ t` (fn th1 =>
                        (Q.UNDISCH_THEN `(s3,f3) ∈ t` (fn th2 =>
                           (first_x_assum (fn impth =>
                              mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                     unabbrev_in_goal "rr" >> simp[] >> rw[] >> metis_tac[]) >>
                 `b ∈ s1` by metis_tac [SUBSET_DEF] >>
                 `(a,b) ∈ s1 × s1` by simp[] >>
                 `∃x. x ∈ s1 ∧ (f1 x = (a,b))`
                   by metis_tac[BIJ_DEF, SURJ_DEF] >>
                 map_every qexists_tac [`x`, `s1`, `f1`] >> simp[] >>
                 DEEP_INTRO_TAC optionTheory.some_intro >>
                 simp[FORALL_PROD] >>
                 Tactical.REVERSE conj_tac >- metis_tac[] >>
                 map_every qx_gen_tac [`s3`, `f3`] >> strip_tac >>
                 Q.UNDISCH_THEN `(s1,f1) ∈ t` (fn th1 =>
                    (Q.UNDISCH_THEN `(s3,f3) ∈ t` (fn th2 =>
                       (first_x_assum (fn impth =>
                          mp_tac (MATCH_MP impth (CONJ th1 th2))))))) >>
                 unabbrev_in_goal "rr" >> simp[] >> rw[] >> metis_tac[]) >>
             (* function is ARB outside of domain *)
             qx_gen_tac `x` >>
             asm_simp_tac (srw_ss() ++ DNF_ss)
                          [Abbr`BigF`, Abbr`BigSet`,
                           DECIDE ``¬p∨q = (p ⇒ q)``, FORALL_PROD]>>
             strip_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
             simp[FORALL_PROD] >> metis_tac[]) >>
         qexists_tac `(BigSet, BigF)` >> conj_tac
         >- ((* (BigSet, BigF) ∈ range rr *)
             simp[range_def] >> qexists_tac `(BigSet,BigF)` >>
             simp[Abbr`rr`]) >>
         (* upper bound really is bigger than arbitrary element of chain *)
         simp[FORALL_PROD] >> map_every qx_gen_tac [`s1`, `f1`] >>
         Cases_on `(s1,f1) ∈ t` >> simp[] >>
         unabbrev_in_goal "rr" >> simp[] >> conj_tac
         >- (simp[Abbr`BigSet`] >> match_mp_tac SUBSET_BIGUNION_I >>
             simp[pairTheory.EXISTS_PROD] >> metis_tac[]) >>
         qx_gen_tac `x` >> strip_tac >> simp[Abbr`BigF`] >>
         DEEP_INTRO_TAC optionTheory.some_intro >>
         simp[FORALL_PROD] >> metis_tac[]) >>
  PRINT_TAC "proved that upper bound works" >>
  `∃Mf. Mf ∈ maximal_elements A rr` by metis_tac [zorns_lemma] >>
  `∃M mf. Mf = (M,mf)` by metis_tac [pairTheory.pair_CASES] >>
  pop_assum SUBST_ALL_TAC >>
  fs[maximal_elements_def] >>
  Q.UNDISCH_THEN `(M,mf) ∈ A` mp_tac >> unabbrev_in_goal "A" >> simp[] >>
  strip_tac >>
  `M ≈ M × M` by metis_tac[cardeq_def] >>
  Cases_on `M ≈ s` >- metis_tac [CARDEQ_CROSS, cardeq_TRANS, cardeq_SYM] >>
  `M ≼ s` by simp[SUBSET_CARDLEQ] >>
  `M ≈ {T;F} × M` by metis_tac [lemma1] >>
  `s = M UNION (s DIFF M)` by (fs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  `¬(s DIFF M ≼ M)`
    by (strip_tac >>
        qsuff_tac `s ≼ M` >- metis_tac [cardleq_ANTISYM] >>
        qsuff_tac `s ≼ {T;F} × M` >- metis_tac[CARDEQ_CARDLEQ, cardeq_REFL] >>
        `∃f0. INJ f0 (s DIFF M) M` by metis_tac[cardleq_def] >>
        simp[cardleq_def, INJ_DEF] >>
        qexists_tac `λa. if a ∈ M then (T,a) else (F,f0 a)` >>
        simp[] >> conj_tac
        >- (rw[] >> metis_tac [IN_DIFF, INJ_DEF]) >>
        rw[] >> prove_tac[IN_DIFF, INJ_DEF]) >>
  `¬(s DIFF M ≈ M)` by metis_tac [CARDEQ_SUBSET_CARDLEQ] >>
  `∃f. INJ f M (s DIFF M)` by metis_tac [cardleq_def, cardlt_lenoteq] >>
  qabbrev_tac `E = IMAGE f M` >>
  `E ⊆ s DIFF M` by (fs[INJ_DEF, SUBSET_DEF, Abbr`E`] >> metis_tac[]) >>
  `INJ f M E` by (fs[Abbr`E`, INJ_DEF] >> metis_tac[]) >>
  `SURJ f M E` by simp[Abbr`E`] >>
  `M ≈ E` by metis_tac[cardeq_def, BIJ_DEF] >>
  `E × E ≈ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `E × M ≈ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `M × E ≈ M` by metis_tac [CARDEQ_CROSS, cardeq_SYM, cardeq_TRANS] >>
  `DISJOINT (E × M) (E × E)`
    by (simp[DISJOINT_DEF, EXTENSION, FORALL_PROD] >>
        metis_tac [SUBSET_DEF, IN_DIFF]) >>
  `(E × M) ∪ (E × E) ≈ M` by metis_tac [lemma1] >>
  `DISJOINT (M × E) (E × M ∪ E × E)`
    by (simp[DISJOINT_DEF, EXTENSION, FORALL_PROD] >>
        metis_tac [SUBSET_DEF, IN_DIFF]) >>
  `M × E ∪ (E × M ∪ E × E) ≈ M` by metis_tac[lemma1] >>
  `M × E ∪ E × M ∪ E × E ≈ E`
    by metis_tac[UNION_ASSOC, cardeq_TRANS] >>
  pop_assum mp_tac >> qmatch_abbrev_tac `ME ≈ E ⇒ s × s ≈ s` >>
  strip_tac >>
  `∃f0. BIJ f0 E ME` by metis_tac [cardeq_def, cardeq_SYM] >>
  qabbrev_tac `FF = λm. if m ∈ M then mf m else if m ∈ E then f0 m else ARB` >>
  `(M ∪ E) × (M ∪ E) = M × M ∪ ME`
    by simp[Abbr`ME`, UNION_ASSOC, set_binomial2] >>
  qabbrev_tac `MM = M × M` >>
  `DISJOINT M E`
    by (simp[DISJOINT_DEF, EXTENSION] >> metis_tac[IN_DIFF, SUBSET_DEF]) >>
  `DISJOINT MM ME`
    by (pop_assum mp_tac >>
        simp[DISJOINT_DEF, EXTENSION, Abbr`ME`, Abbr`MM`, FORALL_PROD] >>
        metis_tac[]) >>
  PRINT_TAC "proving properties of new (can't exist) bijection" >>
  `BIJ FF (M ∪ E) ((M ∪ E) × (M ∪ E))`
    by (simp[better_BIJ, Abbr`FF`] >> rpt conj_tac
        >- (qx_gen_tac `m` >> Cases_on `m ∈ M` >> simp[] >>
            fs[better_BIJ] >> strip_tac >>
            map_every qunabbrev_tac [`ME`, `MM`] >>
            fs[] >> metis_tac[])
        >- (map_every qx_gen_tac [`m1`, `m2`] >>
            strip_tac >> fs[better_BIJ, DISJOINT_DEF, EXTENSION] >>
            metis_tac[])
        >- (simp[FORALL_PROD] >> map_every qx_gen_tac [`m1`, `m2`] >>
            strip_tac
            >- (fs[better_BIJ] >> qsuff_tac `(m1,m2) ∈ MM` >- metis_tac[] >>
                simp[Abbr`MM`]) >>
            (Q.UNDISCH_THEN `DISJOINT M E` mp_tac >>
             simp[DISJOINT_DEF, EXTENSION] >> strip_tac >>
             fs[better_BIJ] >>
             qsuff_tac `(m1,m2) ∈ ME` >- metis_tac[] >>
             simp[Abbr`ME`]))) >>
  `(M ∪ E, FF) ∈ A`
    by (simp[Abbr`A`] >> conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
        simp[Abbr`FF`]) >>
  `(M,mf) ≠ (M ∪ E, FF)`
    by (`M ≠ ∅` by metis_tac[FINITE_EMPTY] >>
        simp[] >> DISJ1_TAC >> simp[EXTENSION] >>
        fs[DISJOINT_DEF, EXTENSION] >> metis_tac[INJ_DEF]) >>
  qsuff_tac `((M,mf), (M ∪ E, FF)) ∈ rr` >- metis_tac[] >>
  simp[Abbr`rr`] >> conj_tac >- simp[Abbr`A`] >>
  simp[Abbr`FF`])

val SET_SUM_CARDEQ_SET = store_thm(
  "SET_SUM_CARDEQ_SET",
  ``INFINITE s ⇒
    s ≈ {T;F} × s ∧
    ∀A B. DISJOINT A B ∧ A ≈ s ∧ B ≈ s ⇒ A ∪ B ≈ s``,
  metis_tac[lemma1, SET_SQUARED_CARDEQ_SET, cardeq_SYM]);

val CARD_BIGUNION = store_thm(
  "CARD_BIGUNION",
  ``INFINITE k ∧ s1 ≼ k ∧ (∀e. e ∈ s1 ⇒ e ≼ k) ⇒ BIGUNION s1 ≼ k``,
  `BIGUNION s1 = BIGUNION (s1 DELETE ∅)` by (simp[EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `INFINITE k` >> simp[cardleq_def] >>
  disch_then (CONJUNCTS_THEN2
                  (Q.X_CHOOSE_THEN `f` strip_assume_tac) strip_assume_tac) >>
  qabbrev_tac `s = s1 DELETE ∅` >>
  `INJ f s k` by fs[INJ_DEF, Abbr`s`] >>
  `(s = ∅) ∨ ∃ff. SURJ ff k s` by metis_tac [inj_surj] >- simp[INJ_EMPTY] >>
  `∅ ∉ s` by simp[Abbr`s`] >>
  qsuff_tac `∃fg. SURJ fg k (BIGUNION s)` >- metis_tac[SURJ_INJ_INV] >>
  `k ≈ k × k` by metis_tac [SET_SQUARED_CARDEQ_SET, cardeq_SYM] >>
  `∃kkf. BIJ kkf k (k × k)` by metis_tac [cardeq_def] >>
  qsuff_tac `∃fg. SURJ fg (k × k) (BIGUNION s)`
  >- (strip_tac >> qexists_tac `fg o kkf` >> match_mp_tac SURJ_COMPOSE >>
      metis_tac[BIJ_DEF]) >>
  `∀e. e ∈ s ⇒ ∃g. SURJ g k e` by metis_tac[inj_surj, IN_DELETE] >>
  pop_assum (Q.X_CHOOSE_THEN `g` assume_tac o
             CONV_RULE (BINDER_CONV RIGHT_IMP_EXISTS_CONV THENC
                        SKOLEM_CONV)) >>
  qexists_tac `λ(k1,k2). g (ff k1) k2` >>
  asm_simp_tac (srw_ss() ++ DNF_ss)
       [SURJ_DEF, FORALL_PROD, pairTheory.EXISTS_PROD] >>
  fs[SURJ_DEF] >> metis_tac[]);


val _ = export_theory()
