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

(*
val INFINITE_CROSS_UNIV = store_thm(
  "INFINITE_CROSS_UNIV",
  ``INFINITE s ⇒ (s × s ≈ s)``,
  strip_tac >>
  qabbrev_tac `A = { (As,f) | As ⊆ s ∧ BIJ f As (As × As) ∧
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
  `({}, K ARB) ∈ A` by simp[Abbr`A`, BIJ_EMPTY] >>
  `∀x. x ∈ A ==> (({},K ARB), x) ∈ rr` by simp[Abbr`rr`, FORALL_PROD] >>
  `∀t. chain t rr ⇒ upper_bounds t rr ≠ {}`
     by (gen_tac >>
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
         `(BigSet,BigF) ∈ A` by
            (unabbrev_in_goal "A" >> simp[] >> rpt conj_tac
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
             simp[range_def] >> qexists_tac `({}, K ARB)` >> simp[]) >>
         (* upper bound really is bigger than arbitrary element of chain *)
         simp[FORALL_PROD] >> map_every qx_gen_tac [`s1`, `f1`] >>
         Cases_on `(s1,f1) ∈ t` >> simp[] >>
         unabbrev_in_goal "rr" >> simp[] >> conj_tac
         >- (simp[Abbr`BigSet`] >> match_mp_tac SUBSET_BIGUNION_I >>
             simp[pairTheory.EXISTS_PROD] >> metis_tac[]) >>
         qx_gen_tac `x` >> strip_tac >> simp[Abbr`BigF`] >>
         DEEP_INTRO_TAC optionTheory.some_intro >>
         simp[FORALL_PROD] >> metis_tac[]) >>
  `A ≠ {}` by (strip_tac >> fs[]) >>
  `∃Mf. Mf ∈ maximal_elements A rr` by metis_tac [zorns_lemma] >>
  `∃M mf. Mf = (M,mf)` by metis_tac [pairTheory.pair_CASES] >>
  pop_assum SUBST_ALL_TAC >>
  fs[maximal_elements_def] >>
  Q.UNDISCH_THEN `(M,mf) ∈ A` mp_tac >> unabbrev_in_goal "A" >> simp[] >>
  strip_tac >>
  `M ≈ M × M` by metis_tac[cardeq_def] >>
  Cases_on `M ≈ s` >- metis_tac [CARDEQ_CROSS, cardeq_TRANS, cardeq_SYM] >>
  `M ≼ s` by simp[SUBSET_CARDLEQ] >>
  `M ≠ {}`
     by (strip_tac >> fs[] >>
         `∃c. c ∈ s` by metis_tac [INFINITE_INHAB] >>
         first_x_assum (qspec_then `({c}, (λx. if x = c then (c,c)
                                               else ARB))` mp_tac) >>
         `mf = K ARB` by simp[FUN_EQ_THM] >> pop_assum SUBST_ALL_TAC >>
         map_every unabbrev_in_goal ["A", "rr"] >> simp[better_BIJ] >>
         unabbrev_in_goal "A" >> simp[better_BIJ, FORALL_PROD]) >>
  `∀e. M ≠ {e}`
     by (rpt strip_tac >> fs[] >>
         `∃Nf n. INJ Nf univ(:num) s ∧ (Nf n = e)`
           by (`∃Nf0. INJ Nf0 univ(:num) s` by metis_tac [infinite_num_inj] >>
               Cases_on `∃n. Nf0 n = e` >- metis_tac[] >> fs[]
               map_every qexists_tac [`λn. if n = 0 then e else Nf0 n`, `0`] >>
               simp[] >> fs[INJ_DEF] >> rw[]) >>
         qabbrev_tac `
           Nfn = λa. case some m. Nf m = a of
                           NONE => ARB
                         | SOME m => (Nf (nfst m), Nf (nsnd m))` >>
         `(IMAGE Nf univ(:num), Nfn) ∈ A`
           by (simp[Abbr`A`] >> conj_tac
               >- (fs[SUBSET_DEF, INJ_DEF] >> metis_tac[]) >>
               simp[better_BIJ] >>
               asm_simp_tac (srw_ss() ++ DNF_ss) [FORALL_PROD] >>
               `∀x y. (Nf x = Nf y) = (x = y)`
                 by metis_tac [INJ_DEF, IN_UNIV] >>
               simp[Abbr`Nfn`] >> conj_tac
               >- (map_every qx_gen_tac [`m`, `p`] >> strip_tac >>
                   map_every (fn q => qspec_then q (SUBST1_TAC o SYM)
                                                 numpairTheory.npair)
                             [`m`, `p`] >> simp[]) >>
               simp[FORALL_PROD] >>
               map_every qx_gen_tac [`m`, `p`] >> qexists_tac `m ⊗ p` >>
               simp[]) >>
         first_x_assum (qspec_then `(IMAGE Nf univ(:num), Nfn)` mp_tac) >>
         map_every unabbrev_in_goal ["A", "rr"] >> simp[better_BIJ] >>
         `∀x y. (Nf x = Nf y) = (x = y)` by metis_tac [INJ_DEF, IN_UNIV] >>
         simp[Abbr`Nfn`] >>
         asm_simp_tac (srw_ss() ++ DNF_ss) [] >> DISJ1_TAC >> qexists_tac `n` >>





  `INFINITE M`
    by (strip_tac >>
  `M ≈ {T;F} × M`
     by (match_mp_tac cardleq_ANTISYM >> conj_tac
         >- (simp[cardleq_def] >> qexists_tac `λx. (T,x)` >> simp[INJ_DEF]) >>
         `M × M ≼ M` by metis_tac [CARDEQ_CARDLEQ, cardleq_REFL, cardeq_REFL] >>
         qsuff_tac `{T;F} × M ≼ M × M` >- metis_tac [cardleq_TRANS] >>
         match_mp_tac CARDLEQ_CROSS_CONG >> simp[FINITE_CLE_INFINITE]



  `s = M UNION (s DIFF M)` by (fs[EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
  `¬(s DIFF M ≼ M)`
    by (strip_tac >>
*)


val _ = export_theory()










