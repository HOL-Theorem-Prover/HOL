(* Define the type of hereditarily finite sets.

   Single (recursive) constructor is

     fromSet : hfs set -> hfs

   where the set must be finite.  (Perhaps an argument to have a finite set
   type in the core distribution?)

   Because there is just one constructor, there is a total inverse to
   fromSet, called toSet

     toSet : hfs -> hfs set

   where we have

     fromSet (toSet h) = h

   Future work:
   - define empty hfs value
   - define other operations such as insert, intersection, union and
     cardinality
   - prove induction principle
   - prove recursion principle

   The type is defined via a cute bijection (due to Ackermann
   according to Wikipedia) with the natural numbers.

   Inspired to do this by Larry Paulson's talk about using h.f. sets
   as part of a mechanisation of automata theory at CADE 2015. There (in
   Isabelle/HOL), the type definition mechanism can create the type
   directly so the Ackermann bijection is not required.
*)

open HolKernel Parse boolLib bossLib;

open lcsymtacs
open pred_setTheory

val _ = new_theory "hfs";

val _ = ParseExtras.tight_equality()

val _ = temp_overload_on ("mk", ``SUM_IMAGE ((EXP) 2)``)

val numeq_wlog = prove(
  ``∀P. (∀n m. P n m ⇔ P m n) ∧ (∀n m. P n m ⇒ n ≤ m) ⇒
        (∀n m. P n m ⇒ (n = m))``,
  metis_tac [DECIDE ``∀n m. n ≤ m ∧ m ≤ n ⇒ m = n``]);

val strictly_increasing_SUC_extends = prove(
  ``(∀n. f n < f (n + 1)) ⇒ (∀n m. n < m ⇒ f n < f m)``,
  strip_tac >> Induct_on `m` >> simp[] >> rpt strip_tac >>
  rename1 `n < SUC m` >>
  `n = m ∨ n < m` by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  metis_tac [DECIDE ``∀m n p. m < n ⇒ n < p ⇒ m < p``]);

val strictly_increasing_injective = prove(
  ``(∀n. f n < f (n + 1)) ⇒ ∀n1 n2. f n1 = f n2 ⇔ n1 = n2``,
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  qspec_then `λn m. f n = f m` (irule o BETA_RULE) numeq_wlog >>
  qexists_tac `f` >> simp[] >> spose_not_then strip_assume_tac >>
  rename1 `¬(n ≤ m)` >> `m < n` by simp[] >>
  `f m < f n` by metis_tac [strictly_increasing_SUC_extends] >>
  metis_tac[DECIDE ``¬(x < x)``]);

val strictly_increasing_nobounds = prove(
  ``(∀n. f n < f (n + 1)) ⇒ ∀b. ∃n. b < f n``,
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  rename1 `bnd < f _` >>
  `∀n. f n ≤ bnd` by metis_tac[DECIDE ``¬(x < y) ⇒ y ≤ x``] >>
  `∀n m. f n = f m ⇔ n = m` by metis_tac[strictly_increasing_injective] >>
  `INJ f (count (bnd + 2)) (count (bnd + 1))`
    by simp[INJ_DEF, DECIDE ``x < y + 1 ⇔ x ≤ y``] >>
  `FINITE (count (bnd + 1))` by simp[] >>
  `CARD (count (bnd + 1)) < CARD (count (bnd + 2))` by simp[] >>
  metis_tac[PHP]);

val TWO_EXP_BOUNDS = prove(
  ``∀n. ∃j. n < 2 ** j``,
  match_mp_tac strictly_increasing_nobounds >> simp[arithmeticTheory.EXP_ADD]);

val bound_exists = prove(
  ``∀n. n < 2 ** (LEAST m. n < 2 ** m) ∧
        ∀p. p < (LEAST m. n < 2 ** m) ⇒ 2 ** p ≤ n``,
  qx_gen_tac `n` >>
  qspec_then `λm. n < 2 ** m`
    (match_mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.NOT_LESS])
     whileTheory.LEAST_EXISTS_IMP >>
  metis_tac[TWO_EXP_BOUNDS]);

val mk_minimum = prove(
  ``∀s. FINITE s ⇒ ∀j. j ∈ s ⇒ 2 ** j ≤ mk s``,
  ho_match_mp_tac FINITE_INDUCT >> simp[] >>
  dsimp[SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >>
  rpt strip_tac >> res_tac >> simp[]);

val mk_onto = prove(
  ``∀n. ∃s. FINITE s ∧ mk s = n``,
  completeInduct_on `n` >>
  qspec_then `n` strip_assume_tac bound_exists >>
  qabbrev_tac `m = LEAST m. n < 2 EXP m` >>
  Cases_on `m = 0`
  >- (fs[] >> `n = 0` by simp[] >> qexists_tac `∅` >>
      simp[SUM_IMAGE_THM]) >>
  `m - 1 < m` by simp[] >>
  `2 ** (m - 1) ≤ n` by simp[] >>
  qabbrev_tac `M = 2 ** (m - 1)` >>
  `0 < M` by simp[Abbr`M`] >>
  `n - M < n` by simp[] >>
  `∃s0. FINITE s0 ∧ mk s0 = n - M` by metis_tac[] >>
  qexists_tac `(m - 1) INSERT s0` >>
  simp[SUM_IMAGE_THM] >>
  Cases_on `m - 1 ∈ s0`
  >- (`M ≤ mk s0` by metis_tac[mk_minimum] >>
      `2 * M ≤ n` by simp[] >>
      `2 * M = 2 ** m` suffices_by simp[] >>
      simp[Abbr`M`]  >> fs[GSYM arithmeticTheory.EXP] >>
      `SUC (m - 1) = m` by simp[] >> lfs[]) >>
  simp[DELETE_NON_ELEMENT_RWT]);

val split_sets = prove(
  ``s1 = (s1 ∩ s2) ∪ (s1 DIFF s2)``,
  simp[EXTENSION] >> metis_tac[]);

val DISJOINT_DIFF = prove(
  ``DISJOINT (s1 DIFF s2) (s2 DIFF s1)``,
  simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]);

val DIFF_NONEMPTY = prove(
  ``s1 ≠ s2 ⇔ s1 DIFF s2 ≠ ∅ ∨ s2 DIFF s1 ≠ ∅``,
  simp[EXTENSION] >> metis_tac[]);

val disjoint_inequal_has_maximum = prove(
  ``FINITE s1 ∧ FINITE s2 ∧ DISJOINT s1 s2 ∧ s1 ≠ s2 ⇒
    (∃m. m ∈ s1 ∧ (∀n. n ∈ s2 ⇒ n < m)) ∨
    (∃m. m ∈ s2 ∧ (∀n. n ∈ s1 ⇒ n < m))``,
  Cases_on `s1 = ∅`
  >- (simp[] >> strip_tac >>
      `∃m s0. s2 = m INSERT s0` by metis_tac[SET_CASES] >> dsimp[]) >>
  Cases_on `s2 = ∅` >> simp[]
  >- (`∃m s0. s1 = m INSERT s0` by metis_tac[SET_CASES] >> dsimp[]) >>
  qabbrev_tac `m1 = MAX_SET s1` >>
  qabbrev_tac `m2 = MAX_SET s2` >>
  strip_tac >>
  `m1 ∈ s1 ∧ (∀a. a ∈ s1 ⇒ a ≤ m1) ∧ m2 ∈ s2 ∧ (∀b. b ∈ s2 ⇒ b ≤ m2)`
    by metis_tac[MAX_SET_DEF] >>
  Cases_on `m1 < m2`
  >- (disj2_tac >> qexists_tac `m2` >> simp[] >> rpt strip_tac >> res_tac >>
      simp[]) >>
  disj1_tac >> qexists_tac `m1` >> simp[] >> rpt strip_tac >>
  `m1 ≠ m2` by (strip_tac >> fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  res_tac >> simp[]);

val topdown_induct = prove(
  ``P ∅ ∧
    (∀e s0. P s0 ∧ e ∉ s0 ∧ (∀n. n ∈ s0 ⇒ n < e) ∧ FINITE s0 ⇒
            P (e INSERT s0)) ⇒
    (∀s. FINITE s ⇒ P s)``,
  strip_tac >> gen_tac >> Induct_on `CARD s`
  >- (rpt strip_tac >> `s = ∅` by metis_tac[CARD_EQ_0] >> simp[]) >>
  rpt strip_tac >> `s ≠ ∅` by (strip_tac >> fs[]) >>
  qabbrev_tac `M = MAX_SET s` >>
  `M ∈ s ∧ ∀n. n ∈ s ⇒ n ≤ M` by metis_tac[MAX_SET_DEF] >>
  `s = M INSERT (s DELETE M)` by metis_tac[INSERT_DELETE] >>
  qabbrev_tac `s0 = s DELETE M` >>
  `M ∉ s0 ∧ FINITE s0` by simp[Abbr`s0`] >>
  rename1 `SUC n = CARD s` >>
  `CARD s = SUC (CARD s0)` by simp[] >>
  `n = CARD s0` by simp[] >>
  `P s0` by metis_tac[] >>
  `∀n. n ∈ s0 ⇒ n < M`
    by (fs[] >> metis_tac[DECIDE ``x ≤ y ∧ x ≠ y ⇒ x < y``]) >>
  metis_tac[]);

val mk_upper_bound = prove(
  ``∀s. FINITE s ⇒ ∀b. (∀n. n ∈ s ⇒ n < b) ⇒ mk s < 2 ** b``,
  ho_match_mp_tac topdown_induct >>
  dsimp[SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT] >> rpt strip_tac >>
  rename1 `e ∉ s` >>
  `mk s < 2 ** e` by metis_tac[] >>
  rename1 `e < b` >>
  `∃d. b = SUC d + e` by metis_tac[arithmeticTheory.LESS_STRONG_ADD] >>
  simp[arithmeticTheory.EXP_ADD, arithmeticTheory.EXP] >>
  match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `2 * 2 ** e` >> simp[]);

val mk_11 = prove(
  ``FINITE s1 ∧ FINITE s2 ⇒ (mk s1 = mk s2 ⇔ s1 = s2)``,
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `c = s1 ∩ s2` >>
  qabbrev_tac `t1 = s1 DIFF s2` >>
  qabbrev_tac `t2 = s2 DIFF s1` >>
  `s1 = c ∪ t1 ∧ s2 = c ∪ t2` by metis_tac[split_sets, INTER_COMM] >>
  `FINITE c ∧ FINITE t1 ∧ FINITE t2` by simp[Abbr`c`, Abbr`t1`, Abbr`t2`] >>
  `c ∩ t1 = ∅ ∧ c ∩ t2 = ∅`
    by (simp[Abbr`c`, Abbr`t1`, Abbr`t2`, EXTENSION] >> metis_tac[]) >>
  `mk s1 = mk c + mk t1 ∧ mk s2 = mk c + mk t2`
    by (rpt BasicProvers.VAR_EQ_TAC >>
        Q.UNDISCH_THEN `mk (c ∪ t1) = mk (c ∪ t2)` kall_tac >>
        simp[SUM_IMAGE_UNION, SUM_IMAGE_THM]) >>
  `mk t1 = mk t2` by simp[] >>
  `DISJOINT t1 t2` by metis_tac[DISJOINT_DIFF] >>
  `t1 ≠ t2` by metis_tac[] >>
  `(∃m1. m1 ∈ t1 ∧ (∀n. n ∈ t2 ⇒ n < m1)) ∨
   (∃m2. m2 ∈ t2 ∧ (∀n. n ∈ t1 ⇒ n < m2))`
     by metis_tac[disjoint_inequal_has_maximum]
  >- (`mk t2 < 2 ** m1` by metis_tac[mk_upper_bound] >>
      `2 ** m1 ≤ mk t1` by metis_tac[mk_minimum] >> lfs[]) >>
  `mk t1 < 2 ** m2` by metis_tac[mk_upper_bound] >>
  `2 ** m2 ≤ mk t2` by metis_tac[mk_minimum] >> lfs[])

val mk_BIJ = prove(
  ``BIJ mk {s | FINITE s} univ(:num)``,
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, mk_11, mk_onto]);

val hfs = new_type_definition(
  "hfs",
  prove(``?x:num. (\x. T) x``, simp[]))

val HFS_TYBIJ =
    define_new_type_bijections { ABS = "mkHFS", REP = "destHFS",
                                 name = "HFS_TYBIJ", tyax = hfs}
                               |> SIMP_RULE (srw_ss()) []

val mkHFS_11 = store_thm(
  "mkHFS_11[simp]",
  ``mkHFS n1 = mkHFS n2 ⇔ n1 = n2``,
  metis_tac[HFS_TYBIJ]);

val destHFS_11 = store_thm(
  "destHFS_11[simp]",
  ``destHFS h1 = destHFS h2 ⇔ h1 = h2``,
  metis_tac[HFS_TYBIJ]);

val toSet_def = Define`
  toSet hfs = IMAGE mkHFS (LINV mk { s | FINITE s } (destHFS hfs))
`;

val LINV_mk_11 = store_thm(
  "LINV_mk_11[simp]",
  ``LINV mk {s | FINITE s} x = LINV mk {s | FINITE s} y ⇔ x = y``,
  `BIJ (LINV mk {s | FINITE s}) univ(:num) { s | FINITE s}`
    by simp[BIJ_LINV_BIJ, mk_BIJ] >>
  fs[BIJ_DEF, INJ_DEF, EQ_IMP_THM]);

val toSet_11 = store_thm(
  "toSet_11[simp]",
  ``toSet h1 = toSet h2 ⇔ h1 = h2``,
  simp[toSet_def, IMAGE_11]);

val FINITE_toSet = store_thm(
  "FINITE_toSet[simp]",
  ``FINITE (toSet h)``,
  simp[toSet_def] >>
  `BIJ (LINV mk {s | FINITE s}) univ(:num) { s | FINITE s}`
    by simp[BIJ_LINV_BIJ, mk_BIJ] >>
  fs[BIJ_DEF, INJ_DEF]);

val fromSet_def = Define`
  fromSet s = mkHFS (mk (IMAGE destHFS s))
`;

val fromSet_toSet = store_thm(
  "fromSet_toSet",
  ``fromSet (toSet h) = h``,
  simp[fromSet_def, toSet_def] >> simp[GSYM IMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF, HFS_TYBIJ] >>
  strip_assume_tac (MATCH_MP BIJ_LINV_INV mk_BIJ) >> fs[HFS_TYBIJ]);

val _ = hide "mk"

val _ = export_theory();
