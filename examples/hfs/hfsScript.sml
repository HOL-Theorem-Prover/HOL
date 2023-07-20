(* Define the type of hereditarily finite sets.

   Single (recursive) constructor is

     fromSet : hfs fset -> hfs

   where the fset type operator is that of finite sets.

   Because there is just one constructor, there is a total inverse to
   fromSet, called toSet

     toSet : hfs -> hfs set

   where we have

     fromSet (toSet h) = h

   Future work:
   - define other operations such as intersection, union and cardinality
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

open pred_setTheory finite_setTheory

val _ = new_theory "hfs";

Overload mk[local] = “fSUM_IMAGE ((EXP) 2)”

Theorem numeq_wlog[local]:
  ∀P. (∀n m. P n m ⇔ P m n) ∧ (∀n m. P n m ⇒ n ≤ m) ⇒
      (∀n m. P n m ⇒ (n = m))
Proof metis_tac [DECIDE ``∀n m. n ≤ m ∧ m ≤ n ⇒ m = n``]
QED

Theorem strictly_increasing_SUC_extends[local]:
  (∀n. f n < f (n + 1)) ⇒ (∀n m. n < m ⇒ f n < f m)
Proof
  strip_tac >> Induct_on `m` >> simp[] >> rpt strip_tac >>
  rename1 `n < SUC m` >>
  `n = m ∨ n < m` by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  metis_tac [DECIDE ``∀m n p. m < n ⇒ n < p ⇒ m < p``]
QED

Theorem strictly_increasing_injective[local]:
  (∀n. f n < f (n + 1)) ⇒ ∀n1 n2. f n1 = f n2 ⇔ n1 = n2
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  qspec_then `λn m. f n = f m` (irule o BETA_RULE) numeq_wlog >>
  qexists_tac `f` >> simp[] >> spose_not_then strip_assume_tac >>
  rename1 `¬(n ≤ m)` >> `m < n` by simp[] >>
  `f m < f n` by metis_tac [strictly_increasing_SUC_extends] >>
  metis_tac[DECIDE ``¬(x < x)``]
QED

Theorem strictly_increasing_nobounds[local]:
  (∀n. f n < f (n + 1)) ⇒ ∀b. ∃n. b < f n
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  rename1 `bnd < f _` >>
  `∀n. f n ≤ bnd` by metis_tac[DECIDE ``¬(x < y) ⇒ y ≤ x``] >>
  `∀n m. f n = f m ⇔ n = m` by metis_tac[strictly_increasing_injective] >>
  `INJ f (count (bnd + 2)) (count (bnd + 1))`
    by simp[INJ_DEF, DECIDE ``x < y + 1 ⇔ x ≤ y``] >>
  `FINITE (count (bnd + 1))` by simp[] >>
  `CARD (count (bnd + 1)) < CARD (count (bnd + 2))` by simp[] >>
  metis_tac[PHP]
QED

Theorem TWO_EXP_BOUNDS[local]:
  ∀n. ∃j. n < 2 ** j
Proof
  match_mp_tac strictly_increasing_nobounds >> simp[arithmeticTheory.EXP_ADD]
QED

Theorem bound_exists[local]:
  ∀n. n < 2 ** (LEAST m. n < 2 ** m) ∧
      ∀p. p < (LEAST m. n < 2 ** m) ⇒ 2 ** p ≤ n
Proof
  qx_gen_tac `n` >>
  qspec_then `λm. n < 2 ** m`
    (match_mp_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.NOT_LESS])
     whileTheory.LEAST_EXISTS_IMP >>
  metis_tac[TWO_EXP_BOUNDS]
QED

Theorem mk_minimum[local]:
  ∀s j. fIN j s ⇒ 2 ** j ≤ mk s
Proof
  Induct >> rw[fSUM_IMAGE_THM] >> simp[] >>
  first_x_assum drule >> simp[]
QED

Triviality mk_onto:
  ∀n. ∃s. mk s = n
Proof
  completeInduct_on `n` >>
  qspec_then `n` strip_assume_tac bound_exists >>
  qabbrev_tac `m = LEAST m. n < 2 EXP m` >>
  Cases_on `m = 0`
  >- (Q.UNABBREV_TAC ‘m’ >> fs[] >> `n = 0` by simp[] >> qexists_tac `fEMPTY` >>
      simp[fSUM_IMAGE_THM]) >>
  `m - 1 < m` by simp[] >>
  `2 ** (m - 1) ≤ n` by simp[] >>
  qabbrev_tac `M = 2 ** (m - 1)` >>
  `0 < M` by simp[Abbr`M`] >>
  `n - M < n` by simp[] >>
  `∃s0. mk s0 = n - M` by metis_tac[] >>
  qexists_tac `fINSERT (m - 1) s0` >>
  simp[fSUM_IMAGE_THM] >>
  Cases_on `fIN (m - 1) s0`
  >- (`M ≤ mk s0` by metis_tac[mk_minimum] >>
      `2 * M ≤ n` by simp[] >>
      `2 * M = 2 ** m` suffices_by simp[] >>
      simp[Abbr`M`]  >> fs[GSYM arithmeticTheory.EXP] >>
      `SUC (m - 1) = m` by simp[] >> lfs[]) >>
  simp[]
QED

Theorem split_sets[local]:
  s1 = fUNION (fINTER s1 s2) (fDIFF s1 s2)
Proof simp[EXTENSION] >> metis_tac[]
QED

Theorem DISJOINT_DIFF[local]:
  fINTER (fDIFF s1 s2) (fDIFF s2 s1) = fEMPTY
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem DIFF_NONEMPTY[local]:
  s1 ≠ s2 ⇔ fDIFF s1 s2 ≠ fEMPTY ∨ fDIFF s2 s1 ≠ fEMPTY
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem disjoint_inequal_has_maximum[local]:
  fINTER s1 s2 = fEMPTY ∧ s1 ≠ s2 ⇒
    (∃m. fIN m s1 ∧ (∀n. fIN n s2 ⇒ n < m)) ∨
    (∃m. fIN m s2 ∧ (∀n. fIN n s1 ⇒ n < m))
Proof
  Cases_on `s1 = fEMPTY` >- metis_tac[fset_cases, IN_INSERT, NOT_IN_EMPTY] >>
  Cases_on `s2 = fEMPTY` >> simp[]
  >- metis_tac[fset_cases, IN_INSERT, NOT_IN_EMPTY] >>
  qabbrev_tac `m1 = fMAX_SET s1` >>
  qabbrev_tac `m2 = fMAX_SET s2` >>
  strip_tac >>
  `fIN m1 s1 ∧ (∀a. fIN a s1 ⇒ a ≤ m1) ∧ fIN m2 s2 ∧ (∀b. fIN b s2 ⇒ b ≤ m2)`
    by metis_tac[fMAX_SET_fIN, fIN_fMAX_SET] >>
  Cases_on `m1 < m2`
  >- (disj2_tac >> qexists_tac `m2` >> simp[] >> rpt strip_tac >> res_tac >>
      simp[]) >>
  disj1_tac >> qexists_tac `m1` >> simp[] >> rpt strip_tac >>
  `m1 ≠ m2` by (strip_tac >> fs[EXTENSION] >> metis_tac[]) >>
  res_tac >> simp[]
QED

Theorem topdown_induct[local]:
  P fEMPTY ∧
  (∀e s0. P s0 ∧ ~fIN e s0 ∧ (∀n. fIN n s0 ⇒ n < e) ⇒ P (fINSERT e s0)) ⇒
  (∀s. P s)
Proof
  strip_tac >> gen_tac >> Induct_on ‘fCARD s’ >> simp[] >>
  rpt strip_tac >> `s ≠ fEMPTY` by (strip_tac >> fs[]) >>
  qabbrev_tac `M = fMAX_SET s` >>
  `fIN M s ∧ ∀n. fIN n s ⇒ n ≤ M` by metis_tac[fMAX_SET_fIN, fIN_fMAX_SET] >>
  `s = fINSERT M (fDELETE M s)` by (simp[EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `s0 = fDELETE M s` >>
  `~fIN M s0` by simp[Abbr`s0`] >>
  rename1 `SUC n = fCARD s` >>
  `fCARD s = SUC (fCARD s0)` by simp[] >>
  `n = fCARD s0` by simp[] >>
  `P s0` by metis_tac[] >>
  `∀n. fIN n s0 ⇒ n < M`
     by (fs[] >> metis_tac[DECIDE ``x ≤ y ∧ x ≠ y ⇒ x < y``]) >>
    metis_tac[]
QED

Theorem mk_upper_bound[local]:
  ∀s b. (∀n. fIN n s ⇒ n < b) ⇒ mk s < 2 ** b
Proof
  ho_match_mp_tac topdown_induct >>
  dsimp[fSUM_IMAGE_THM] >> rpt strip_tac >>
  rename1 `~fIN e s` >>
  `mk s < 2 ** e` by metis_tac[] >>
  rename1 `e < b` >>
  `∃d. b = SUC d + e` by metis_tac[arithmeticTheory.LESS_STRONG_ADD] >>
  simp[arithmeticTheory.EXP_ADD, arithmeticTheory.EXP] >>
  match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `2 * 2 ** e` >> simp[]
QED

Theorem mk_11[local]:
  mk s1 = mk s2 ⇔ s1 = s2
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `c = fINTER s1 s2` >>
  qabbrev_tac `t1 = fDIFF s1 s2` >>
  qabbrev_tac `t2 = fDIFF s2 s1` >>
  `s1 = fUNION c t1 ∧ s2 = fUNION c t2` by metis_tac[split_sets, fINTER_COMM] >>
  `fINTER c t1 = fEMPTY ∧ fINTER c t2 = fEMPTY`
    by (simp[Abbr`c`, Abbr`t1`, Abbr`t2`, EXTENSION] >> metis_tac[]) >>
  `mk s1 = mk c + mk t1 ∧ mk s2 = mk c + mk t2`
    by (rpt BasicProvers.VAR_EQ_TAC >>
        Q.UNDISCH_THEN `mk (fUNION c t1) = mk (fUNION c t2)` kall_tac >>
        simp[fSUM_IMAGE_UNION, fSUM_IMAGE_THM]) >>
  `mk t1 = mk t2` by simp[] >>
  `fINTER t1 t2 = fEMPTY` by (simp[EXTENSION, Abbr‘t1’, Abbr‘t2’] >> metis_tac[]) >>
  `t1 ≠ t2` by metis_tac[] >>
  `(∃m1. fIN m1 t1 ∧ (∀n. fIN n t2 ⇒ n < m1)) ∨
   (∃m2. fIN m2 t2 ∧ (∀n. fIN n t1 ⇒ n < m2))`
     by metis_tac[disjoint_inequal_has_maximum]
  >- (`mk t2 < 2 ** m1` by metis_tac[mk_upper_bound] >>
      `2 ** m1 ≤ mk t1` by metis_tac[mk_minimum] >> gvs[]) >>
  `mk t1 < 2 ** m2` by metis_tac[mk_upper_bound] >>
  `2 ** m2 ≤ mk t2` by metis_tac[mk_minimum] >> gvs[]
QED

Theorem mk_BIJ[local]: BIJ mk UNIV UNIV
Proof
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF, mk_11, mk_onto]
QED

val hfs = new_type_definition(
  "hfs",
  prove(``?x:num. (\x. T) x``, simp[]))

val HFS_TYBIJ =
    define_new_type_bijections { ABS = "mkHFS", REP = "destHFS",
                                 name = "HFS_TYBIJ", tyax = hfs}
                               |> SIMP_RULE (srw_ss()) []

Theorem mkHFS_11[simp]: mkHFS n1 = mkHFS n2 ⇔ n1 = n2
Proof metis_tac[HFS_TYBIJ]
QED

Theorem destHFS_11[simp]: destHFS h1 = destHFS h2 ⇔ h1 = h2
Proof metis_tac[HFS_TYBIJ]
QED

Definition toSet_def:
  toSet hfs = fIMAGE mkHFS (LINV mk UNIV (destHFS hfs))
End

Theorem LINV_mk_11[simp]:
  LINV mk UNIV x = LINV mk UNIV y ⇔ x = y
Proof
  `BIJ (LINV mk UNIV) univ(:num) UNIV`
    by simp[BIJ_LINV_BIJ, mk_BIJ] >>
  fs[BIJ_DEF, INJ_DEF, EQ_IMP_THM]
QED

Theorem toSet_11[simp]: toSet h1 = toSet h2 ⇔ h1 = h2
Proof
  simp[toSet_def, fIMAGE_11]
QED

Definition fromSet_def:
  fromSet s = mkHFS (mk (fIMAGE destHFS s))
End

Theorem fromSet_toSet[simp]:
  fromSet (toSet h) = h
Proof
  simp[fromSet_def, toSet_def] >> simp[GSYM fIMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF, HFS_TYBIJ] >>
  strip_assume_tac (MATCH_MP BIJ_LINV_INV mk_BIJ) >> fs[HFS_TYBIJ]
QED

Triviality LINV_mk:
  ∀s. LINV mk UNIV (mk s) = s
Proof
  rpt strip_tac >> irule LINV_DEF >> simp[INJ_DEF, mk_11] >>
  qexists_tac `UNIV` >> simp[]
QED

Theorem toSet_fromSet[simp]:
  ∀hs. toSet (fromSet hs) = hs
Proof
  csimp[toSet_def, fromSet_def, HFS_TYBIJ, LINV_mk, GSYM fIMAGE_COMPOSE] >>
  simp[combinTheory.o_DEF, HFS_TYBIJ]
QED

Theorem fromSet_11[simp]:
  fromSet s1 = fromSet s2 ⇔ s1 = s2
Proof
  metis_tac[toSet_fromSet]
QED

Definition hINSERT_def: hINSERT h1 h2 = fromSet (fINSERT h1 $ toSet h2)
End

Definition hEMPTY_def: hEMPTY = fromSet fEMPTY
End

Theorem hf_CASES:
  ∀h. h = hEMPTY ∨ ∃h1 h2. h = hINSERT h1 h2
Proof
  gen_tac >>
  simp_tac bool_ss [GSYM toSet_11, hEMPTY_def, hINSERT_def, toSet_fromSet] >>
  `toSet h = fEMPTY ∨ ∃e s. toSet h = fINSERT e s ∧ ~fIN e s`
                            by (Cases_on ‘toSet h’ >> metis_tac[]) >>
  simp[] >> qexistsl [`e`, `fromSet s`] >> simp[]
QED

Theorem hINSERT_NEQ_hEMPTY[simp]: hINSERT h hs ≠ hEMPTY
Proof
  simp[hINSERT_def, hEMPTY_def]
QED

Theorem hINSERT_hINSERT[simp]:
  hINSERT x (hINSERT x s) = hINSERT x s
Proof
  simp[hINSERT_def, toSet_fromSet]
QED

Theorem hINSERT_COMMUTES:
  hINSERT x (hINSERT y s) = hINSERT y (hINSERT x s)
Proof
  simp[hINSERT_def, EXTENSION] >> metis_tac[]
QED

Definition hIN_def:
  hIN h hs ⇔ (hINSERT h hs = hs)
End

Theorem hIN_toSet:
  hIN h hs ⇔ fIN h $ toSet hs
Proof
  simp[hIN_def, hINSERT_def] >> eq_tac
  >- (disch_then (mp_tac o Q.AP_TERM `toSet`) >>
      simp_tac bool_ss [toSet_fromSet] >>
      simp[fABSORPTION]) >>
  simp[fABSORPTION]
QED

Theorem hIN_hEMPTY[simp]: ¬(hIN h hEMPTY)
Proof simp[hIN_def]
QED

Theorem hIN_hINSERT[simp]:
  hIN h1 (hINSERT h2 hs) ⇔ h1 = h2 ∨ hIN h1 hs
Proof
  simp[hIN_toSet, hINSERT_def]
QED

Theorem EXP_LT[local,simp]:
  ∀n. n < 2 ** n
Proof
  Induct >> simp[arithmeticTheory.EXP]
QED

Theorem hIN_reduces[local]:
  hIN h0 h ⇒ destHFS h0 < destHFS h
Proof
  simp[hIN_toSet, toSet_def, PULL_EXISTS, HFS_TYBIJ] >> rpt strip_tac >>
  drule mk_minimum >> simp[MATCH_MP BIJ_LINV_INV mk_BIJ] >> strip_tac >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >> first_assum $ irule_at Any >>
  simp[]
QED

Theorem hf_induction:
  ∀P. (∀h. (∀h0. hIN h0 h ⇒ P h0) ⇒ P h) ⇒ (∀h. P h)
Proof
  rpt strip_tac >>
  completeInduct_on ‘destHFS h’ >> gs[PULL_FORALL] >> rw[] >>
  last_x_assum irule >> rw[] >> last_x_assum irule >>
  simp[hIN_reduces]
QED

val _ = export_theory();
