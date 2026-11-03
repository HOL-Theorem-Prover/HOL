(* Define the type of hereditarily finite sets.

   Single (recursive) constructor is

     fromSet : hfs fset -> hfs

   where the fset type operator is that of finite sets.

   Because there is just one constructor, there is a total inverse to
   fromSet, called tofSet

     tofSet : hfs -> hfs set

   where we have

     fromSet (tofSet h) = h

   Future work:
   - define other operations such as intersection, union and cardinality

   The type can be defined via a cute bijection (due to Ackermann according to
   Wikipedia) with the natural numbers.

   Inspired to do this by Larry Paulson's talk about using h.f. sets
   as part of a mechanisation of automata theory at CADE 2015. There (in
   Isabelle/HOL), the type definition mechanism can create the type
   directly so the Ackermann bijection is not required. HOL4 has the same
   BNF technology too, but I also define the Ackermann function, which
   ends up having type :hfs -> num, via the mk below, which takes a finite
   set of numbers and maps that set to a single number.
*)
Theory hfs
Ancestors
  pred_set finite_set


Datatype:
  hfs = fromSet (hfs fset)
End

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
     WhileTheory.LEAST_EXISTS_IMP >>
  metis_tac[TWO_EXP_BOUNDS]
QED

Theorem mk_minimum[local]:
  ∀s j. fIN j s ⇒ 2 ** j ≤ mk s
Proof
  Induct >> rw[fSUM_IMAGE_THM] >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem mk_onto[local]:
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

Definition ackermann_def[simp]:
  ackermann (fromSet s : hfs) = mk (fIMAGE ackermann s) : num
End

Definition tofSet_def[simp]:
  tofSet (fromSet s) = s
End

Theorem tofSet_11[simp]: tofSet h1 = tofSet h2 ⇔ h1 = h2
Proof
  Cases_on ‘h1’ >> Cases_on ‘h2’ >> simp[]
QED

Theorem fromSet_tofSet[simp]:
  fromSet (tofSet h) = h
Proof
  Cases_on ‘h’ >> simp[]
QED

Theorem LINV_mk[local]:
  ∀s. LINV mk UNIV (mk s) = s
Proof
  rpt strip_tac >> irule LINV_DEF >> simp[INJ_DEF, mk_11] >>
  qexists_tac `UNIV` >> simp[]
QED

Definition hINSERT_def: hINSERT h1 h2 = fromSet (fINSERT h1 $ tofSet h2)
End

Definition hEMPTY_def: hEMPTY = fromSet fEMPTY
End

Theorem hf_CASES:
  ∀h. h = hEMPTY ∨ ∃h1 h2. h = hINSERT h1 h2
Proof
  gen_tac >>
  simp_tac bool_ss [GSYM toSet_11, hEMPTY_def, hINSERT_def, toSet_fromSet] >>
  Cases_on ‘h’ >> simp[] >> qspec_then ‘f’ strip_assume_tac fset_cases >>
  simp[] >> rename [‘f = fINSERT e s’] >>
  qexistsl [‘e’, ‘fromSet s’] >> simp[]
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

Theorem hIN_tofSet:
  hIN h hs ⇔ fIN h $ tofSet hs
Proof
  Cases_on ‘hs’ >> simp[hIN_def, hINSERT_def] >> metis_tac[fABSORPTION]
QED

Theorem hIN_hEMPTY[simp]: ¬(hIN h hEMPTY)
Proof simp[hIN_def]
QED

Theorem hIN_hINSERT[simp]:
  hIN h1 (hINSERT h2 hs) ⇔ h1 = h2 ∨ hIN h1 hs
Proof
  simp[hIN_tofSet, hINSERT_def]
QED

Theorem EXP_LT[local,simp]:
  ∀n. n < 2 ** n
Proof
  Induct >> simp[arithmeticTheory.EXP]
QED

Theorem ackermann_11[simp]:
  ∀s1 s2. ackermann s1 = ackermann s2 ⇔ s1 = s2
Proof
  simp[EQ_IMP_THM] >> Induct >> Cases >> simp[ackermann_def, mk_11] >>
  contr >> qpat_x_assum ‘fIMAGE _ _ = fIMAGE _ _’ mp_tac >>
  simp[] >> rename [‘f1 ≠ f2 (* a *)’] >>
  ‘toSet f1 ≠ toSet f2’ by simp[finite_setTheory.toSet_11] >>
  ‘(∃h. h ∈ toSet f1 ∧ h ∉ toSet f2) ∨ (∃h. h ∈ toSet f2 ∧ h ∉ toSet f1)’
    by ASM_SET_TAC[] >>
  simp[finite_setTheory.EXTENSION] >> metis_tac[fIN_IN]
QED

Theorem fSUM_IMAGE_fIMAGE:
  (∀x y. g x = g y ⇔ x = y) ⇒
  ∀s. fSUM_IMAGE f (fIMAGE g s) = fSUM_IMAGE (f o g) s
Proof
  strip_tac >> Induct_on ‘s’ >> simp[]
QED

Theorem fIN_LT_fSUM_IMAGE:
 (∀x. x < f x) ⇒ ∀a A. fIN a A ⇒ a < fSUM_IMAGE f A
Proof
  strip_tac >> Induct_on ‘A’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >~
  [‘e < f e + _’]
  >- (‘e < f e’ by simp[] >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem hIN_reduces[local]:
  ∀h0 h. hIN h0 h ⇒ ackermann h0 < ackermann h
Proof
  Induct_on ‘h’ >> simp[hIN_tofSet] >> rw[] >>
  irule fIN_LT_fSUM_IMAGE >> simp[]
QED

(* alternative induction principle using the hIN predicate rather than
   the constructor and the finite_set$toSet function.
*)
Theorem hf_induction:
  ∀P. (∀h. (∀h0. hIN h0 h ⇒ P h0) ⇒ P h) ⇒ (∀h. P h)
Proof
  gen_tac >> strip_tac >> Induct_on ‘h’ >>
  last_x_assum irule >> simp[hIN_tofSet, fIN_IN]
QED
