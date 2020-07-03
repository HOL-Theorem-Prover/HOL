open HolKernel Parse boolLib bossLib;

open numpairTheory primrecfnsTheory nlistTheory arithmeticTheory listTheory
     recursivefnsTheory

val _ = new_theory "unary_recfns";

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition pr1_pr_def:
  pr1_pr b s n =
   if nfst n = 0 then b (nsnd n)
   else
     s ((nfst n - 1) ⊗ pr1_pr b s ((nfst n - 1) ⊗ nsnd n) ⊗ nsnd n)
Termination
  WF_REL_TAC ‘measure (λ(b,s,n). nfst n)’ >> simp[]
End

Theorem pr1_pr_thm[simp]:
  pr1_pr b s (0 ⊗ v) = b v ∧
  pr1_pr b s (SUC n ⊗ v) = s (n ⊗ pr1_pr b s (n ⊗ v) ⊗ v) ∧
  pr1_pr b s ((n + 1) ⊗ v) = s (n ⊗ pr1_pr b s (n ⊗ v) ⊗ v)
Proof
  csimp[GSYM ADD1] >> conj_tac >>
  simp[Once pr1_pr_def, SimpLHS]
QED


Inductive primrec1:
  primrec1 (K 0) ∧
  primrec1 SUC ∧
  primrec1 nfst ∧
  primrec1 nsnd ∧
  (∀f g. primrec1 f ∧ primrec1 g ⇒ primrec1 (λn. f n ⊗ g n)) ∧
  (∀f g. primrec1 f ∧ primrec1 g ⇒ primrec1 (f o g)) ∧
  (∀b s. primrec1 b ∧ primrec1 s ⇒ primrec1 (pr1_pr b s))
End

Theorem primrec1_I[simp]:
  primrec1 I ∧ primrec1 (λx. x)
Proof
  ‘I = (λx:num. x)’ by simp[FUN_EQ_THM] >> simp[] >>
  ‘primrec1 (λn. nfst n ⊗ nsnd n)’ by metis_tac[primrec1_rules] >>
  fs[]
QED

Theorem primrec1_add:
  primrec1 (λn. nfst n + nsnd n)
Proof
  ‘primrec1 (SUC o nfst o nfst)’ by metis_tac[primrec1_rules] >>
  qabbrev_tac ‘ADD = pr1_pr I (SUC o nfst o nsnd)’ >>
  ‘primrec1 ADD’ by metis_tac[primrec1_rules, primrec1_I] >>
  ‘ADD = (λn. nfst n + nsnd n)’ suffices_by (rw[] >> rw[]) >>
  simp[FUN_EQ_THM, Abbr‘ADD’] >> gen_tac >>
  ‘∃x y. n = x ⊗ y’ by metis_tac[npair_cases] >> rw[] >> Induct_on ‘x’ >>
  simp[]
QED

Theorem primrec_Cn = List.nth (CONJUNCTS primrec_rules, 3)

Theorem primrec1_primrec:
  ∀f. primrec1 f ⇒ ∃g. primrec g 1 ∧ ∀n. g [n] = f n
Proof
  Induct_on ‘primrec1’ >> rw[]
  >- (qexists_tac ‘zerof’ >> simp[])
  >- (qexists_tac ‘succ’ >> simp[primrec_rules])
  >- (qexists_tac ‘pr1 nfst’ >> simp[primrec_nfst])
  >- (qexists_tac ‘pr1 nsnd’ >> simp[primrec_nsnd])
  >- (rename [‘f1 _ ⊗ f2 _’, ‘g1 [_] = f1 _’, ‘g2 [_] = f2 _’] >>
      qexists_tac ‘Cn (pr2 npair) [g1; g2]’ >> simp[primrec_rules])
  >- (rename [‘f1 (f2 _)’, ‘g1 [_] = f1 _’, ‘g2 [_] = f2 _’] >>
      qexists_tac ‘Cn g1 [g2]’>> simp[primrec_rules]) >>
  rename [‘pr1_pr b1 s1’, ‘b [_] = b1 _’, ‘s [_] = s1 _’] >>
  qexists_tac
    ‘Cn (Pr b (Cn s [Cn (pr2 npair) [proj 0; Cn (pr2 npair) [proj 1; proj 2]]]))
        [pr1 nfst; pr1 nsnd]’ >>
  conj_tac
  >- (irule primrec_Cn >> simp[] >> irule alt_Pr_rule >> simp[primrec_rules]) >>
  gen_tac >>
  ‘∃x y. n = x ⊗ y’ by metis_tac[npair_cases] >> rw[] >> Induct_on ‘x’ >>
  simp[]
QED

Definition unfold_def[simp]:
  unfold 0 m = [] ∧
  unfold (SUC n) m = if n = 0 then [m]
                     else nfst m :: unfold n (nsnd m)
End

Theorem unfold1[simp]:
  unfold 1 n = [n]
Proof
  simp_tac bool_ss [ONE, unfold_def]
QED

Theorem unfold_LENGTH[simp]:
  ∀m n. LENGTH (unfold m n) = m
Proof
  Induct_on ‘m’ >> rw[]
QED

Theorem unfold_EQ_NIL[simp]:
  unfold a n = [] ⇔ a = 0
Proof
  Cases_on ‘a’ >> rw[]
QED

Definition fold_def[simp]:
  fold [] = 0 ∧
  fold [x] = x ∧
  fold (x::xs) = x ⊗ fold xs
End

Theorem fold_unfold[simp]:
  ∀a n. 0 < a ⇒ fold (unfold a n) = n
Proof
  Induct >> rw[] >>
  Cases_on ‘unfold a (nsnd n)’ >> fs[] >>
  pop_assum (assume_tac o SYM) >> simp[]
QED

Theorem unfold_fold[simp]:
  ∀l. unfold (LENGTH l) (fold l) = l
Proof
  Induct_on ‘l’ >> simp[] >> rw[] >> Cases_on ‘l’ >> fs[]
QED

Theorem unfold_fold_alt:
  n = LENGTH l ⇒ unfold n (fold l) = l
Proof
  simp[]
QED

Triviality FUNPOW_o:
  FUNPOW f 0 = I ∧
  FUNPOW f (SUC n) = f o FUNPOW f n
Proof
  simp[FUN_EQ_THM, FUNPOW_SUC]
QED

Definition foldfs_def[simp]:
  foldfs [f] n = f n ∧
  foldfs (f::fs) n = f n ⊗ foldfs fs n
End

Theorem foldfs_as_function:
  foldfs [f] = f ∧
  foldfs (f::g::fs) = λn. f n ⊗ foldfs (g::fs) n
Proof
  simp[FUN_EQ_THM]
QED

Theorem primrec1_foldfs:
  fs ≠ [] ∧ (∀f. MEM f fs ⇒ primrec1 f) ⇒ primrec1 (foldfs fs)
Proof
  Induct_on ‘fs’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> qx_gen_tac ‘f’ >>
  Cases_on ‘fs’ >> fs[foldfs_as_function, DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[primrec1_rules]
QED

Theorem unfold_foldfs:
  ∀a fs n. 0 < a ∧ LENGTH fs = a ⇒ unfold a (foldfs fs n) = MAP (λf. f n) fs
Proof
  Induct_on ‘fs’ >> simp[] >> fs[] >> rw[]
  >- (Cases_on ‘fs’ >> fs[]) >>
  Cases_on ‘fs’ >> fs[]
QED

Theorem MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

Theorem primrec_primrec1:
  ∀f a. primrec f a ⇒ ∃g. primrec1 g ∧ ∀n. g n = f (unfold a n)
Proof
  Induct_on ‘primrec’ >> rw[]
  >- (qexists_tac ‘K 0’ >> simp[primrec1_rules])
  >- (qexists_tac ‘SUC’ >> simp[primrec1_rules])
  >- (rename [‘proj i (unfold a _)’] >>
      qexists_tac ‘(if i + 1 = a then I else nfst) o FUNPOW nsnd i’ >> conj_tac
      >- (pop_assum (K ALL_TAC) >>
          ‘primrec1 (FUNPOW nsnd i)’
            suffices_by metis_tac[primrec1_rules, primrec1_I] >>
          Induct_on ‘i’ >> simp[FUNPOW_o, primrec1_rules]) >>
      pop_assum mp_tac >> qid_spec_tac ‘a’ >>
      ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
      Induct_on ‘i’ >> simp[]
      >- (rw[] >> simp[] >> Cases_on ‘a’ >> simp[]) >>
      rw[]
      >- (simp_tac bool_ss [GSYM ADD1, Once unfold_def] >>
          simp[Excl "unfold_def"] >> simp[FUNPOW]) >>
      ‘∃a0. a = SUC a0’ by (Cases_on ‘a’ >> fs[]) >> fs[FUNPOW])
  >- (fs[listTheory.EVERY_MEM, PULL_EXISTS, GSYM RIGHT_EXISTS_IMP_THM] >>
      fs[SKOLEM_THM] >> rename [‘primrec1 (mk1 _)’] >>
      rename [‘f1 _ = f (unfold (LENGTH gs) _)’] >>
      qexists_tac ‘f1 o foldfs (MAP mk1 gs)’ >>
      ‘gs ≠ []’ by (strip_tac >> fs[] >> drule primrec_nzero >> simp[]) >>
      conj_tac
      >- simp[primrec1_foldfs, primrec1_rules, MEM_MAP, PULL_EXISTS] >>
      ‘0 < LENGTH gs’ by (CCONTR_TAC >> fs[]) >>
      simp[Cn_def, unfold_foldfs, MAP_MAP_o, combinTheory.o_ABS_L,
           Cong MAP_CONG']) >>
  rename [‘b1 _ = b (unfold a _)’, ‘s1 _ = s (unfold (a + 2) _)’] >>
  ‘0 < a’ by metis_tac[primrec_nzero] >>
  qexists_tac ‘pr1_pr b1 s1’ >> simp[primrec1_rules] >>
  simp[GSYM ADD1] >>
  qx_gen_tac ‘N’ >>
  ‘∃x y. N = x ⊗ y’ by metis_tac[npair_cases] >> rw[] >>
  Induct_on ‘x’ >> simp[] >> ‘∀n. n + 2 = SUC (SUC n)’ by simp[] >> simp[]
QED

Theorem primrec_primrec1_fold:
  ∀f a. primrec f a ⇒ ∃g. primrec1 g ∧ ∀l. LENGTH l = a ⇒ f l = g (fold l)
Proof
  rw[] >> drule_then (qx_choose_then ‘G’ strip_assume_tac) primrec_primrec1 >>
  qexists_tac ‘G’ >> rw[] >> rw[unfold_fold]
QED

Definition recpair_def:
  recpair f g (n:num) = do i <- f n; j <- g n; return (i ⊗ j); od
End

Definition recCn1_def:
  recCn1 (f:num->num option) g (n:num) = do x <- g n ; f x; od
End

Definition recPr1_def:
  recPr1 b s n = if nfst n = 0 then b (nsnd n)
                 else do
                        r <- recPr1 b s ((nfst n - 1) ⊗ nsnd n) ;
                        s ((nfst n - 1) ⊗ r ⊗ nsnd n)
                      od
Termination
  WF_REL_TAC ‘measure (λ(b,s,n). nfst n)’ >> simp[]
End

Theorem recPr1_thm[simp]:
  recPr1 b s (0 ⊗ m) = b m ∧
  recPr1 b s (SUC n ⊗ m) = do r <- recPr1 b s (n ⊗ m) ;
                              s (n ⊗ r ⊗ m) ;
                           od
Proof
  conj_tac >> simp[Once recPr1_def, SimpLHS]
QED

Definition recMin1_def:
  recMin1 f m =
    OLEAST n. f (n ⊗ m) = SOME 0 ∧ ∀i. i < n ⇒ ∃r. f (i ⊗ m) = SOME r
End

Inductive recfn1:
  recfn1 (SOME o K 0) ∧
  recfn1 (SOME o SUC) ∧
  recfn1 (SOME o nfst) ∧
  recfn1 (SOME o nsnd) ∧
  (∀f g. recfn1 f ∧ recfn1 g ⇒ recfn1 (recpair f g)) ∧
  (∀f g. recfn1 f ∧ recfn1 g ⇒ recfn1 (recCn1 f g)) ∧
  (∀b s. recfn1 b ∧ recfn1 s ⇒ recfn1 (recPr1 b s)) ∧
  (∀f. recfn1 f ⇒ recfn1 (recMin1 f))
End

Theorem primrec1_recfn1:
  ∀f. primrec1 f ⇒ recfn1 (SOME o f)
Proof
  Induct_on ‘primrec1’ >> rw[recfn1_rules]
  >- (rename [‘f1 _ ⊗ f2 _’] >>
      ‘recfn1 (recpair (SOME o f1)(SOME o f2))’ by simp[recfn1_rules] >>
      pop_assum mp_tac >>
      qmatch_abbrev_tac ‘recfn1 F1 ⇒ recfn1 F2’ >>
      ‘F1 = F2’ suffices_by simp[] >>
      simp[recpair_def, Abbr‘F1’, Abbr‘F2’, FUN_EQ_THM])
  >- (rename [‘SOME o f o g’] >>
      ‘recCn1 (SOME o f) (SOME o g) = SOME o f o g’
        suffices_by metis_tac[recfn1_rules] >>
      simp[FUN_EQ_THM, recCn1_def])
  >- (rename [‘SOME o pr1_pr b s’] >>
      ‘recPr1 (SOME o b) (SOME o s) = SOME o pr1_pr b s’
        suffices_by metis_tac[recfn1_rules] >>
      simp[FUN_EQ_THM] >> qx_gen_tac ‘N’ >>
      ‘∃x y. N = x ⊗ y’ by metis_tac[npair_cases] >> rw[] >>
      Induct_on ‘x’ >> simp[])
QED

Theorem recfn1_recfn:
  ∀f. recfn1 f ⇒ recfn (rec1 f) 1
Proof
  Induct_on ‘recfn1’ >> rw[] >> irule recfn_rec1
  >- (qexists_tac ‘K (SOME 0)’ >> simp[])
  >- (qexists_tac ‘SOME o succ’ >> simp[recfn_rules])
  >- (qexists_tac ‘SOME o pr1 nfst’ >> simp[] >>
      irule primrec_recfn >> simp[])
  >- (qexists_tac ‘SOME o pr1 nsnd’ >> simp[] >>
      irule primrec_recfn >> simp[])
  >- (rename [‘recpair f1 f2’] >>
      qexists_tac ‘recCn (SOME o pr2 npair) [rec1 f1; rec1 f2]’ >>
      simp[recCn_def, recpair_def, rec1_def] >> conj_tac
      >- (irule recfnCn >> simp[] >> irule primrec_recfn >> simp[]) >>
      qx_gen_tac ‘N’ >> Cases_on ‘f1 N’ >> simp[] >> Cases_on ‘f2 N’ >> simp[])
  >- (rename [‘recCn1 f g _’] >>
      qexists_tac ‘recCn (rec1 f) [rec1 g]’ >> simp[recfn_rules] >>
      simp[recCn_def, recCn1_def, rec1_def] >> qx_gen_tac ‘N’ >>
      Cases_on ‘g N’ >> simp[])
  >- (rename [‘recPr1 b s _’] >>
      qexists_tac
        ‘recCn (recPr (rec1 b)
                      (recCn (rec1 s) [
                          SOME o Cn (pr2 npair) [
                            proj 0;
                            Cn (pr2 npair) [proj 1; proj 2]
                          ]
                       ]))
               [SOME o pr1 nfst; SOME o pr1 nsnd]’ >>
      conj_tac
      >- (irule recfnCn >> simp[primrec_recfn] >>
          irule recfnPr >> simp[] >> irule recfnCn >> simp[] >>
          irule primrec_recfn >> irule primrec_Cn >>
          simp[primrec_rules]) >>
      qx_gen_tac ‘N’ >> ‘∃x y. N = x ⊗ y’ by metis_tac[npair_cases] >>
      rw[recCn_def] >> Induct_on ‘x’ >> simp[Once recPr_def, rec1_def] >>
      Cases_on ‘recPr1 b s (x ⊗ y)’ >> simp[recCn_def, rec1_def]) >>
  rename [‘recMin1 f’] >>
  qexists_tac
    ‘minimise (recCn (rec1 f) [SOME o Cn (pr2 $*,) [proj 0; proj 1]])’ >>
  conj_tac
  >- (irule (last (CONJUNCTS recfn_rules)) >> simp[] >> irule recfnCn >>
      simp[] >> irule primrec_recfn >> simp[primrec_rules]) >>
  simp[minimise_def, recMin1_def, recCn_def, rec1_def] >> qx_gen_tac ‘N’ >>
  rw[]
  >- (simp[whileTheory.OLEAST_EQ_SOME] >> SELECT_ELIM_TAC >> conj_tac
      >- metis_tac[] >>
      simp[] >> rw[] >- metis_tac[] >>
      first_x_assum drule >> simp[PULL_EXISTS]) >>
  fs[] >> rename [‘f (A ⊗ B) = SOME 0’] >>
  Cases_on ‘f (A ⊗ B) = SOME 0’ >> simp[] >>
  qspec_then ‘λn. f (n ⊗ B) = SOME 0’ mp_tac WOP >> simp[] >> impl_tac
  >- metis_tac[] >>
  disch_then (qx_choose_then ‘A0’ strip_assume_tac) >>
  ‘A0 ≤ A’ by metis_tac[DECIDE “¬(x < y) ⇔ y ≤ x”] >>
  ‘∃i0. i0 < A0 ∧ ∀m. f (i0 ⊗ B) = SOME m ⇒ m = 0’ by metis_tac[] >>
  metis_tac[DECIDE “x < y ∧ y ≤ z ⇒ x < z”]
QED

(* basically, expanding def'n of rec1 *)
Theorem recfn1_recfn_alt:
  recfn1 f ⇒ ∃g. recfn g 1 ∧ ∀n. g [n] = f n
Proof
  strip_tac >> drule_then strip_assume_tac recfn1_recfn >>
  qexists_tac ‘rec1 f’ >> simp[rec1_def]
QED

Definition ofoldfs_def:
  ofoldfs [f] (n:num) = f n ∧
  ofoldfs (f::fs) n = do r1 <- f n ;
                         rs <- ofoldfs fs n ;
                         return (r1 ⊗ rs) ;
                      od
End

Theorem ofoldfs_thm[simp]:
  ofoldfs [f] = f ∧
  ofoldfs (f1::f2::fs) = recpair f1 (ofoldfs (f2::fs))
Proof
  simp[FUN_EQ_THM, recpair_def, ofoldfs_def]
QED

Theorem ofoldfs_EQ_NONE[simp]:
  fs ≠ [] ⇒
  (ofoldfs fs n = NONE ⇔ ∃f. MEM f fs ∧ f n = NONE)
Proof
  Induct_on ‘fs’ >> simp[] >> Cases_on ‘fs’ >>
  simp[recpair_def, PULL_EXISTS] >>
  metis_tac[TypeBase.distinct_of “:α option”, TypeBase.nchotomy_of “:α option”]
QED


Theorem recfn1_ofoldfs:
  fs ≠ [] ∧ (∀f. MEM f fs ⇒ recfn1 f) ⇒ recfn1 (ofoldfs fs)
Proof
  Induct_on ‘fs’ >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  qx_gen_tac ‘f’ >> Cases_on‘fs’ >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, recfn1_rules]
QED

Theorem ofoldfs_EQ_SOME:
  fs ≠ [] ⇒
  ∀l. ofoldfs fs n = SOME l ⇒ l = fold (MAP (λf. THE (f n)) fs)
Proof
  Induct_on ‘fs’ >> simp[] >> Cases_on ‘fs’ >> fs[] >>
  simp[recpair_def, PULL_EXISTS]
QED

Theorem recfn_recfn1:
  ∀f a. recfn f a ⇒ ∃g. recfn1 g ∧ ∀n. g n = f (unfold a n)
Proof
  Induct_on ‘recfn’ >> rw[]
  >- (qexists_tac ‘SOME o K 0’ >> simp[recfn1_rules])
  >- (qexists_tac ‘SOME o SUC’ >> simp[recfn1_rules])
  >- (‘primrec (proj i) a’ by simp[primrec_rules] >>
      drule_then (qx_choose_then ‘G’ strip_assume_tac) primrec_primrec1 >>
      qexists_tac ‘SOME o G’ >> simp[] >> simp[primrec1_recfn1])
  >- (fs[EVERY_MEM, GSYM RIGHT_EXISTS_IMP_THM, PULL_EXISTS, SKOLEM_THM] >>
      rename [‘mk1 _ _ = _ (unfold _ _)’] >>
      rename [‘f1 _ = f (unfold (LENGTH gs) _)’] >>
      qexists_tac ‘recCn1 f1 (ofoldfs (MAP mk1 gs))’ >>
      ‘gs ≠ []’ by (strip_tac >> fs[] >> drule recfn_nzero >> simp[]) >>
      conj_tac
      >- simp[recfn1_ofoldfs, recfn1_rules, MEM_MAP, PULL_EXISTS] >>
      ‘0 < LENGTH gs’ by (CCONTR_TAC >> fs[]) >>
      simp[recCn_def, MAP_MAP_o, recCn1_def, EVERY_MEM, MEM_MAP,
           combinTheory.o_ABS_R] >> qx_gen_tac ‘N’ >>
      Cases_on‘ofoldfs (MAP mk1 gs) N’ >> simp[]
      >- (rfs[MEM_MAP] >> rw[] >> qpat_x_assum ‘mk1 _ N = NONE’ mp_tac >>
          simp[] >> metis_tac[]) >>
      ‘∀g. NONE ≠ g (unfold a N) ∨ ¬MEM g gs’
         by (CCONTR_TAC >> fs[] >> rename [‘MEM G gs’] >>
             ‘NONE = mk1 G N’ by metis_tac[] >>
             metis_tac[MEM_MAP, ofoldfs_EQ_NONE, MAP_EQ_NIL,
                       TypeBase.distinct_of “:α option”]) >>
      simp[] >>
      ‘MAP mk1 gs ≠ []’ by simp[] >>
      drule_all ofoldfs_EQ_SOME >>
      rw[MAP_MAP_o, combinTheory.o_ABS_L, unfold_fold_alt] >>
      simp[Cong MAP_CONG'] >> fs[] >> metis_tac[])
  >- (rename [‘b1 _ = b (unfold (a-1) _)’, ‘s1 _ = s (unfold (a + 1) _)’] >>
      ‘0 < a-1’ by metis_tac[recfn_nzero] >>
      qexists_tac ‘recPr1 b1 s1’ >> simp[recfn1_rules] >>
      qx_gen_tac ‘N’ >>
      ‘∃x y. N = x ⊗ y’ by metis_tac[npair_cases] >> rw[] >>
      Induct_on ‘x’ >> simp[]
      >- (‘∃a0. a = SUC a0’ by (Cases_on ‘a’ >> fs[]) >>
          simp[unfold_def, Once recPr_def]) >>
      ‘∃a0. a = SUC a0’ by (Cases_on ‘a’ >> fs[]) >> simp[unfold_def] >>
      simp[SimpRHS, Once recPr_def] >> simp[GSYM ADD1] >>
      Cases_on‘recPr b s (x::unfold a0 y)’ >> simp[])
  >- (rename [‘f1 _ = f (unfold _ _)’] >>
      qexists_tac ‘recMin1 f1’ >> simp[recfn1_rules] >>
      simp[recMin1_def, minimise_def, GSYM ADD1] >> qx_gen_tac ‘N’ >>
      rw[] >> fs[]
      >- (simp[whileTheory.OLEAST_EQ_SOME] >> SELECT_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          rw[] >- metis_tac[] >>
          first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
      rename [‘f (n::unfold a N) = SOME 0’] >>
      Cases_on ‘f (n::unfold a N) = SOME 0’ >> simp[] >>
      qspec_then ‘λi. f (i::unfold a N) = SOME 0’ mp_tac WOP >>
      impl_tac >- metis_tac[] >> simp[] >>
      disch_then (qx_choose_then ‘n0’ strip_assume_tac) >>
      ‘n0 ≤ n’ by metis_tac[DECIDE “¬(x < y) ⇔ y ≤ x”] >>
      ‘∃i. i < n0 ∧ ∀m. f (i :: unfold a N) = SOME m ⇒ m = 0’ by metis_tac[] >>
      qexists_tac ‘i’ >> simp[] >> metis_tac[])
QED

Theorem recfn_recfn1_alt:
  recfn f a ⇒ ∃g. recfn1 g ∧ ∀l. LENGTH l = a ⇒ f l = g (fold l)
Proof
  metis_tac[unfold_fold, recfn_recfn1]
QED

val _ = export_theory();
