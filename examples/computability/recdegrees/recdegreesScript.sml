open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open prtermTheory;
open nlistTheory;

open recfunsTheory;
open recsetsTheory;

open reductionEval;
open churchDBTheory;

val _ = new_theory "recdegrees";

val _ = Datatype`form = BASE num num | EXISTS num form | ALL num form`

Definition MKEA_0[simp]:
 (MKEA0 0 m R = BASE R (m+1)) ∧
 (MKEA0 (SUC n) m R = EXISTS (SUC n) (MKAE0 n m R)) ∧
 (MKAE0 0 m R = BASE R (m+1)) ∧
 (MKAE0 (SUC n) m R = ALL (SUC n) (MKEA0 n m R))
End

Definition MKEA[simp]:
  MKEA n R = MKEA0 n n R
End

Definition MKAE[simp]:
  MKAE n R = MKAE0 n n R
End

Definition interpret[simp]:
  (interpret σ (BASE Ri n) <=> (Phi Ri (nlist_of (MAP σ (GENLIST I (n)))) = SOME 1)) ∧
  (interpret σ (EXISTS v f) <=> ∃n. interpret σ⦇v↦n⦈ f) ∧
  (interpret σ (ALL v f) <=> ∀n. interpret σ⦇v↦n⦈ f)
End

SIMP_CONV(srw_ss())[theorem "MKEA_0_compute",combinTheory.APPLY_UPDATE_THM] ``interpret I⦇0 ↦ x⦈ (MKEA 1 r)``;

Definition rec_sigma:
  rec_sigma n = {
    A | ∃Ri. (∀m. (Phi Ri m = SOME 0) ∨ (Phi Ri m = SOME 1)) ∧ 
             ∀x. x∈A <=> interpret I⦇0↦x⦈ (MKEA n Ri)
  }
End

Theorem recfn_nhd:
  recfn (SOME o pr1 nhd) 1
Proof
  fs[primrec_nhd,primrec_recfn]
QED

Theorem nhd_nlist_of:
  nhd (nlist_of (h::t)) = h
Proof
  fs[nhd_thm]
QED

Theorem nhd_phi_exists:
  ∃i. ∀x. Phi i (nlist_of x) = SOME (pr1 nhd x)
Proof
  assume_tac recfn_nhd >> drule recfns_in_Phi >> rw[] >> qexists_tac`i` >> rw[] >> 
  `∃l. nlist_of l = x` by fs[nlist_of_SURJ] >> rw[] >> Cases_on`l` >> rw[]
QED


Theorem recfn_ncons:
  recfn (SOME o pr2 ncons) 2
Proof
  assume_tac primrec_ncons >> fs[primrec_recfn]
QED

Theorem primrec_ncons1:
  primrec (pr1 (λx. ncons x 0)) 1
Proof
  `Cn (pr2 ncons) [(proj 0); zerof] = pr1 (λx. ncons x 0)` by 
    (fs[FUN_EQ_THM,Cn_def,pr1_def] >> rw[] >> Cases_on`x` >> rw[] ) >> 
  `primrec (Cn (pr2 ncons) [proj 0; zerof]) 1` suffices_by fs[primrec_recfn] >>
  fs[primrec_rules]
QED

Theorem recfn_ncons1:
  recfn (SOME o pr1 (λx. ncons x 0)) 1
Proof
  assume_tac primrec_ncons >> 
  `Cn (pr2 ncons) [(proj 0); zerof] = pr1 (λx. ncons x 0)` by 
    (fs[FUN_EQ_THM,Cn_def,pr1_def] >> rw[] >> Cases_on`x` >> rw[] ) >> 
  `recfn (SOME o  (Cn (pr2 ncons) [proj 0; zerof])) 1` suffices_by rw[] >> 
  `primrec (Cn (pr2 ncons) [proj 0; zerof]) 1` suffices_by fs[primrec_recfn] >>
  fs[primrec_rules]
QED

Theorem recfn2_ncons0:
  recfn (SOME o pr2 (λx y. ncons x 0)) 2
Proof
  assume_tac primrec_ncons >> 
  `Cn (pr2 ncons) [(proj 0); zerof] = pr2 (λx y. ncons x 0)` by 
    (fs[FUN_EQ_THM,Cn_def,pr2_def] >> rw[] >> Cases_on`x` >> rw[] >> Cases_on`t` >> rw[] ) >> 
  `recfn (SOME o  (Cn (pr2 ncons) [proj 0; zerof])) 2` suffices_by rw[] >> 
  `primrec (Cn (pr2 ncons) [proj 0; zerof]) 2` suffices_by fs[primrec_recfn] >>
  fs[primrec_rules]
QED

Theorem recfn1_ncons_k:
  recfn (SOME o pr1 (λx. ncons x k)) 1
Proof
  assume_tac primrec_ncons >> 
  `Cn (pr2 ncons) [(proj 0); K k] = pr1 (λx. ncons x k)` by 
    (fs[FUN_EQ_THM,Cn_def,pr1_def] >> rw[] >> Cases_on`x` >> rw[] ) >> 
  `recfn (SOME o  (Cn (pr2 ncons) [proj 0; K k])) 1` suffices_by rw[] >> 
  `primrec (Cn (pr2 ncons) [proj 0; K k]) 1` suffices_by fs[primrec_recfn] >>
  fs[primrec_rules]
QED

(*
Theorem primrec_eq_1:
  (∀x. f [x] = g [x]) ∧ primrec f 1 ==> primrec g 1
Proof
  rw[] >> `(∀x. g [x] = (λy. f [y]) x)` by fs[] >> 
  `g = pr1 (λy. f [y]) ` by fs[unary_primrec_eq] >>
  fs[primrec_rules]
  `primrec (λl. FUNPOW g 1 (proj 0 l)) 1`
QED

Theorem primrec_nlist_of:
  primrec nlist_of 1
Proof
  `∀x. nlist_of [x] = ncons x 0`  by fs[] >>
  `primrec (pr1 (λx. ncons x 0)) 1` suffices_by 
    (`∀l. nlist_of [l] = pr1 (λx. ncons x 0) [l]` by fs[] >> 
     `pr1 (λx. ncons x 0) = pr1 (λx. nlist_of [x])` by fs[unary_primrec_eq] >> 
     `primrec (pr1 (λx. nlist_of [x])) 1` by fs[primrec_pr1]  ) >> 
    fs[primrec_ncons1] >> unary_primrec_eq, primrec_pr1
QED

Theorem not_true_thm:
  recfn (SOME o (λl. ncons (nlist_of l) 0)) 1
Proof
  `primrec (λl. ncons (nlist_of l) 0) 1` suffices_by fs[primrec_recfn] >> 
  ` (λl. ncons (nlist_of l) 0) = Cn (pr2 ncons) [nlist_of;zerof]` by 
    (fs[FUN_EQ_THM,Cn_def,pr2_def] >> rw[]) >> 
  `primrec (Cn (pr2 ncons) [nlist_of;zerof]) 1` suffices_by fs[] >> 
  `primrec (pr2 ncons) (LENGTH [nlist_of;zerof]) ∧ EVERY (λg. primrec g 1) [nlist_of;zerof]` suffices_by simp[primrec_rules] >> rw[primrec_ncons] >>
  ``
QED
*)



Theorem ncons_phi_exists:
  ∃i. ∀x. Phi i x = SOME (ncons x 0)
Proof
  qexists_tac`dBnum (fromTerm (C @@ cncons @@ (church 0) ) )` >> fs[Phi_def] >>
  `0 = nlist_of []` by fs[] >> pop_assum (fn th=> simp_tac(bool_ss)[SimpL``$/\``,th]) >>
  simp_tac(bsrw_ss())[cncons_behaviour,Excl "nlist_of_def",normal_orderTheory.bnf_bnf_of] >> 
  fs[]
QED

Theorem recfn_nlist_of:
  ∃Ri. ∀n. Phi Ri n = SOME (nlist_of [n])
Proof
  fs[nlist_of_def,ncons_phi_exists] 
QED

Theorem recfns_in_Phi2:
  ∀f n. recfn f 1 ⇒ ∃i. ∀x. Phi i x = f [x]
Proof
  rw[] >> drule recfns_in_Phi >> rw[] >> 
  `∃Ri. ∀n. Phi Ri n = SOME (nlist_of [n])` by fs[recfn_nlist_of] >>
  `∃Rii. ∀n. Phi Rii n = monad_bind (Phi Ri n) (λx. Phi i x)` by fs[composition_computable] >>
  qexists_tac`Rii` >> rw[] >> ` Phi i (nlist_of [x]) = f [x]` by fs[] >> fs[]
QED


Theorem phi_ncons_exists:
  ∃i. ∀x n. (Phi i (ncons x n) = SOME x) ∧ (Phi i 0 = SOME 0)
Proof
  `∃j. ∀x. (Phi j 0 = SOME 0) ∧ (Phi j (SUC x) = SOME (nhd (SUC x)))` suffices_by 
    (strip_tac >> qexists_tac`j` >> rw[] >> `ncons x n <> 0` by 
     fs[ncons_not_nnil] >> 
     `∃m. ncons x n = SUC m` by (qexists_tac`x ⊗ n` >> simp[ncons_def]) >>
     fs[] >> metis_tac[nhd_thm]) >> 
   `∃i. ∀x. Phi i x = SOME (nhd x)` suffices_by 
     (strip_tac >> qexists_tac`i` >> rw[] >> EVAL_TAC) >>
   assume_tac recfn_nhd >> drule recfns_in_Phi2 >> rw[]
QED

Theorem rec_sigma0_corr:
  A ∈ rec_sigma 0 <=> recursive A
Proof
  simp[rec_sigma,recursive_def] >> eq_tac >> rw[] >>
  fs[combinTheory.APPLY_UPDATE_THM]
  >- ( 
      `∃i. ∀x. Phi i x = SOME (ncons x 0)` by fs[ncons_phi_exists] >> 
      `∃Rii. ∀n. Phi Rii n = monad_bind (Phi i n) (λx. Phi Ri x)` by fs[composition_computable]>>
      qexists_tac`Rii` >> rw[] >> metis_tac[] )
  >- (fs[combinTheory.APPLY_UPDATE_THM] >>
      `∃i. ∀x n. (Phi i (ncons x n) = SOME x) ∧ (Phi i 0 = SOME 0)` by fs[phi_ncons_exists] >>
      `∃Rii. ∀n. Phi Rii n = monad_bind (Phi i n) (λx. Phi M x)` by fs[composition_computable]>>
      qexists_tac`Rii` >> rw[] >> 
      `∀x.  ((if x ∈ A then 1 else 0) ≠ 0) =(x ∈ A) ` by (rw[] >> eq_tac >> rw[]) >> fs[]>>
      `(m = 0) ∨ (∃k j. m = ncons k j)` by metis_tac[nlist_cases] >> fs[AllCaseEqs()] )
QED

val rec_cn = List.nth (CONJUNCTS recfn_rules,3)

Theorem recfn_K_2:
  ∀n. recfn (SOME o (K n)) 2
Proof
  rw[] >> `primrec (K n) 2` by fs[primrec_K] >> `recfn (SOME ∘ (K n)) 2` by fs[primrec_recfn] >>fs[]
QED

Theorem recfn_proj:
  ∀i n. i<n ==> recfn (SOME o (proj i)) n
Proof
  rw[] >> `primrec (proj i) n` by fs[primrec_rules] >> fs[primrec_recfn]
QED

Theorem recfn_sub:
  recfn (SOME o (pr2 $-)) 2
Proof
  fs[primrec_pr_sub,primrec_recfn]
QED

Theorem recfn_recCnminimise_r_ncons:
  ∀R. recfn (minimise (recCn (SOME o (pr2 $-)) [SOME o (K 1);recCn recPhi [SOME o (K R);recCn (SOME o (pr2 ncons)) [SOME o (proj 1);recCn (SOME o (pr2 ncons)) [SOME o (proj 0);SOME o zerof]] ] ]) ) 1
Proof
  strip_tac >> `recfn (recCn (SOME o (pr2 $-)) [SOME o (K 1);recCn recPhi [SOME o (K R);recCn (SOME o (pr2 ncons)) [SOME o (proj 1);recCn (SOME o (pr2 ncons)) [SOME o (proj 0);SOME o zerof]] ] ]) 2` suffices_by fs[recfn_rules] >>
  irule rec_cn >> rw[]
  >- (`recfn (SOME o (K 1)) 2` by fs[recfn_K_2] >> fs[])
  >- (irule rec_cn >> rw[] 
      >- (`recfn (SOME o (K R)) 2` by fs[recfn_K_2] >> fs[]) 
      >- (irule rec_cn >> rw[]
          >- (fs[recfn_proj])
          >- (irule rec_cn >> rw[] 
              >- (fs[recfn_proj])
              >- (`recfn (SOME o (K 0)) 2` by fs[recfn_K_2] >> fs[])
              >- (fs[recfn_ncons]))
          >- (fs[recfn_ncons]) ) 
      >- (metis_tac[recfn_recPhi,recPhi_rec2Phi]) )
  >- (fs[recfn_sub])
QED


Theorem recCnminimise_r_ncons_corr:
  (recCn (SOME o (pr2 $-)) [SOME o (K 1);recCn recPhi [SOME o (K R);recCn (SOME o (pr2 ncons)) [SOME o (proj 1);recCn (SOME o (pr2 ncons)) [SOME o (proj 0);SOME o zerof]] ] ]) [n;e] = 
  if IS_SOME (Phi R (ncons e (ncons n 0))) then SOME (1 - THE (Phi R (ncons e (ncons n 0)))) else NONE
Proof
  rw[recCn_def] >> fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
QED

Theorem recCnminimise_r_ncons_corr2:
  IS_SOME (Phi R (ncons e (ncons n 0))) ==>
  ((recCn (SOME o (pr2 $-)) [SOME o (K 1);recCn recPhi [SOME o (K R);recCn (SOME o (pr2 ncons)) [SOME o (proj 1);recCn (SOME o (pr2 ncons)) [SOME o (proj 0);SOME o zerof]] ] ]) [n;e] = 
  SOME (1 - THE (Phi R (ncons e (ncons n 0)))))
Proof
  fs[recCnminimise_r_ncons_corr]
QED

Theorem recCnminimise_r_ncons_corr3:
  ∀R e n. IS_SOME (Phi R (ncons e (ncons n 0))) ==>
  ((recCn (SOME o (pr2 $-)) 
      [K (SOME 1);
       recCn recPhi 
         [K (SOME R);
          recCn (SOME o (pr2 ncons)) 
            [SOME o (proj 1);
             recCn (SOME o (pr2 ncons)) [SOME o (proj 0);K (SOME 0)]] ] ]) 
    [n;e] = SOME (1 - THE (Phi R (ncons e (ncons n 0)))))
Proof
  rw[] >> assume_tac recCnminimise_r_ncons_corr2 >> fs[]
QED

Theorem minimise_useful:
  (minimise f l = SOME n) <=> ((f (n::l) = SOME 0) ∧ ∀i. i<n ==> ∃m. (f (i::l) = SOME m) ∧ 0 < m)
Proof
  fs[minimise_thm] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[EQ_IMP_THM]
  >- simp[] >- metis_tac[] >> rename[`n1=n2`] >>  `¬(n1<n2) ∧ ¬(n2<n1) ` suffices_by simp[] >> 
  rpt strip_tac  >> metis_tac[prim_recTheory.LESS_REFL,optionTheory.SOME_11]
QED


val step_n_def = Define`step_n N = LAM "xn" 
         (cbnf @@ (csteps @@ (cnel @@ church 1 @@ VAR"xn") 
                          @@ (cdAPP @@ (cnumdB @@ church N) 
                                    @@ (cchurch @@ (cnel @@ church 0 @@ VAR"xn") ) ) )
               @@ church 1
               @@ church 0 ) `;

Theorem FV_cnel[simp]: FV cnel = {}
Proof simp[EXTENSION,cnel_def]
QED

val step_n_eqn = brackabs.brackabs_equiv [] (SPEC_ALL step_n_def)

Theorem step_n_behaviour:
  step_n N @@ church M == 
  church (if (bnf (steps (nel 1 M) (toTerm (numdB N) @@ church (nel 0 M)) ) ) then 1 else 0)
Proof
  simp_tac (bsrw_ss()) [step_n_eqn, cnel_behaviour,csteps_behaviour,cbnf_behaviour] >> 
  qmatch_abbrev_tac`cB BB @@ _ @@ _ == _` >> Cases_on`BB` >>  
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] 
QED

Theorem FV_steps_n[simp]: FV (step_n N) = {}
Proof simp[EXTENSION,step_n_def]
QED


Theorem cB_true_K:
  cB T = K
Proof
  simp_tac (bsrw_ss()) [churchboolTheory.cB_def] >>
  fs[chap2Theory.K_def]
QED



Theorem cB_false_I:
  cB F = LAM "x" I
Proof
  simp_tac (bsrw_ss()) [brackabsTheory.I_I,churchboolTheory.cB_def]
QED


Theorem cB_church:
  is_church (cB p) ==> (∃n. cB p = church n)
Proof
  rw[] >> `∃n. cB p = church n` by fs[churchnumTheory.is_church_church] >> 
  metis_tac[]
QED

Theorem cB_is_church_T:
  is_church (cB T)
Proof
  fs[churchnumTheory.is_church_def,churchboolTheory.cB_def] >> qexists_tac`"y" ` >>
  qexists_tac`"x"` >> qexists_tac`0` >> rw[]
QED

Theorem cB_is_church_F:
  ¬(is_church (cB F))
Proof
  strip_tac >> fs[churchnumTheory.is_church_def,churchboolTheory.cB_def] >> 
  fs[termTheory.LAM_eq_thm] >> Cases_on`n` >> fs[FUNPOW_SUC]
  >- (`swapstr f "y" z = z` by fs[basic_swapTheory.swapstr_thm ] >> metis_tac[])
  >- (Cases_on`"x" <> f` >> rw[] 
        >- (`swapstr z "x" f = f` by fs[basic_swapTheory.swapstr_thm ] >> fs[])
        >- (`swapstr z "x" "x" = z` by fs[basic_swapTheory.swapstr_thm ] >> fs[] >>
            `swapstr z "y" "x" = "x"` by fs[basic_swapTheory.swapstr_thm ] >> fs[] ))
QED



Theorem force_num_cB_F:
  force_num (cB F) = 0
Proof
  metis_tac[cB_is_church_F,churchnumTheory.force_num_def]
QED

Theorem force_num_cB_T:
  force_num (cB T) = 0
Proof
  fs[cB_is_church_T,churchnumTheory.force_num_def] >>
  SELECT_ELIM_TAC >> rw[cB_church,cB_is_church_T] >>
  fs[churchboolTheory.cB_def,churchnumTheory.church_def,termTheory.LAM_eq_thm] >>
  Cases_on`x` >> fs[FUNPOW_SUC]
QED

Theorem force_num_cB:
  force_num (cB x) = 0
Proof
  Cases_on`x` >> fs[force_num_cB_F,force_num_cB_T]
QED

Theorem bnf_of_church[simp]:
  bnf_of (church x) = SOME (church x)
Proof
  simp[normal_orderTheory.bnf_bnf_of]
QED

Theorem rec_sigma1_corr:
  A ∈ rec_sigma 1 <=> re A
Proof
  simp[rec_sigma,re_semidp] >> eq_tac >> rw[] >> 
  fs[combinTheory.APPLY_UPDATE_THM,theorem "MKEA_0_compute"]
  >- (qabbrev_tac`M =  ( (recCn (SOME o (pr2 $-)) [SOME o (K 1);recCn recPhi 
        [SOME o (K Ri);recCn (SOME o (pr2 ncons)) [SOME o (proj 1);recCn (SOME o (pr2 ncons)) 
        [SOME o (proj 0);SOME o zerof]] ] ]) ) ` >> 
      `recfn (minimise M) 1` by fs[Abbr`M`,recfn_recCnminimise_r_ncons] >> 
      drule recfns_in_Phi2 >> rw[] >>
      qexists_tac`i` >> rw[] >> 
      `∀x. IS_SOME (Phi Ri x)` by (rw[] >> Cases_on`Phi Ri x = SOME 0` >> fs[]) >>
      `∀x y. M [x;y] = SOME (1 - THE (Phi Ri (ncons y (ncons x 0))))` by 
            (rw[Abbr`M`] >> 
             assume_tac recCnminimise_r_ncons_corr3 >> fs[]) >>
      eq_tac>> rw[]
      >- (qabbrev_tac`mu = LEAST x. Phi Ri (ncons e (ncons x 0)) = SOME 1` >>
          qexists_tac`mu` >> rw[minimise_def] 
          >- (qexists_tac`mu` >> simp[Abbr`mu`] >> numLib.LEAST_ELIM_TAC >> rw[] >- metis_tac[] >>
              qmatch_abbrev_tac`0<1 - THE (Phi Ri X)` >> `Phi Ri X = SOME 0` by metis_tac[] >>fs[]  )
          >- (SELECT_ELIM_TAC >> rw[]  
              >- (qexists_tac`mu` >> simp[Abbr`mu`] >> numLib.LEAST_ELIM_TAC >> rw[] 
                  >- metis_tac[] >> qmatch_abbrev_tac`0<1 - THE (Phi Ri X)` >> 
                  `Phi Ri X = SOME 0` by metis_tac[] >>fs[]  ) >> 
              fs[Abbr`mu`] >> numLib.LEAST_ELIM_TAC >> rw[] >- metis_tac[] >> rename[`n1=n2`] >>
              `¬(n1<n2) ∧ ¬(n2<n1) ` suffices_by simp[] >> rpt strip_tac 
              >- (metis_tac[optionTheory.THE_DEF,DECIDE``¬(1<=0)``])
              >- (FIRST_X_ASSUM drule >> simp[]) )  )
     >- (qexists_tac`m` >> pop_assum mp_tac >> simp[minimise_useful] >> rw[] >> 
         metis_tac[optionTheory.THE_DEF,DECIDE``¬(1<=0)``] )  )
  >- (qexists_tac`dBnum (fromTerm (step_n N) )` >> rw[Phi_def] >>  
      simp_tac (bsrw_ss()) [step_n_behaviour] 
      >- (full_simp_tac (bsrw_ss()) [step_n_behaviour,CaseEq"bool"] )
      >- (simp_tac bool_ss [nel_SUC_CONS,ONE] >> rw[stepsTheory.bnf_steps,CaseEq"bool"]  ) )
QED


Definition co_re:
  co_re s = re (COMPL s)
End

Definition rec_pi:
  rec_pi n = {
    A | ∃Ri.
             (∀m. (Phi Ri m = SOME 0) ∨ (Phi Ri m = SOME 1)) ∧
             ∀x. x ∈ A ⇔ interpret I⦇0 ↦ x⦈ (MKAE n Ri)
  }
End

Theorem rec_pi_0_recursive:
  A ∈ rec_pi 0 <=> recursive A
Proof
  `A ∈ rec_pi 0 <=> A ∈ rec_sigma 0` suffices_by metis_tac[rec_sigma0_corr] >>
  simp[rec_pi,rec_sigma]
QED


Definition co_re_machine:
  co_re_machine Ri = 
  LAM "e" 
    (cfindleast 
     @@ (LAM "NN" 
        (ceqnat @@
          church 0 @@
          (cforce_num @@ 
               (cbnf_ofk @@ I @@ (cdAPP @@ (cnumdB @@ church Ri)
                                        @@ (cchurch @@ (cncons @@ VAR "e"
                                                               @@  (cncons @@ VAR "NN"
                                                                           @@ church 0 ) ))) ) ) ))
     @@ I)
End


Theorem FV_co_re_machine[simp]:
  FV (co_re_machine n) = {}
Proof
  simp[co_re_machine,EXTENSION] >> rw[EQ_IMP_THM]
QED

val co_re_machine_eqn = brackabs.brackabs_equiv [] (SPEC_ALL co_re_machine)

Theorem cncons_sing:
  cncons @@ church n @@ church 0 == church (nlist_of [n])
Proof
  assume_tac (GEN_ALL prtermTheory.cncons_behaviour) >> 
  `cncons @@ church n @@ church (nlist_of []) == church (nlist_of (n::[]))` by metis_tac[] >> fs[]
QED

val _ = delsimps["DISJ_IMP_EQ"]




Theorem rec_pi_1_co_re:
  A ∈ rec_pi 1 <=> co_re A
Proof
  simp[rec_pi,re_semidp,co_re] >> eq_tac >> rw[] >> 
  fs[combinTheory.APPLY_UPDATE_THM,theorem "MKEA_0_compute"]
  >- (qexists_tac`dBnum (fromTerm (co_re_machine Ri))` >> rw[] >> 
      simp_tac (bsrw_ss()) [co_re_machine_eqn,Phi_def] >>
      qmatch_abbrev_tac`_ <=> ∃z. bnf_of (cfindleast @@ P @@ I) = SOME z` >>
      `∀n. P @@ church n == cB (Phi Ri (nlist_of [e;n]) = SOME 0)` by 
        (simp_tac (bsrw_ss()) [Abbr`P`, cncons_sing,Excl"nlist_of_def",
                               cdBnum_behaviour,cncons_behaviour] >> GEN_TAC >> 
         last_x_assum (qspec_then `nlist_of [e;n]` mp_tac) >> simp[] >> strip_tac>>simp[] >>
         pop_assum mp_tac >> simp[Phi_def] >> strip_tac >> drule (GEN_ALL cbnf_of_works1) >> 
         simp[] >>
           simp_tac (bsrw_ss()) [] >> pop_assum (fn th=> simp[SYM th]) ) >>
      `(∀n. ∃b. P @@ church n == cB b)` by metis_tac[] >>
      eq_tac >> rw[] 
      >- (last_x_assum (qspec_then `nlist_of [e;n]` mp_tac)>> reverse (rw[])
          >- (fs[Phi_def] >> metis_tac[]) >> 
          `∃N. P @@ church N == cB T` by (asm_simp_tac (bsrw_ss()) [] >> metis_tac[]) >> 
          drule_all (GEN_ALL churchnumTheory.cfindleast_termI) >> simp_tac (bsrw_ss()) [] )  
      >- (`(cfindleast @@ P @@ I) -n->* z ∧ bnf z` by metis_tac[normal_orderTheory.bnf_of_SOME]>>
          `(cfindleast @@ P @@ I) == z` by fs[normal_orderTheory.nstar_lameq ] >>
          drule_all (GEN_ALL churchnumTheory.cfindleast_bnfE) >> rw[] >>
          qexists_tac`m` >> qpat_x_assum `_ @@ _ == cB T` mp_tac >> 
          asm_simp_tac (bsrw_ss()) [] >> simp[Phi_def] >> rpt strip_tac >> 
          rename[`0 = force_num z1`,`_ ∨ 1 <> force_num z2`] >>
          Cases_on`1 ≠ force_num z2` >> simp[] >> `1 = force_num z2` by fs[] >> strip_tac >> fs[]  ) )
  >- (qexists_tac`dBnum (fromTerm (B @@ (cminus @@ church 1) @@ step_n N) )` >> rw[Phi_def] >>  
      simp_tac (bsrw_ss()) [step_n_behaviour,churchnumTheory.cminus_behaviour] 
      >- (rw[] )
      >- (simp_tac bool_ss [nel_SUC_CONS,ONE,nel0_ncons] >> 
          ONCE_REWRITE_TAC[(DECIDE``(P <=> Q) <=> (¬P <=> ¬Q)``)] >>
          PURE_ASM_REWRITE_TAC [] >> simp[Phi_def] >> simp_tac (srw_ss()++boolSimps.COND_elim_ss) [] >>
         simp[stepsTheory.bnf_steps] ) )
QED



Definition rec_delta:
  rec_delta n = rec_sigma n ∩ rec_pi n			
End


Definition lnot:
  lnot M = dBnum (fromTerm (B @@ (cbnf_ofk @@ (B @@ (cminus @@ church 1) 
                                           @@ cforce_num) )
                              @@ (B @@ (cdAPP @@ (cnumdB @@ church M))
                                    @@ cchurch )))
End


Theorem lnot_thm[simp]:
  Phi (lnot m) n = OPTION_MAP ((-) 1) (Phi m n)
Proof
  fs[lnot,Phi_def] >> simp_tac (bsrw_ss()) [] >> Cases_on`bnf_of (toTerm (numdB m) @@ church n)` >> simp[]
  >- (drule bnfNONE_cbnf_ofk_fails >> simp[] >> rw[normal_orderTheory.bnf_of_NONE]) >>
  drule cbnf_of_works1 >> simp[] >> simp_tac (bsrw_ss()) []
QED

Theorem lnot_lnot_I:
  (∀m. (Phi n m = SOME 0) ∨ (Phi n m = SOME 1)) ==> (Phi (lnot (lnot n)) k = Phi n k)
Proof
  rw[] >> Cases_on`Phi n k = SOME 0` >> simp[] >> `Phi n k = SOME 1` by metis_tac[] >> simp[]
QED

Theorem lnot_01:
   (∀m. (Phi n m = SOME 0) ∨ (Phi n m = SOME 1)) ==>  (∀m. (Phi (lnot n) m = SOME 0) ∨ (Phi (lnot n) m = SOME 1))
Proof
  rw[] >> Cases_on`(∃z. (Phi n m = SOME z) ∧ 1 ≤ z)` >> rw[] >> qexists_tac`0` >> fs[] >> 
  `Phi n m ≠ SOME 1 ∨ ¬(1 ≤ 1)` by fs[] >- metis_tac[] >- fs[]
QED


Theorem MKAE0_lnot_lnot[simp]:
  (∀m. (Phi R m = SOME 0) ∨ (Phi R m = SOME 1)) ==> 
  ∀f. (interpret f (MKAE0 n k (lnot (lnot R))) = interpret f (MKAE0 n k R)) ∧ 
      (interpret f (MKEA0 n k (lnot (lnot R))) = interpret f (MKEA0 n k R))
Proof
  strip_tac >> Induct_on`n` >> simp[combinTheory.APPLY_UPDATE_THM,theorem "MKEA_0_compute"] >> rw[EQ_IMP_THM]
  >- (Cases_on`z' = 1` >> fs[] >> Cases_on`z'=0` >> fs[] >> 
      `(Phi R (nlist_of (MAP f (GENLIST I (k + 1)))) = SOME 0) ∨ 
       (Phi R (nlist_of (MAP f (GENLIST I (k + 1)))) = SOME 1)` by fs[]>>fs[])
QED

Theorem lnot_interpret:
   ∀k f R. (∀m. (Phi R m = SOME 0) ∨ (Phi R m = SOME 1)) ==> 
   ((¬interpret f (MKEA0 n k R)) ⇔ interpret f (MKAE0 n k (lnot R))) ∧
   ((¬interpret f (MKAE0 n k R)) ⇔ interpret f (MKEA0 n k (lnot R)))
Proof
  Induct_on`n` >> simp[combinTheory.APPLY_UPDATE_THM,theorem "MKEA_0_compute"]
  >> rw[] >> fs[combinTheory.APPLY_UPDATE_THM,theorem "MKEA_0_compute"] >> rw[] >> eq_tac >> rw[] 
     >- (qexists_tac`0` >> fs[] >>metis_tac[]) 
     >- (`z=0` by fs[] >> fs[] ) 
QED



Theorem thm1_3_i:
  COMPL A ∈ rec_pi n <=> A ∈ rec_sigma n
Proof
  simp[rec_pi,rec_sigma] >> eq_tac >> rw[] >> 
  fs[combinTheory.APPLY_UPDATE_THM,lnot_interpret] >> metis_tac[lnot_interpret,lnot_01]
QED



(* Up to here *)


Theorem interpret_MKEA0_LT:
  ∀m1 n1 n2 f g m2. (n1<m1 ∧ n2<m2 ∧ interpret f (MKEA0 n1 n2 Ri)) ==> 
    (interpret g (MKAE0 m1 m2 Ri) ∧ interpret g (MKEA0 m1 m2 Ri))
Proof
  Induct_on`m1` >> fs[] >> rw[] >> Cases_on `n1 = m1` >> rw[]
  >- ()
  >- (`n1 < m1` by fs[] >> metis_tac[])
  >- ()
  >- (qexists_tac`SUC m1` >> `n1 < m1` by fs[] >> metis_tac[])
QED


Theorem rec_sigma_step:
  A ∈ rec_sigma n ∨ A ∈ rec_pi n ==> A ∈ rec_sigma (SUC n) ∧ A ∈ rec_pi (SUC n)
Proof
  rw[rec_pi,rec_sigma] >> qexists_tac`Ri` >> rw[]
QED



Theorem thm1_3_ii1:
  ∀m n. A ∈ rec_sigma n ==>  n<m ==> A ∈ rec_sigma m ∩ rec_pi m
Proof
  Induct_on`m` >> simp[] >> rw[] >> fs[rec_sigma,rec_pi]
  >- (qexists_tac`Ri` >> rw[] >> eq_tac >> rw[])

  >- (Cases_on`A ∈ rec_sigma m` >- (fs[]) >- (fs[] >> `¬(n<m)` by fs[] >> Cases_on`n=m` >> fs[])  )
QED


Theorem thm1_3_ii2:
  rec_pi A n ==> (∀m. m>n ==> (rec_sigma A m ∧ rec_pi A m) )
Proof
  rw[rec_pi,rec_sigma]
QED


Theorem thm1_3_iii1:
  rec_sigma A n ∧ rec_sigma B n ==> (rec_sigma (A ∪ B) n ∧ rec_sigma (A ∩ B) n)
Proof

QED

Theorem thm1_3_iii2:
  rec_pi A n ∧ rec_pi B n ==> (rec_pi (A ∪ B) n ∧ rec_pi (A ∩ B) n)
Proof

QED

Theorem thm1_3_iv:
  rec_sigma R n ∧ n>0 ∧ A = {x | ∃y. R (x,y)} ==> rec_sigma A n
Proof

QED



val _ = export_theory()
