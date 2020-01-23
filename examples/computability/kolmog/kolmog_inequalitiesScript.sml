open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmogorov_complexityTheory invarianceResultsTheory boolListsTheory
open churchDBTheory
open recursivefnsTheory primrecfnsTheory prtermTheory
open unary_recfnsTheory

val _ = new_theory "kolmog_inequalities"
val _ = intLib.deprecate_int()

Theorem on2bl_SOME:
  on2bl x = SOME y <=> (∃z. x = SOME z ∧ y = n2bl z)
Proof
 simp[on2bl_def]
QED

Definition nblconcat_def:
  nblconcat a b = a + b * 2 ** (LENGTH (n2bl a))
End

Theorem nblconcat_correct[simp]:
  nblconcat (bl2n a) (bl2n b) = bl2n (a++b)
Proof
  fs[nblconcat_def,bl2n_append]
QED


Theorem pr_log2_thm[compute]:
  pr_log2 [i] = if i <= 1 then 1 else 1 + pr_log2 [i DIV 2]
Proof
  fs[pr_log2_def,Once prnlistTheory.WFM_correct]
QED

Definition pr_ell:
  pr_ell = WFM (λf n. if n=0 then 0
                      else if EVEN n then 1 + f ((n-2) DIV 2)
                           else 1 + f ((n-1) DIV 2) )
End

Theorem pr_ell_thm:
  pr_ell [n] = if n=0 then 0
               else if EVEN n then 1 + pr_ell [(n-2) DIV 2]
                    else 1 + pr_ell [(n-1) DIV 2]
Proof
  fs[pr_ell,Once prnlistTheory.WFM_correct] >> rw[] >> intLib.ARITH_TAC
QED




Theorem primrec_ell:
  primrec (pr1 ℓ) 1
Proof
  irule primrec_pr1 >> qexists_tac‘pr_ell’ >> rw[]
  >- (fs[pr_ell] >> irule prnlistTheory.primrec_WFM >>
      rw[prnlistTheory.restr_def,DIV_LESS_EQ] >>
      ‘∀n. (n-1) DIV 2 <= n’ by (intLib.ARITH_TAC) >> simp[] >> irule primrec_pr2 >> simp[] >>
      qexists_tac‘pr_cond (Cn pr_mod [proj 0; K 2])
                          (Cn succ [Cn (pr2 nel) [Cn (pr_div) [Cn (pr2 $-) [proj 0;K 1]; K 2];proj 1]])
                          (Cn succ [Cn (pr2 nel) [Cn (pr_div) [proj 0; K 2];proj 1]])’ >> rw[]
      >- (irule primrec_pr_cond >> rw[] >> rpt (irule primrec_Cn >> simp[primrec_rules] ) ) >>
      rw[pr_cond_def] >- (‘m MOD 2 = 1’ suffices_by simp[] >> fs[EVEN_ADD,MOD_2]) >>
      ‘m MOD 2 = 0’ suffices_by simp[] >> fs[EVEN_ADD,MOD_2]  ) >>

  completeInduct_on‘n’ >> simp[Once pr_ell_thm,Once num_to_bool_list_def] >>  rw[ADD1]>>
  first_x_assum irule >> intLib.ARITH_TAC
QED


(* UCKC is conditional kolmogorov complexity, UKCB is kolmogorov complexity typed the right way *)
Theorem pair_11[simp]:
  pair a b = pair c d <=> a=c ∧ b=d
Proof
  rw[EQ_IMP_THM,pair_def,bar_def] >>
  ‘LENGTH a = LENGTH c ∧ a++b = c++d’ by
    (‘Tpow (LENGTH a) ++ [F] ++ (a ++ b) = Tpow (LENGTH c) ++ [F] ++ (c ++ d)’
       by metis_tac[APPEND_ASSOC] >> metis_tac[Tpow_Fapp_eq]) >>
  ‘DROP (LENGTH a) (a++b) = DROP (LENGTH c) (c++d)’ by fs[] >>
  ‘TAKE (LENGTH a) (a++b) = TAKE (LENGTH c) (c++d)’ by fs[] >>
  fs[rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem pair_LENGTH[simp]:
  LENGTH (pair a b) = 2*LENGTH a + 1 + LENGTH b
Proof
  simp[pair_def]
QED

Theorem Tpow_11[simp]:
  Tpow n = Tpow m ⇔ n = m
Proof
  simp[Tpow_def, EQ_IMP_THM, LIST_EQ_REWRITE]
QED


Theorem bar_prefix_append[simp]:
  bar x ≼ bar y ++ l ⇔ x = y
Proof
  simp[bar_def, EQ_IMP_THM, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  rename [‘_ ++ l = _ ++ m’] >>
  ‘y ++ l = x ++ m’  by metis_tac[Tpow_Fapp_eq, APPEND_ASSOC, APPEND_11] >>
  full_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND_11] >> fs[] >>
  ‘LENGTH l = LENGTH m’ by (pop_assum (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[])>>
  metis_tac[APPEND_LENGTH_EQ]
QED

Theorem Tpow_0[simp]:
  Tpow 0 = []
Proof
  fs[Tpow_def]
QED

Theorem pair_nil[simp]:
  pair [] x = F::x
Proof
  fs[pair_def,bar_def]
QED

Definition subndiv2_def:
  subndiv2 n = recCn (recCn (SOME o pr_div)
                            [SOME o proj 0;K (SOME 2)])
                     [recCn (SOME o (pr2 $-)) [SOME o proj 0;K (SOME n)]]
End

Theorem subndiv2_rec[simp]:
  recfn (subndiv2 n) 1
Proof
  simp[subndiv2_def] >> rpt (irule recfnCn >> rw[]) >>
  irule primrec_recfn >> fs[primrec_rules]
QED

Theorem subndiv2_correct[simp]:
  subndiv2 n [m] = SOME ((m-n) DIV 2)
Proof
  fs[subndiv2_def, recursivefnsTheory.recCn_def]
QED

Theorem recfn_rec2_Phi[simp]:
  recfn (rec2 Phi) 2
Proof
  mp_tac prtermTheory.recfn_recPhi >> rw[Excl"recfn_recPhi"]
QED

Theorem unary_rec_fns_phi:
  recfn f 1 ==> ∃i. ∀x. Phi i x = f [x]
Proof
  rw[] >> drule_then strip_assume_tac recfns_in_Phi >> qexists_tac‘i’ >> rw[] >>
  ‘Phi i (fold [x]) = f [x]’ by fs[] >> fs[unary_recfnsTheory.fold_def]
QED

Theorem binary_rec_fns_phi:
  recfn f 2 ⇒ ∃i. ∀x y. Phi i (x ⊗ y) = f [x;y]
Proof
  rw[] >> drule_then strip_assume_tac recfns_in_Phi >> qexists_tac‘i’ >> rw[] >>
  pop_assum (simp o single o GSYM)
QED

(* univ_mach does not imply univ_rf anymore  *)

(*

Theorem univ_mach_rf:
  univ_mach U ==> univ_rf U
Proof
  rw[univ_mach_def,univ_rf_def] >>
  qabbrev_tac`G=recCn recPhi [K (SOME f);subndiv2 1]` >>
  `recfn G 1` by (simp[Abbr`G`] >> rpt (irule recfnCn >> rw[])) >>
  ‘∀x. G [bl2n (F::x)] = Phi f (bl2n x)’ by
    (simp[Abbr`G`,recCn_def,bool_list_to_num_def]) >>
  drule_then strip_assume_tac recfns_in_Phi >>
  LAST_X_ASSUM (qspecl_then [`n2bl i`,`[]`] mp_tac) >> rw[] >> fs[pair_def] >>
  qexists_tac`F::bar (n2bl i)` >> rw[] >> `Phi f x = Phi i (bl2n (F::n2bl x))` suffices_by fs[]>>
  `G [bl2n (F::n2bl x)] = Phi f (bl2n (n2bl x))` by fs[] >>
  `Phi i (fold [bl2n (F::n2bl x)]) = G [bl2n (F::n2bl x)]` by simp[] >> fs[]
QED

*)

(* rename pair to bl pair etc *)

Definition blsnd_def:
  blsnd l = let l' = dropWhile ((=) T) l; sz = LENGTH l - LENGTH l'; in DROP (sz+1) l'
End

Theorem dropWhile_Tpow:
  dropWhile ((=) T) (Tpow n ++ [F] ++ a ++ b) = [F]++a++b
Proof
  Induct_on‘n’ >> fs[tpow_suc]
QED

Theorem blsnd_pair[simp]:
  blsnd (pair a b) = b
Proof
  fs[blsnd_def,pair_def,bar_def,dropWhile_Tpow] >>
  qmatch_abbrev_tac‘DROP m _ = _’ >>
  ‘m = LENGTH a’ suffices_by fs[rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[Abbr‘m’]
QED

Definition nblsnd0_def:
  nblsnd0 x = if EVEN x ∧ x<>0 then let (nr) = nblsnd0 ((x-2) DIV 2) in
                ((nfst nr)+1) *, (nsnd nr)
              else 0 *, x
Termination
WF_REL_TAC‘$<’ >>rw[DIV_LT_X]
End

Theorem bl2n_eq0[simp]:
  bl2n x = 0 <=> x = []
Proof
  Cases_on‘x’ >> simp[bool_list_to_num_def] >> rw[]
QED

Theorem nblsnd0_correct:
  nblsnd0 (bl2n (Tpow n ++ [F] ++ x)) = n *, bl2n ([F] ++ x)
Proof
  Induct_on‘n’
  >- fs[Once nblsnd0_def,bool_list_to_num_def,tpow_suc,EVEN_ADD,EVEN_MULT] >>
  simp[Once nblsnd0_def] >>
  simp[bool_list_to_num_def,tpow_suc,EVEN_ADD,EVEN_MULT]
QED

Definition nblsr_def[simp]:
  nblsr x 0 = x ∧
  nblsr x (SUC n) = nblsr ((x-1) DIV 2) n
End

Theorem nblsr0[simp]:
  nblsr 0 n = 0
Proof
  Induct_on‘n’ >> simp[]
QED



Theorem DROP_n2bl:
  ∀n x. DROP n (n2bl x) = n2bl (nblsr x n)
Proof
  Induct_on‘n’ >> simp[] >> rw[] >>
  Cases_on‘x=0’  >> simp[]
  >- (rpt (simp[Once num_to_bool_list_def]) ) >>
  Cases_on‘n2bl x’ >> simp[]
  >- (pop_assum (mp_tac o Q.AP_TERM ‘bl2n’) >>
      simp[bool_list_to_num_def,Excl"bl2n_11"] ) >>
  FIRST_X_ASSUM (qspecl_then [‘bl2n t’] mp_tac) >> rw[] >>
  ‘bl2n t = (x-1) DIV 2’ suffices_by fs[] >>
  pop_assum kall_tac >> pop_assum (mp_tac o Q.AP_TERM ‘bl2n’) >>
  simp[bool_list_to_num_def,Excl"bl2n_11"] >> rw[]
QED

Definition nblsnd_def:
  nblsnd x = let nr = nblsnd0 x; n = nfst nr; r = nsnd nr; in nblsr r (n+1)
End

Theorem nblsnd_correct:
  n2bl (nblsnd (bl2n (pair a b))) = b
Proof
  fs[nblsnd_def,GSYM DROP_n2bl,pair_def,bar_def] >>
  ‘DROP (nfst (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))))+1)
        (n2bl (nsnd (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b)))))) =
     b’ suffices_by fs[] >>
  ‘nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))) =
   LENGTH a ⊗ bl2n ([F] ++ (a ++ b))’
     by metis_tac[nblsnd0_correct] >> fs[rich_listTheory.DROP_LENGTH_APPEND]
QED


Definition pr_nblsr_def:
  pr_nblsr = Pr (proj 0)
                (Cn (pr_div) [Cn (pr2 $-) [proj 1;K 1];K 2])
End

Theorem pr_nblsr_correct:
  ∀n r. pr_nblsr [n;r] = nblsr r n
Proof
  Induct_on‘n’ >> simp[pr_nblsr_def,nblsr_def] >> rw[] >>
  ‘ (Pr (proj 0) (Cn pr_div [Cn (pr2 $-) [proj 1; K 1]; K 2]) [n; r] − 1) DIV
        2 = pr_nblsr [n; (r − 1) DIV 2]’ suffices_by fs[] >> pop_assum kall_tac >>
  rw[pr_nblsr_def] >> Induct_on‘n’ >> simp[]
QED

Theorem primrec_pr_nblsr:
  primrec (pr_nblsr) 2
Proof
  simp[pr_nblsr_def,primrec_rules]
QED

Theorem recfn_pr_nblsr:
  recfn (SOME o pr_nblsr) 2
Proof
  irule primrec_recfn >> simp[pr_nblsr_def,primrec_rules]
QED





Definition pr_nblsnd0_def:
  pr_nblsnd0 =
  WFM (λf n. if (EVEN n ∧ n<>0) then (nfst (f ((n-2) DIV 2)) + 1) *, (nsnd (f ((n-2) DIV 2)))
             else 0 *, n)
End

Theorem n_sub2_div2:
  ¬((n-2) DIV 2 < n) ==> n=0
Proof
  rw[] >> ‘n <= (n-2) DIV 2’ by fs[] >> ‘2*n <= 2* ((n-2) DIV 2)’ by fs[] >>
  ‘2*n <= n-2’ by fs[X_LE_DIV] >> Cases_on‘n=0’ >> simp[]
QED

Theorem pr_nblsnd0_correct:
  pr_nblsnd0 [n] = (pr1 nblsnd0) [n]
Proof
  completeInduct_on‘n’ >>
  simp[Once pr_nblsnd0_def,Once nblsnd0_def,Once prnlistTheory.WFM_correct] >>
  rw[]
  >- (qmatch_abbrev_tac‘nfst a = nfst b’ >> ‘a=b’ suffices_by fs[] >>
      simp[Abbr‘a’,Abbr‘b’] >>
      ‘pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]’ by fs[] >> fs[] >>
      fs[Once pr_nblsnd0_def])
  >- (qmatch_abbrev_tac‘nsnd a = nsnd b’ >> ‘a=b’ suffices_by fs[] >>
      simp[Abbr‘a’,Abbr‘b’] >>
      ‘pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]’ by fs[] >> fs[] >>
      fs[Once pr_nblsnd0_def]) >>
  metis_tac[n_sub2_div2]
QED



Definition pr_pr_nblsnd0:
pr_pr_nblsnd0 = pr_cond (Cn pr_eq
                          [Cn pr_mod
                              [Cn succ
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair)
                          [Cn succ
                              [Cn (pr1 nfst)
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd)
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair)
                          [zerof;
                           Cn succ
                              [proj 0] ] )
End

Theorem primrec_restr_lem:
  primrec (λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) 3
Proof
  ‘(λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) = pr_cond (Cn pr_le [proj 2;proj 0]) (Cn (pr2 nel) [proj 2;proj 1]) (zerof)’ by (fs[FUN_EQ_THM] >> rw[prnlistTheory.restr_def]) >> rw[] >>
  irule primrec_pr_cond >> rw[primrec_rules]
QED

Theorem primrec_pr_nblsnd0:
  primrec pr_nblsnd0 1
Proof
  fs[pr_nblsnd0_def] >> irule prnlistTheory.primrec_WFM >> irule primrec_pr2 >> fs[] >>
  qexists_tac‘pr_cond (Cn pr_eq
                          [Cn pr_mod
                              [Cn succ
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair)
                          [Cn succ
                              [Cn (pr1 nfst)
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) )
                                       [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd)
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) )
                                  [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair)
                          [zerof;
                           Cn succ
                              [proj 0] ] )’ >> rw[]
  >- (irule primrec_pr_cond >> rw[primrec_rules] >> rpt (irule unary_recfnsTheory.primrec_Cn >>
      rw[primrec_rules]) >> fs[primrec_restr_lem] )
  >- (‘¬EVEN (SUC m)’ by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
  >- (‘EVEN (SUC m)’ by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
QED

Definition pr_nblsnd_def:
  pr_nblsnd = Cn pr_nblsr
                 [Cn succ [Cn (pr1 nfst)
                              [Cn pr_nblsnd0
                                  [proj 0]]];
                  Cn (pr1 nsnd)
                     [Cn pr_nblsnd0
                         [proj 0] ] ]
End

Theorem pr_nblsnd_correct:
  pr_nblsnd [n] = (pr1 nblsnd) [n]
Proof
  fs[pr_nblsnd_def,nblsnd_def] >>
  ‘nsnd (pr_nblsnd0 [n]) = nsnd (nblsnd0 n)’ by simp[pr_nblsnd0_correct] >>
  ‘SUC (nfst (pr_nblsnd0 [n])) = nfst (nblsnd0 n) + 1’ by simp[pr_nblsnd0_correct] >>
  simp[pr_nblsr_correct,Excl"nblsr_def"]
QED

Theorem primrec_nblsnd:
  primrec pr_nblsnd 1
Proof
  simp[pr_nblsnd_def] >>
  rpt (irule unary_recfnsTheory.primrec_Cn >>
       rw[primrec_rules,primrec_pr_nblsr,primrec_pr_nblsnd0])
QED

Theorem recfn_nblsnd:
  recfn (SOME o (pr1 nblsnd)) 1
Proof
  irule primrec_recfn >> irule primrecfnsTheory.primrec_pr1 >> qexists_tac‘pr_nblsnd’ >> rw[primrec_nblsnd,pr_nblsnd_correct]
QED

Theorem nblsnd_index:
  ∃i. ∀x. Phi i x = (SOME o (pr1 nblsnd)) [x]
Proof
  assume_tac recfn_nblsnd >> drule recfns_in_Phi >> rw[] >>
  qexists_tac‘i’ >> rw[] >>
  first_x_assum (qspec_then ‘[x]’ mp_tac) >> rw[]
QED

Theorem nblsnd_correct2[simp] =
  nblsnd_correct |> AP_TERM“bl2n” |> SIMP_RULE (srw_ss()) [Excl"bl2n_11"]


Definition nblft_def:
  nblft x 0 = 0n ∧
  nblft x (SUC n) = if x=0 then 0
                    else (if EVEN x then (2 + 2* (nblft ((x-2) DIV 2) n) )
                          else (1 + 2*(nblft ((x-1) DIV 2) n)))
End

Theorem nblft_zero[simp]:
  nblft 0 x = 0
Proof
  Induct_on‘x’ >> fs[nblft_def]
QED

Theorem n2bl_zero[simp]:
  n2bl 0 = []
Proof
  simp[Once num_to_bool_list_def]
QED


Theorem n2bl_2_EVEN_lem:
   T::n2bl (x) = n2bl (2 * x + 2)
Proof
  ‘EVEN (2 * x + 2)’ by
    (‘EVEN (2*(x+1))’ suffices_by rw[LEFT_ADD_DISTRIB] >> metis_tac[EVEN_DOUBLE]) >>
  ‘n2bl (2*x + 2) = T::(n2bl x)’ by (simp[Once num_to_bool_list_def]) >> metis_tac[]
QED

Theorem n2bl_1_ODD_lem:
   F::n2bl (x) = n2bl (2 * x + 1)
Proof
  ‘ODD (2 * x + 1)’ by
    (‘∃m. 2*x + 1 = SUC (2*m)’ by (qexists_tac‘x’ >> fs[]) >>
     metis_tac[ODD_EXISTS] ) >>
  ‘~EVEN (2 * x + 1)’ by fs[ODD_EVEN] >>
  ‘n2bl (2*x + 1) = F::(n2bl x)’ by (simp[Once num_to_bool_list_def]) >>
  metis_tac[]
QED

Theorem TAKE_n2bl:
  ∀n x. TAKE n (n2bl x) = n2bl (nblft x n)
Proof
  Induct_on‘n’ >> simp[] >> rw[]  >>
  simp[nblft_def] >>rw[] >>
  simp[Once num_to_bool_list_def] >> rw[n2bl_1_ODD_lem,n2bl_2_EVEN_lem]
QED

Definition nblfst_def:
  nblfst x = (let nr = nblsnd0 x;n=nfst nr;r = nsnd nr in nblft (nblsr r (1)) n)
End

Theorem DROP_bl2n:
  ∀x n. DROP n x = n2bl (nblsr (bl2n x) n)
Proof
  rw[] >>
  ‘DROP n (n2bl (bl2n x)) = n2bl (nblsr (bl2n (n2bl (bl2n x))) n)’ suffices_by
   (rw[] >> fs[bool_num_inv]) >>
  metis_tac[DROP_n2bl,bool_num_inv]
QED

Theorem nblfst_correct[simp]:
  nblfst (bl2n (pair a b)) = bl2n a
Proof
  ‘n2bl (nblfst (bl2n (pair a b))) = a’ suffices_by
    (rw[] >> ‘bl2n (n2bl (nblfst (bl2n (pair a b)))) = bl2n a’ by fs[] >>
     metis_tac[bool_num_inv]) >>
  fs[nblfst_def,nblsnd_def,GSYM TAKE_n2bl,pair_def,bar_def] >>
  ‘TAKE (nfst (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b) ))))
        (n2bl
          (nblsr(nsnd (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))))) 1))
      = a’ suffices_by fs[] >>
  ‘nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))) =
   LENGTH a ⊗ bl2n ([F] ++ (a ++ b))’
     by metis_tac[nblsnd0_correct] >> fs[rich_listTheory.TAKE_LENGTH_APPEND] >>
  simp[GSYM DROP_bl2n] >> fs[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Definition lam_nblft_def:
  lam_nblft = LAM "x" (
    LAM "y" (
      VAR "y"
       @@ (K @@ church 0)
       @@ (LAM "r" (
             LAM "x'" (
               cis_zero @@ VAR "x'"
                        @@ church 0
                        @@ (cis_zero
                             @@ (cmod @@ VAR "x'" @@ church 2)
                             @@ (cplus @@ church 2
                                       @@ (cmult @@ church 2
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'"
                                                                                 @@ church 2)
                                                                      @@ church 2) )  ) )
                             @@ (cplus @@ church 1
                                       @@ (cmult @@ church 2
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'"
                                                                                 @@ church 1)
                                                                      @@ church 2) )  ) )  ) )))
       @@ VAR "x"
    )
  )
End

Theorem FV_lam_nblft:
  FV lam_nblft = {}
Proof
  simp[lam_nblft_def,EXTENSION]
QED

Theorem lam_nblft_equiv = brackabs.brackabs_equiv [] lam_nblft_def

Theorem lam_nblft_behaviour:
   ∀x y. lam_nblft @@ church x @@ church y == church (nblft x y)
Proof
  Induct_on‘y’ >> simp_tac (bsrw_ss()) [lam_nblft_equiv,nblft_def] >> rw[] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >> fs[EVEN_MOD2] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >>
  full_simp_tac (bsrw_ss()) [lam_nblft_equiv] >> simp[]
QED

Theorem lam_nblft_phi:
  Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) (m *, n) =
  SOME (nblft m n)
Proof
  simp[Phi_def] >>
  simp_tac (bsrw_ss()) [lam_nblft_behaviour,normal_orderTheory.bnf_bnf_of]
QED

Theorem nblft_phiii:
  ∀z1 z2. rec2 (λx y. SOME (nblft x y)) [z1;z2] =
  recCn
    (recCn
       recPhi
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)] [z1;z2]
Proof
  rpt strip_tac >> simp[Excl"fromTerm_def",recPhi_correct,recCn_def,lam_nblft_phi ]
QED

Theorem nblft_phi_lem:
rec2 (λx y. SOME (nblft x y)) =
  recCn
    (recCn
       recPhi
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)]
Proof
  rw[FUN_EQ_THM,Excl"fromTerm_def"] >> Cases_on‘x’ >> rw[Excl"fromTerm_def"]
  >-(simp[recCn_def,Excl"fromTerm_def"] >> ‘SOME 0 =
     Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd))) (0 *, 0)’
       suffices_by simp[Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >>
  Cases_on‘t’ >> rw[Excl"fromTerm_def"]
  >-(simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >>
  simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]
QED

Theorem recfn_some_num:
  recfn (λx. SOME (a:num)) 1
Proof
  ‘(λ(x:num list). SOME a) = K (SOME a)’ by (simp[FUN_EQ_THM,combinTheory.K_THM]) >>
  ‘recfn (K (SOME a)) 1’ suffices_by simp[] >> simp[recfn_K]
QED

Theorem recfn_nblfst:
  recfn (rec1 (SOME o nblfst)) 1
Proof
  irule recfn_rec1 >> fs[nblfst_def] >>
  qexists_tac‘recCn (rec2 (λx y. SOME (nblft x y) )) [SOME o Cn pr_nblsr [K 1;Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 0]] ];
                    SOME o Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 0]] ]’ >> rw[]
  >- (irule recfnCn >> rw[recfn_rules]
      >- (irule primrec_recfn >>
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]) )
      >- (irule primrec_recfn >>
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]))
      >- (simp[nblft_phi_lem,Excl"fromTerm_def"] >> irule recfnCn >>
          rw[recfn_rules,Excl"fromTerm_def"]
          >- (irule primrec_recfn >> simp[primrec_npair]) >> irule recfnCn >>
         rw[recfn_rules,Excl"fromTerm_def"] >> simp[recfn_some_num] )  )
  >- (simp[recCn_def] >>  simp[pr_nblsr_correct,Excl"nblsr_def",ADD1,pr_nblsnd0_correct])
QED

val nblfst_i_def = new_specification(
  "nblfst_i_def", ["nblfst_i"],
  MATCH_MP unary_rec_fns_phi recfn_nblfst
);

Theorem nblfst_bar[simp]:
  nblfst (bl2n (bar x)) = bl2n x
Proof
  assume_tac (GEN_ALL nblfst_correct) >>
  full_simp_tac bool_ss [pair_def] >>
  metis_tac [APPEND_NIL]
QED

Definition pfPhi_def:
  pfPhi i j = if prefix_free { n2bl a | Phi i a <> NONE } then Phi i j
              else NONE
End

Definition checkbar_def:
  checkbar =
  minimise (λx. if proj 0 x = nblfst (proj 1 x) ∧
                   nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
                then
                  SOME 0
                else SOME 1)
End

Theorem EXISTS_bar[simp]:
  EXISTS ($~ o $= T) (bar x)
Proof
  simp[bar_def]
QED

Theorem nblsnd0_correct' =
  nblsnd0_correct |> Q.INST [‘x’ |-> ‘a ++ b’] |> SIMP_RULE (srw_ss()) []

Theorem checkbar_correct:
  checkbar [bl2n (pair a b)] = if b = [] then SOME (bl2n a) else NONE
Proof
  reverse (rw[checkbar_def, minimise_thm] >>
           DEEP_INTRO_TAC optionTheory.some_intro >> rw[pair_def])
  >- (fs[nblsnd0_correct', bar_def, ADD1] >> Cases_on ‘b’ >> fs[]) >>
  qexists_tac‘bl2n a’ >> rw[] >>
  fs[nblsnd0_correct, bar_def, ADD1]
QED

Theorem checkbar_correct'[simp] =
  checkbar_correct |> Q.INST [‘b’ |-> ‘[]’] |> SIMP_RULE (srw_ss()) [pair_def]

Definition recfn_cond_def:
  recfn_cond P f g = recCn
        (recCn (SOME o pr2 $+)
           [recCn (SOME o pr2 $* ) [SOME o proj 0; SOME o proj 1];
            recCn (SOME o pr2 $* ) [recCn (SOME o pr2 $-) [SOME o K 1; SOME o proj 0]; SOME o proj 2]]) [P; f; g]
End

Theorem recfn_recfn_cond:
  recfn P n ∧ recfn f n ∧ recfn g n ⇒ recfn (recfn_cond P f g) n
Proof
  rw[recfn_cond_def,GSYM (CONJUNCT2 combinTheory.K_o_THM),Excl"K_o_THM"] >> rpt (irule recfnCn >> rw[recfn_rules,GSYM (CONJUNCT2 combinTheory.K_o_THM),Excl"K_o_THM"]) >> irule primrec_recfn >> simp[]
QED

Theorem recfn_checkbar_lem1:
  recfn (λx. if proj 0 x = nblfst (proj 1 x) ∧
                nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
             then
                SOME 0
             else SOME 1) 2
Proof
  ‘(λx. if proj 0 x = nblfst (proj 1 x) ∧
                nfst (nblsnd0 (proj 1 x)) + 1 = ℓ (nsnd (nblsnd0 (proj 1 x)))
        then SOME 0n
        else SOME 1) =
   recfn_cond (
     recCn (SOME o pr_eq) [
       SOME o proj 0;
       recCn (rec1 (SOME o nblfst)) [SOME o proj 1]
     ]
   ) (
     SOME o pr_cond (
       Cn pr_eq [
         Cn succ [Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 1]]];
         Cn (pr1 ℓ) [Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 1]]]
       ]
     ) (K 0) (K 1)
   )
   (K (SOME 1))’
     by (rw[FUN_EQ_THM, recfn_cond_def,recCn_def, pr_nblsnd_correct] >>
         rw[] >> fs[ADD1, pr_nblsnd0_correct] >>
         Cases_on ‘proj 0 x = nblfst (proj 1 x)’ >> simp[]) >>
  rw[] >>
  irule recfn_recfn_cond >> rw[]
  >- (irule recfnCn >> rw[recfn_rules, recfnCn, recfn_nblfst, primrec_recfn])
  >- (irule primrec_recfn >>
      rpt ((irule primrec_Cn ORELSE irule primrec_pr_cond) >>
           rw[primrec_rules, primrec_nblsnd, primrec_pr_nblsnd0,primrec_ell]))>>
  ‘(K (SOME 1) : num list -> num option) = SOME o K 1’ by simp[] >>
  pop_assum SUBST1_TAC >> irule primrec_recfn >> simp[]
QED

Theorem recfn_checkbar:
  recfn checkbar 1
Proof
 fs[checkbar_def] >> irule (last (CONJUNCTS recfn_rules)) >> rw[] >>
 simp[recfn_checkbar_lem1]
QED

val checkbar_i_def =  new_specification (
  "checkbar_i_def",["checkbar_i"],
  MATCH_MP unary_rec_fns_phi recfn_checkbar
);

Theorem bl2n_onto:
  !x. ?y. x = bl2n y
Proof
  metis_tac[bool_num_inv]
QED

Theorem nblsnd0_Tpow[simp]:
  nblsnd0 (bl2n (Tpow n)) = n ⊗ 0
Proof
  Induct_on ‘n’ >>
  simp[Once nblsnd0_def, tpow_suc, bool_list_to_num_def, EVEN_MULT, EVEN_ADD]
QED

Theorem checkbar_EQ_NONE[simp]:
  checkbar [x] = NONE ⇔ ∀y. x ≠ bl2n (bar y)
Proof
  rw[checkbar_def, minimise_thm] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[]
  >- (qspec_then ‘x’ strip_assume_tac bl2n_onto >> rw[] >> fs[] >>
      rename [‘bl2n bl’] >>
      Cases_on ‘MEM F bl’
      >- (fs[Once MEM_SPLIT_APPEND_first] >>
          ‘∃n. pfx = Tpow n’
            by (simp[Tpow_def] >>
                qexists_tac‘LENGTH pfx’ >> rw[LIST_EQ_REWRITE] >>
                CCONTR_TAC >> ‘EL x pfx = F’ by simp[] >>
                Q.UNDISCH_THEN ‘~MEM F pfx’ MP_TAC >> simp[MEM_EL] >>
                metis_tac[]) >>
          rw[] >> fs[nblsnd0_correct, ADD1] >>
          simp[bar_def]) >>
      ‘∃n. bl = Tpow n’
         by (simp[Tpow_def] >>
             qexists_tac‘LENGTH bl’ >> rw[LIST_EQ_REWRITE] >>
             CCONTR_TAC >> ‘EL x bl = F’ by simp[] >>
             Q.UNDISCH_THEN ‘~MEM F bl’ MP_TAC >> simp[MEM_EL] >>
             metis_tac[]) >>
      rw[] >> fs[]) >>
  fs[AllCaseEqs()] >>
  strip_tac >> rw[] >> fs[bar_def, nblsnd0_correct] >> rfs[]
QED

Theorem pf_machines_exist:
  ∀i. ∃j. ∀a. pfPhi j (bl2n (bar a)) = Phi i (bl2n a) ∧ ((∀b. a <> bar b) ==> pfPhi j (bl2n a) = NONE)
Proof
  simp[pfPhi_def] >> gen_tac >> qexists_tac‘i o checkbar_i’ >>
  simp[computable_composition_def, checkbar_i_def] >> rw[] >>
  fs[prefix_free_def] >> rw[] >> fs[]
QED

Definition univ_mach_def:
  univ_mach U <=>
     (∀i x y.
        U (pair x (pair i y)) =
        on2bl (pfPhi (bl2n i) (bl2n (pair x y)))) ∧
     ∀m. (∀i x y. m <> pair x (pair i y)) ==> U m = NONE
End

Theorem univ_mach_pf:
  univ_mach U ⇒ prefix_machine U
Proof
  rw[univ_mach_def, prefix_machine_def] >>
  qexists_tac‘{ x | ∃y. U x = SOME y}’ >> simp[] >>
  rw[prefix_free_def] >> strip_tac >>
  rename [‘a1 ≺ a2’, ‘U a1 = SOME r1’, ‘U a2 = SOME r2’] >>
  ‘(∃x y z. a1 = pair x (pair y z)) ∧
   (∃u v w. a2 = pair u (pair v w))’
     by metis_tac[optionTheory.NOT_NONE_SOME] >> rw[] >>
  fs[prefix_def, pair_def] >>
  reverse (Cases_on ‘x = u’) >>
  full_simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPENDS,GSYM APPEND_ASSOC]
  >- (drule rich_listTheory.IS_PREFIX_APPEND1 >> simp[]) >>
  reverse (Cases_on ‘y = v’) >>
  full_simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPENDS,GSYM APPEND_ASSOC]
  >- (drule rich_listTheory.IS_PREFIX_APPEND1 >> simp[]) >> rw[] >>
  rfs[on2bl_SOME, pfPhi_def] >> rw[] >>
  rename [‘x ≼ y’, ‘Phi (bl2n M) (bl2n (bar a1 ++ x)) = SOME r1’,
          ‘Phi (bl2n M) (bl2n (bar a1 ++ y)) = SOME r2’] >>
  ‘bar a1 ++ x ∈ {n2bl a | Phi (bl2n M) a ≠ NONE} ∧
   bar a1 ++ y ∈ {n2bl a | Phi (bl2n M) a ≠ NONE}’
    by (simp[] >> metis_tac[num_bool_inv, optionTheory.NOT_NONE_SOME]) >>
  ‘¬(bar a1 ++ x ≺ bar a1 ++ y)’ by metis_tac[prefix_free_def] >>
  fs[prefix_def]
QED



Theorem univ_mach_nonempty[simp]:
  univ_mach U ⇒ ∀x. ∃y. U y = SOME x
Proof
  rw[univ_mach_def] >>
  ‘recfn (SOME o (K (bl2n x))) 1’ by (irule primrec_recfn >> fs[primrec_rules]) >>
  ‘∃i. ∀y. Phi i y = (SOME o (K (bl2n x))) [y]’ by (irule unary_rec_fns_phi >> fs[]) >> 
  ‘∃j. ∀a. pfPhi j (bl2n (bar a)) = Phi i (bl2n a)’ by metis_tac[pf_machines_exist] >>
  qexists_tac ‘pair x (pair (n2bl j) [])’ >>
  simp[on2bl_SOME,pair_def]
QED

Theorem univ_mach_nonempty'[simp]:
  univ_mach U ⇒ ∀x. (∀y. U y ≠ SOME x) = F
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘x’ strip_assume_tac) univ_mach_nonempty >>
  simp[]
QED

Theorem pfPhi_SOME:
  pfPhi a b = SOME c ==> prefix_free {n2bl i | Phi a i ≠ NONE} ∧ Phi a b = SOME c
Proof
  rw[pfPhi_def]
QED


Theorem pf_composition:
  prefix_free {n2bl p | Phi a p ≠ NONE} ∧ prefix_free {n2bl p | Phi b p ≠ NONE} ==>
    ∀c. pfPhi (a o b) c = Phi (a o b) c
Proof
  rw[pfPhi_def] >> rw[] >> fs[prefix_free_def] >>
  rename[‘p1≺p2’,‘p1 = n2bl n1’, ‘p2 = n2bl n2’] >>
  fs[computable_composition_def] >>
  ‘(∃p. p1 = n2bl p ∧ Phi b p ≠ NONE) ∧
            (∃p. p2 = n2bl p ∧ Phi b p ≠ NONE) ⇒
            ~(p1 ≺ p2)’ by metis_tac[] >> metis_tac[]
QED



Definition pffi_def:
 pffi i = prefix_free {n2bl p | Phi i p <> NONE}
End

Theorem pffi_correct:
  pffi i ==> pfPhi i = Phi i
Proof
  rw[pffi_def,FUN_EQ_THM,pfPhi_def]
QED

val nblsnd_i_def =  new_specification (
  "nblsnd_i_def",["nblsnd_i"],
  MATCH_MP unary_rec_fns_phi recfn_nblsnd
);

Theorem bar_decomp:
  (∃n x. p1 = bl2n (Tpow n ++ [F] ++ x)) ∨ (∃m. p1 = bl2n (Tpow m) )
Proof
  Cases_on ‘MEM F (n2bl p1)’
      >- (fs[Once MEM_SPLIT_APPEND_first] >>
          ‘∃n. pfx = Tpow n’
            by (simp[Tpow_def] >>
                qexists_tac‘LENGTH pfx’ >> rw[LIST_EQ_REWRITE] >>
                CCONTR_TAC >> ‘EL x pfx = F’ by simp[] >>
                Q.UNDISCH_THEN ‘~MEM F pfx’ MP_TAC >> simp[MEM_EL] >>
                metis_tac[]) >>
          Cases_on‘(∃n x. p1 = bl2n (Tpow n ++ [F] ++ x))’ >> fs[] >>
          ‘p1 <> (bl2n (Tpow n ++ [F] ++ sfx))’ by fs[] >>
          ‘bl2n (n2bl p1) = bl2n (Tpow n ++ [F] ++ sfx)’ by fs[] >> metis_tac[bool_num_inv] ) >>
      ‘∃n. (n2bl p1) = Tpow n’
         by (simp[Tpow_def] >>
             qexists_tac‘LENGTH (n2bl p1)’ >> rw[LIST_EQ_REWRITE] >>
             CCONTR_TAC >> ‘EL x (n2bl p1) = F’ by simp[] >>
             Q.UNDISCH_THEN ‘~MEM F (n2bl p1)’ MP_TAC >> simp[MEM_EL] >>
             metis_tac[]) >> Cases_on‘∃m. p1 = bl2n (Tpow m)’ >> fs[] >>
      ‘bl2n (n2bl p1) = bl2n (Tpow n)’ by fs[] >> metis_tac[bool_num_inv]
QED

Theorem n2bl_inj[simp]:
  n2bl x = n2bl y <=> x=y
Proof
  metis_tac[bool_num_inv]
QED

Theorem n2bl_eq_CONS:
  n2bl n = h::t <=> ∃m. n = 2 * m + (if h then 2 else 1) ∧ n2bl m = t
Proof
  Cases_on‘n’ >> simp[Once num_to_bool_list_def,AllCaseEqs ()] >> rw[EQ_IMP_THM] >>simp[] >>
  pop_assum MP_TAC >> intLib.ARITH_TAC
QED

Theorem nblsr_correct' = GSYM DROP_bl2n |> SPEC_ALL |> Q.AP_TERM ‘bl2n’ |> SIMP_RULE (srw_ss()) [Excl"bl2n_11"]

                
Theorem nblsnd_behav:
  ∀p1 x cr. (nblsnd p1) = bl2n (bar x) ==> (nblsnd (bl2n ((n2bl p1) ++ cr)) ) = bl2n ( bar x ++ cr)
Proof
  GEN_TAC >> strip_assume_tac bar_decomp >>
  rw[nblsnd_def,nblsnd0_correct,nblsnd0_correct',nblsnd0_Tpow,nblsr_correct',
     rich_listTheory.DROP_APPEND] 
  >- (‘n <= LENGTH x’ suffices_by (strip_tac >> ‘n - LENGTH x = 0’ by simp[] >> simp[]) >>
  CCONTR_TAC >> ‘LENGTH x < n’ by fs[] >> ‘n >= LENGTH x’ by fs[] >>
  ‘DROP n x = []’ by fs[DROP_NIL] >> ‘bar x' = []’ by fs[] >> fs[bar_def]) >>
  ‘n2bl 0 = n2bl (bl2n (bar x))’ by fs[] >>
  ‘[] = bar x’ by metis_tac[num_bool_inv,n2bl_zero] >> fs[bar_def]
QED

Theorem pffi_checkbar:
  pffi (checkbar_i o nblsnd_i)
Proof
  fs[pffi_def,computable_composition_def,prefix_free_def] >> rw[] >> rename[‘~(n2bl p1 ≺ n2bl p2)’] >>
  ‘(∃f. Phi nblsnd_i p1 = SOME f) ∧ ∃g. Phi nblsnd_i p2 = SOME g’ by
    (rw[] >>metis_tac[optionTheory.option_CASES]) >> 
  strip_tac >> fs[nblsnd_i_def,checkbar_i_def] >>  rw[] >>
  ‘∃cr. n2bl p2  = n2bl p1 ++ cr’ by fs[prefix_append] >>
  ‘(nblsnd (bl2n ((n2bl p1) ++ cr)) ) = bl2n ( bar y ++ cr)’ by fs[nblsnd_behav] >>
  ‘bl2n (n2bl p2) = bl2n (n2bl p1 ++ cr)’ by fs[] >> fs[Excl"bl2n_11"] >>
  ‘bl2n (bar y') =  bl2n (bar y ++ cr)’ by metis_tac[] >>
  ‘bar y' = bay y ++ cr’ by fs[] >> fs[bar_def]
QED

Theorem pffi_comp:
  pffi g ==> pffi (f o g)
Proof
  rw[pffi_def,computable_composition_def] >>
  ‘{n2bl p | Phi g p ≠ NONE ∧ ∀x. Phi g p = SOME x ⇒ Phi f x ≠ NONE} ⊆ 
    {n2bl p | Phi g p ≠ NONE}’ by (rw[SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[prefix_free_subset]
QED



        
Theorem univ_mach_pair_nonempty:
   univ_mach U  ⇒ {p | U (pair y p) = SOME x} ≠ ∅
Proof
  rw[EXTENSION] >>
  ‘∃a. U a = SOME x’ by simp[] >>
  fs[univ_mach_def] >>
  ‘∃i b c. a = pair b (pair i c)’
    by metis_tac[optionTheory.NOT_NONE_SOME] >>
  rw[] >> rfs[on2bl_SOME] >>
  
  qexists_tac ‘pair (n2bl (bl2n i o (checkbar_i o nblsnd_i ))) (bar (pair b c))’ >>
  fs[computable_composition_def, on2bl_SOME, PULL_EXISTS] >>
  ‘pffi (bl2n i ∘ (checkbar_i ∘ nblsnd_i))’ by (assume_tac pffi_checkbar >> simp[pffi_comp]) >>
  fs[pffi_correct] >>
  fs[computable_composition_def, on2bl_SOME, PULL_EXISTS,checkbar_i_def,nblsnd_i_def] >>
  fs[pfPhi_def]
QED

Theorem univ_mach_pair_nonempty'[simp] =
  SIMP_RULE (srw_ss()) [EXTENSION] univ_mach_pair_nonempty

Definition rUMibl_def:
  rUMibl = recCn recPhi
                [recCn (SOME o (pr1 nblfst))
                       [SOME o proj 0];
                 recCn (SOME o (pr1 nblsnd))
                       [SOME o proj 0]]
End

Theorem rUMibl_correct:
  rUMibl [bl2n (pair a b)] = Phi (bl2n a) (bl2n b)
Proof
  fs[rUMibl_def,rec2_def,recCn_def,nblfst_correct,nblsnd_correct2]
QED

Theorem rec1_pr1:
  SOME o pr1 f = rec1 (SOME o f)
Proof
  simp[FUN_EQ_THM] >> Cases_on‘x’ >> rw[rec1_def,pr1_def]
QED

Theorem rUMibl_recfn:
  recfn rUMibl 1
Proof
  fs[rUMibl_def] >> irule recfnCn >> rw[] >> irule recfnCn >>
  rw[recfn_rules,recfn_nblsnd,recfn_nblfst] >>
  ‘(SOME ∘ pr1 nblfst) = rec1 (SOME o nblfst)’ suffices_by fs[recfn_nblfst] >>
  fs[rec1_pr1]
QED

Theorem rUMibl_index:
  ∃i. ∀x. Phi i x = rUMibl [x]
Proof
  fs[unary_rec_fns_phi,rUMibl_recfn]
QED

Theorem CKC_thm[simp]:
  univ_mach U ⇒ CKC U x y = MIN_SET {LENGTH p | U (pair y p) = SOME x}
Proof
  simp[CKC_def, cond_core_complexity_def, univ_mach_pair_nonempty]
QED

Theorem KC_thm[simp]:
  univ_mach U ⇒ KC U x = MIN_SET {LENGTH p | U p = SOME x}
Proof
  simp[KC_def, core_complexity_def, EXTENSION]
QED

(* Up to here! *)

Theorem extra_information1:
  univ_mach U ==> ∃c. ∀x y. (CKC U x y) <= (KC U x) + c
Proof
  rw[] >>
  qx_choose_then ‘nblsnd_i’ strip_assume_tac nblsnd_index >>
  qx_choose_then ‘rUMi’ strip_assume_tac rUMibl_index >>
  qabbrev_tac‘j = rUMi o nblsnd_i’ >>
  qexists_tac‘2 * ℓ j + 1’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_mach_pair_nonempty] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >> fs[PULL_EXISTS] >>
  rename [‘univ_mach U’, ‘U p2 = SOME x’] >>
  fs[univ_mach_def] >>
  ‘∃a i b. p2 = pair a (pair i b)’
     by metis_tac[optionTheory.NOT_SOME_NONE] >> rw[] >>
  qabbrev_tac ‘ARG2 = pair (n2bl j) ((pair i (pair a b)))’ >>
  ‘U (pair y ARG2) = SOME x’
    by (rfs[Abbr‘ARG2’, Abbr‘j’, computable_composition_def, rUMibl_correct,on2bl_SOME] >>
        qexists_tac‘z’ >> rw[] >> ‘prefix_free {n2bl p | Phi (bl2n i) p ≠ NONE}’ by
          metis_tac[pfPhi_SOME] >> simp[pfPhi_def] >> rw[]
    >- (simp[computable_composition_def] >> )  >> fs[computable_composition_def,rUMibl_correct,pfPhi_def] )
  last_x_assum drule >> simp[Abbr‘ARG2’, LEFT_ADD_DISTRIB]
QED




Theorem primrec_nblconcat[simp]:
  primrec (pr2 nblconcat) 2
Proof
  irule primrec_pr2 >> fs[nblconcat_def] >>
  qexists_tac
  ‘Cn (pr2 $+ )
      [proj 0 ;
       Cn (pr2 $* )
          [proj 1 ;
           Cn (λl. FUNPOW (λx. 2*x ) ((proj 0) l) ((K 1n) l)  )
              [Cn (pr1 ℓ )
                  [proj 0] ] ] ] ’ >> rw[]
  >- (rpt (irule unary_recfnsTheory.primrec_Cn >>
           rw[primrec_pr_mult,primrec_pr_add,primrec_rules,primrec_ell]) >>
      HO_MATCH_MP_TAC primrec_FUNPOW >> rw[]
      >- (irule primrec_pr1 >> qexists_tac‘Cn (pr2 $*) [K 2;proj 0]’ >> simp[primrec_rules])
      >- (‘(λ(l:num list). 1n) = K 1’ suffices_by simp[] >> simp[FUN_EQ_THM] ) >>
      simp_tac (srw_ss()++boolSimps.ETA_ss) [primrec_rules] ) >>
  Q.SPEC_TAC (‘ℓ m’,‘k’) >> Induct >> simp[FUNPOW_SUC,EXP]
QED



Definition nblpair_to_concat_def:
  nblpair_to_concat = recCn (SOME o pr2 nblconcat) [rec1 (SOME o nblfst);SOME o pr1 nblsnd]
End

Theorem recfn_nblpair_to_concat:
  recfn nblpair_to_concat 1
Proof
  simp[nblpair_to_concat_def] >> irule recfnCn >> rw[recfn_nblsnd,recfn_nblfst,primrec_recfn]
QED

Theorem nblpair_to_concat_correct[simp]:
  nblpair_to_concat [bl2n (pair x y)] = SOME (bl2n (x++y))
Proof
  simp[nblpair_to_concat_def,recCn_def,nblfst_correct,nblsnd_correct2]
QED

val nblpc_i_def =  new_specification ("nblpc_i_def",["nblpc_i"],MATCH_MP unary_rec_fns_phi recfn_nblpair_to_concat)


Definition comp_machine_t_def:
  comp_machine_t =
  LAM "ijx" (
    LAM "ij" (
      LAM "i" (
        LAM "j" (
          LAM "x" (
            cbnf_ofk
              @@ (LAM "r" (UM @@ (cnpair @@ (cnfst @@ VAR "ij")
                                         @@ (cforce_num @@ VAR "r"))))
              @@ (cdAPP @@ (cnumdB @@ (cnsnd @@ VAR "ij"))
                        @@ (cchurch @@ VAR "x"))
          ) @@ (cnsnd @@ VAR "ijx")
        ) @@ (cnsnd @@ VAR "ij")
      ) @@ (cnfst @@ VAR "ij")
    ) @@ (cnfst @@ VAR "ijx")
  )
End

Theorem FV_comp_machine_t[simp]:
  FV comp_machine_t = ∅
Proof
  simp[comp_machine_t_def, EXTENSION]
QED

Triviality comp_machine_equiv = brackabs.brackabs_equiv [] comp_machine_t_def

Theorem comp_machine_t_behaviour_good:
  Phi j x = SOME n ∧ Phi i n = SOME r ⇒
  (comp_machine_t @@ church ((i ⊗ j) ⊗ x) == church r)
Proof
  strip_tac >>
  Q.UNDISCH_THEN ‘Phi j x = SOME n’ mp_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv, Phi_def] >> strip_tac >>
  drule cbnf_of_works1 >>
  simp[] >> simp_tac (bsrw_ss())[] >> disch_then (K ALL_TAC) >>
  drule PhiSOME_UM_I >> rw[] >> asm_simp_tac(bsrw_ss()) []
QED

Theorem comp_machine_t_behaviour_bad1:
  Phi j x = NONE ⇒
  bnf_of (comp_machine_t @@ church ((i ⊗ j) ⊗ x)) = NONE
Proof
  strip_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv] >>
  simp[PhiNONE_cbnf_ofk]
QED

Theorem comp_machine_t_behaviour_bad2:
  Phi j x = SOME n ∧ Phi i n = NONE ⇒
  bnf_of (comp_machine_t @@ church ((i ⊗ j) ⊗ x)) = NONE
Proof
  strip_tac >>
  Q.UNDISCH_THEN ‘Phi j x = SOME n’ mp_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv, Phi_def] >> strip_tac >>
  drule cbnf_of_works1 >> simp_tac (bsrw_ss()) [] >> disch_then (K ALL_TAC) >>
  fs[PhiNONE_UM, normal_orderTheory.bnf_of_NONE]
QED

Definition comp_machine_i_def:
  comp_machine_i = dBnum (fromTerm comp_machine_t)
End

Theorem Phi_comp:
  Phi comp_machine_i ((i ⊗ j) ⊗ x) = Phi (i o j) x
Proof
  simp[computable_composition_def] >>
  simp[SimpLHS, Phi_def, comp_machine_i_def] >>
  Cases_on ‘Phi j x’
  >- simp[comp_machine_t_behaviour_bad1] >>
  rename [‘Phi j x = SOME r’] >>
  Cases_on ‘Phi i r’
  >- (drule_all comp_machine_t_behaviour_bad2 >> simp[]) >>
  drule_all comp_machine_t_behaviour_good >>
  asm_simp_tac (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]
QED

Definition comp_machine_bl:
  comp_machine_bl =
    recCn recPhi [
      SOME o K comp_machine_i;
      recCn (SOME o pr2 $*,) [
        recCn (SOME o pr2 $*,) [
          recCn (rec1 (SOME o nblfst)) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ];
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0]
      ]
    ]
End

Theorem recfn_comp_machine_bl[simp]:
  recfn comp_machine_bl 1
Proof
  simp[comp_machine_bl] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst] >> rw[])
QED

Theorem comp_machine_bl_correct:
  comp_machine_bl [bl2n (pair (pair i j) x)] =
  Phi (bl2n i o bl2n j) (bl2n x)
Proof
  simp[comp_machine_bl, recCn_def, Phi_comp]
QED

val comp_bli = new_specification (
  "comp_bli", ["comp_bli"],
  MATCH_MP unary_rec_fns_phi recfn_comp_machine_bl
);

(* takes (pair (pair f (pair g1 g2)) x) and computes f (g1 x) (g2 x)
   as f, g1 and g2 are all indexes, running them actually involves a call
   to recPhi.
*)
Definition nbl_comp2_def:
  nbl_comp2 =
  recCn recPhi [
    recCn (rec1 (SOME o nblfst)) [
      recCn (rec1 (SOME o nblfst)) [SOME o proj 0] (* f is fst(fst arg) *)
    ];
    recCn (SOME o pr2 $*,) [ (* g1 x ⊗  g2 x *)
      recCn recPhi [ (* Phi g1 x *)
        recCn (rec1 (SOME o nblfst)) [
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0] (* x is snd (arg) *)
      ];
      recCn recPhi [ (* Phi g2 x *)
        recCn (SOME o pr1 nblsnd) [
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0] (* x is snd (arg) *)
      ]
    ]
  ]
End

Theorem recfn_nbl_comp2:
  recfn nbl_comp2 1
Proof
  simp[nbl_comp2_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst] >> rw[])
QED

Theorem nbl_comp2_correct:
  nbl_comp2 [bl2n (pair (pair f (pair g1 g2)) x)] =
  do
    r1 <- Phi (bl2n g1) (bl2n x);
    r2 <- Phi (bl2n g2) (bl2n x);
    Phi (bl2n f) (r1 ⊗ r2);
  od
Proof
  simp[nbl_comp2_def, recCn_def] >>
  Cases_on ‘Phi (bl2n g1) (bl2n x)’ >> simp[] >>
  Cases_on ‘Phi (bl2n g2) (bl2n x)’ >> simp[]
QED

val nbl_comp2_i_def =
new_specification ("nbl_comp2_i_def", ["nbl_comp2_i"],
                   MATCH_MP unary_rec_fns_phi recfn_nbl_comp2)

Theorem subadditivity1:
  univ_mach U ==> ∃c. ∀x y. KC U (x++y) <= KC U (pair x y) + c
Proof
  rw[] >>
  assume_tac nblpc_i_def >>
  qexists_tac‘4 * ℓ nblpc_i + 2 * ℓ comp_bli + 3’ >>
  rw[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >> fs[PULL_EXISTS] >>
  rename[‘U pp = SOME (pair x y)’] >> fs[univ_mach_def] >>
  ‘∃pi a b. pp = pair a (plist bar (pi::b))’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblpc_i) pi) (plist bar (n2bl comp_bli :: a :: b))
  ’ >>
  ‘U ARG = SOME (x++y)’
     by (simp[Abbr‘ARG’, comp_bli, Excl "plist_def"] >>
         ‘z = bl2n (pair x y)’ by simp[] >>
         rw[comp_machine_bl_correct, on2bl_SOME, computable_composition_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED

Theorem extra_information2:
  univ_mach U ⇒ ∃c. ∀x y. KC U x ≤ KC U (pair x y) + c
Proof
  rw[] >>
  qexists_tac‘4 * ℓ nblfst_i + 2 * ℓ comp_bli + 5’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  rename[‘U pp = SOME (pair x y)’] >>
  fs[univ_mach_def, PULL_EXISTS] >>
  ‘∃a i c. pp = pair a (plist bar (i::c))’
      by metis_tac[optionTheory.NOT_SOME_NONE] >> rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblfst_i) i) (plist bar (n2bl comp_bli::a::c))
  ’ >>
  ‘U ARG = SOME x’ by
    (simp[computable_composition_def, Abbr‘ARG’, comp_bli, on2bl_SOME,
          comp_machine_bl_correct, plist_def] >>
     ‘z = bl2n (pair x y)’ by simp[] >>
     rw[nblfst_i_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’, LEFT_ADD_DISTRIB]
QED

Theorem subadditivity3:
  univ_mach U ==> ∃c. ∀x y. KC U x + CKC U y x <= KC U x + KC U y + c
Proof
  metis_tac[ADD_ASSOC,LE_ADD_LCANCEL, extra_information1]
QED

Definition nblTpow_def:
  nblTpow = Cn (pr2 $-) [
    (λl. FUNPOW (λx. 2*x ) (Cn succ [proj 0] l) ((K 1n) l));
    K 2
  ]
End

Theorem nblTpow_compute:
  nblTpow [n] = 2**(n+1) - 2
Proof
  Induct_on‘n’ >> fs[nblTpow_def,FUNPOW_SUC,EXP,GSYM ADD1] >>
  ‘2*FUNPOW (λx. 2 * x) n 1 -2 + 2 = 2*2 ** n -2 + 2’ by fs[] >> Cases_on‘n=0’ >> simp[] >>
  ‘2*FUNPOW (λx. 2 * x) n 1 = 2*2 ** n’ suffices_by rw[] >>
  ‘2 <= FUNPOW (λx. 2 * x) n 1 ∧ 2<= 2**n’ suffices_by fs[SUB_ADD] >> rw[X_LE_X_EXP] >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >> rw[] >>
  Induct_on‘n’ >> rw[FUNPOW_SUC] >>  pop_assum kall_tac >> Induct_on‘n’ >> rw[FUNPOW_SUC]
QED

Theorem primrec_nblTpow:
  primrec nblTpow 1
Proof
  simp[nblTpow_def,Excl"K_THM.1",Excl"Cn0123.1"] >> irule primrec_Cn >> rw[Excl"K_THM.1",Excl"Cn0123.1"] >> irule primrec_FUNPOW >> rw[primrec_rules] >> irule primrec_pr1 >> rw[] >> qexists_tac‘Cn (pr2 $*) [K 2;proj 0]’ >> rw[] >> irule primrec_Cn >> rw[primrec_rules]
QED




Definition nblpair_def:
  nblpair = Cn (pr2 nblconcat)
               [Cn (pr2 nblconcat)
                   [Cn (pr2 nblconcat)
                       [Cn nblTpow
                           [Cn (pr1 (λp. ℓ p))
                               [proj 0]];
                        K 1];
                    proj 0];
                proj 1]
End



Theorem primrec_nblpair:
  primrec nblpair 2
Proof
  simp[nblpair_def] >> rpt (irule primrec_Cn >> rw[primrec_rules,primrec_nblconcat,primrec_nblTpow,primrec_ell])
QED

Theorem nblconcat_correct2:
  nblconcat a b = bl2n ((n2bl a)++(n2bl b))
Proof
  ‘∃x. a = bl2n x ∧ ∃y. b=bl2n y’ by (qexists_tac‘n2bl a’ >> rw[] >> qexists_tac‘n2bl b’ >> rw[]) >>  fs[nblconcat_correct]
QED

Theorem nblTpow_correct:
  nblTpow [n] = bl2n (Tpow n)
Proof
  simp[Tpow_def,nblTpow_compute] >> Induct_on‘n’ >> rw[] >- simp[Once bool_list_to_num_def] >>
  simp[GSYM ADD1,EXP,GENLIST_CONS,Once bool_list_to_num_def] >> fs[EXP,GSYM ADD1] >>
  Cases_on‘n=0’ >- fs[Once bool_list_to_num_def] >>
  ‘4 * 2 ** n − 2 - 2 = 2 * bl2n (GENLIST (K T) n) + 2 - 2 ’ by fs[CANCEL_SUB] >>
  fs[] >>
  ‘4 * 2 ** n − 4 + 2 = 2 * bl2n (GENLIST (K T) n) + 2’ by fs[] >>
  ‘4 * 2 ** n − 4 + 2 = 4 * 2 ** n − 2’ suffices_by fs[] >>
  rpt (pop_assum kall_tac) >>
  Induct_on‘n’ >> simp[EXP]
QED



Theorem nblpair_correct:
  nblpair [x;y] = bl2n (pair (n2bl x) (n2bl y))
Proof
  rw[nblpair_def,nblconcat_correct2,pair_def,bar_def,nblTpow_correct] >>
  simp[Once num_to_bool_list_def]
QED

Definition nblpair_flip_def:
  nblpair_flip = recCn (SOME o nblpair) [SOME o pr1 nblsnd;rec1 (SOME o nblfst)]
End



Theorem recfn_nblpair_flip:
  recfn nblpair_flip 1
Proof
  simp[nblpair_flip_def] >> irule recfnCn >> rw[recfn_nblsnd,recfn_nblfst,primrec_recfn] >>
  irule primrec_recfn >> simp[primrec_nblpair]
QED

Theorem nblpair_flip_correct[simp]:
  nblpair_flip [bl2n (pair x y)] = SOME (bl2n (pair y x))
Proof
  simp[nblpair_flip_def,recCn_def,nblfst_correct,nblsnd_correct2,nblpair_correct]
QED

val nblpf_i_def =  new_specification ("nblpf_i_def",["nblpf_i"],MATCH_MP unary_rec_fns_phi recfn_nblpair_flip)

Theorem symmetry_of_information2a:
  univ_mach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U (pair y x) + c
Proof
  rw[] >>
  qexists_tac‘4 * ℓ nblpf_i + 2 * ℓ comp_bli + 5’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  fs[PULL_EXISTS, univ_mach_def] >>
  rename[‘U pp = SOME (pair y x)’] >>
  ‘∃a i b. pp = pair a (plist bar (i::b))’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblpf_i) i) (plist bar (n2bl comp_bli :: a :: b))
  ’ >>
  ‘U ARG = SOME (pair x y)’
    by (simp[Abbr‘ARG’, comp_bli, Excl "plist_def"] >>
        simp[comp_machine_bl_correct,computable_composition_def, nblpf_i_def] >>
        ‘z = bl2n (pair y x)’ by simp[] >> rw[on2bl_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED

val nblpair_i_def = new_specification(
  "nblpair_i_def", ["nblpair_i"],
  MATCH_MP binary_rec_fns_phi (MATCH_MP primrec_recfn primrec_nblpair)
     |> SIMP_RULE (srw_ss()) [nblpair_correct]
);

Overload rfst = “rec1 (SOME o nblfst)”
Overload rsnd = “SOME o pr1 nblsnd”
Overload rpair = “SOME o nblpair”


Definition extra_info_cond_prog_def:
   extra_info_cond_prog = (* f ((y,z),(a,b)) = U(y,(a,b)) = Phi a (y,b)  *)
   recCn recPhi [recCn rfst [recCn rsnd [SOME o proj 0]];
                recCn rpair [recCn rfst [recCn rfst [SOME o proj 0]];
                             recCn rsnd [recCn rsnd [SOME o proj 0] ]] ]
End

Theorem recfn_extra_info_cond_prog:
  recfn extra_info_cond_prog 1
Proof
  simp[extra_info_cond_prog_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst, primrec_recfn, primrec_nblpair] >>
       rw[])
QED

Theorem extra_info_cond_prog_correct:
  extra_info_cond_prog [bl2n (pair (pair y z) (pair a b))] =
  Phi (bl2n a) (bl2n (pair y  b))
Proof
  simp[extra_info_cond_prog_def, recCn_def, nblpair_correct]
QED

Theorem extra_information_cond1:
  univ_mach U ==> ∃c. ∀x y z. CKC U x (pair y z) <= CKC U x y + c
Proof
  rw[] >>
  qx_choose_then ‘exinfoprog_i’ strip_assume_tac
                 (MATCH_MP unary_rec_fns_phi recfn_extra_info_cond_prog) >>
  qexists_tac ‘2 * ℓ exinfoprog_i + 7’ >> rw[] >>

  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_mach_pair_nonempty] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_mach_pair_nonempty] >>
  fs[PULL_EXISTS] >>
  rename [‘U (pair (pair y z) p1) = SOME x’, ‘U (pair y p2) = SOME x’]>>
  fs[univ_mach_def] >>
  ‘∃a b. p2 = plist bar (a::b)’
     by metis_tac[optionTheory.NOT_SOME_NONE, pair_11] >>
  rw[] >> rfs[on2bl_SOME] >> rw[] >>

  rename [‘Phi (bl2n a) _ = SOME x’] >>
  qabbrev_tac‘
    ARG = plist bar (n2bl exinfoprog_i::a::b)
  ’ >>
  ‘U (pair (pair y z) ARG) = SOME (n2bl x)’
    by (simp[Abbr‘ARG’, extra_info_cond_prog_correct, on2bl_def,
             plist_bar_CONS] >> fs[plist_bar_CONS]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED

Definition subaddprog_def:
  subaddprog = (* f (a,b,c,u,v) =  pair(b(a,c), u(b(a,c), v))*)
  let bac =
        recCn recPhi [
          recCn rfst [recCn rsnd [SOME o proj 0]]; (* b *)
          recCn rpair [
            (* a *) recCn rfst [SOME o proj 0];
            (* c *) recCn rfst [recCn rsnd [recCn rsnd [SOME o proj 0]]]
          ]
        ]
  in
    recCn rpair [
      bac;
      recCn recPhi [
        recCn rfst [recCn rsnd [recCn rsnd [recCn rsnd [SOME o proj 0]]]];(*u*)
        recCn rpair [
          bac;
          recCn rsnd [recCn rsnd [recCn rsnd [recCn rsnd [SOME o proj 0]]]](*v*)
        ]
      ]
    ]
End

Theorem recfn_subaddproj:
  recfn subaddprog 1
Proof
  simp[subaddprog_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst, primrec_recfn, primrec_nblpair] >>
       rw[])
QED

Theorem subaddprog_correct:
  subaddprog [bl2n (pair a (pair b (pair c (pair u v))))] =
  do
    x <- Phi (bl2n b) (bl2n (pair a c)) ;
    y <- Phi (bl2n u) (bl2n (pair (n2bl x) v)) ;
    SOME (bl2n (pair (n2bl x) (n2bl y)))
  od
Proof
  simp[subaddprog_def, recCn_def, nblpair_correct] >>
  Cases_on ‘Phi (bl2n b) (bl2n (pair a c))’ >> simp[] >>
  Cases_on ‘Phi (bl2n u) (bl2n (pair (n2bl x) v))’ >> simp[]
QED


Definition SIb_machine_def:
  SIb_machine =
  let len = recCn rfst [SOME o proj 0];
      aibjc = recCn rsnd [SOME o proj 0];
      aib = recCn (rec2 (λx y. SOME (nblft x y))) [aibjc;len];
      jc = recCn (SOME o pr_nblsr) [len;aibjc];
      a = recCn rfst [aib];
      i = recCn rfst [recCn rsnd [aib]];
      b = recCn rsnd [recCn rsnd [aib]];
      j = recCn rfst [jc];
      c = recCn rsnd [jc];
      x = recCn recPhi [i; recCn rpair [a;b]];
      y = recCn recPhi [j;recCn rpair [recCn rpair [x;len];c] ]
  in
    recCn rpair [y;x]
End

Theorem nblsr_thm = DROP_n2bl |> GSYM |> SPEC_ALL |> AP_TERM “bl2n” |> REWRITE_RULE [bool_num_inv];

Theorem nblft_thm = TAKE_n2bl |> GSYM |> SPEC_ALL |> AP_TERM “bl2n” |> REWRITE_RULE [bool_num_inv]

Theorem SIb_machine_correct:
  len = n2bl (LENGTH (pair a (pair i b) )) ==>
  SIb_machine [bl2n (pair len ((pair a (pair i b) ) ++ (pair j c) ) )] =
  do
    x <- Phi (bl2n i) (bl2n (pair a b));
    y <- Phi (bl2n j) (bl2n (pair (pair (n2bl x) len) c));
    SOME (bl2n (pair (n2bl y) (n2bl x)))
  od
Proof
  strip_tac >>
  fs[SIb_machine_def,recCn_def,pr_nblsr_correct,nblsr_thm,nblft_thm,
     rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND,
     nblpair_correct,Excl "pair_LENGTH"] >>
  Cases_on‘ Phi (bl2n i) (bl2n (pair a b))’ >> simp[Excl "pair_LENGTH"] >>
  Cases_on‘
    Phi (bl2n j)
        (bl2n
         (pair (pair (n2bl x) (n2bl (LENGTH (pair a (pair i b))))) c))’ >>
  simp[Excl "pair_LENGTH"]
QED

Theorem recfn_nblft:
 recfn (rec2 (λx y. SOME (nblft x y))) 2
Proof
  simp[nblft_phi_lem] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,recfn_some_num,
                             recfn_nblfst, primrec_recfn, primrec_nblpair,recfn_pr_nblsr] >>
       rw[])
QED

Theorem recfn_SIb_machine:
  recfn SIb_machine 1
Proof
  simp[SIb_machine_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,recfn_nblft,
                             recfn_nblfst, primrec_recfn, primrec_nblpair,recfn_pr_nblsr] >>
       rw[])
QED


Definition nblbar_def:
  nblbar = Cn (pr2 nblconcat) [Cn nblTpow [Cn (pr1 (λp. ℓ p)) [proj 0]];
                               Cn (pr2 nblconcat) [K 1;proj 0] ]
End

Theorem nblconcat_thm:
  nblconcat a b = bl2n (n2bl a ++ n2bl b)
Proof
  ‘∃m. a = bl2n m’ by (qexists_tac‘n2bl a’ >> fs[]) >>
  ‘∃n. b = bl2n n’ by (qexists_tac‘n2bl b’ >> fs[]) >>
  rw[]
QED

Theorem nblbar_correct:
  nblbar [l] = bl2n (bar (n2bl l))
Proof
  simp[nblbar_def,nblconcat_thm,nblTpow_correct,bar_def] >> EVAL_TAC
QED

Theorem primrec_nblbar:
  primrec nblbar 1
Proof
  fs[nblbar_def] >>
  rpt (irule primrec_Cn >> rw[primrec_nblconcat,primrec_nblTpow,primrec_ell,primrec_rules])
QED

(* up to here *)

Theorem symmetry_of_information1b:
  univ_mach U ==>
  ∃c. ∀x y. KC U (pair x y) ≤ CKC U x (pair y (n2bl (KC U y))) + KC U y + c
Proof
  rw[] >>
  qx_choose_then ‘SIb_i’ strip_assume_tac
                 (MATCH_MP unary_rec_fns_phi recfn_SIb_machine) >>
  qexists_tac ‘2 * ℓ SIb_i + 7’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_mach_pair_nonempty] >>
  fs[PULL_EXISTS, univ_mach_def] >>
  rename [‘U p = SOME (pair x y)’, ‘U p1 = SOME y’,
          ‘U (pair (pair y (n2bl (LENGTH p1))) p2) = SOME x’] >>
  ‘∃a1 i1 b1. p1 = pair a1 (plist bar (i1::b1))’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME, Excl "pair_LENGTH"] >> rw[] >>
  qabbrev_tac ‘N1 = LENGTH (pair a1 (plist bar (i1::b1)))’ >>
  ‘∃i2 b2. p2 = plist bar (i2::b2)’
     by metis_tac[optionTheory.NOT_SOME_NONE, pair_11] >>
  rw[] >> rfs[on2bl_SOME, Excl "pair_LENGTH"] >> rw[] >>
  rename [‘U p = SOME (pair (n2bl x) (n2bl y))’] >>
  qabbrev_tac‘ARG = pair (n2bl N1) (plist bar (n2bl SIb_i :: a1 :: i1 :: b1) ++ pair i2 b2) )’ >>
  ‘U ARG = SOME (pair (n2bl x) (n2bl y))’ by (simp[Abbr‘ARG’,SIb_machine_correct,on2bl_SOME]) >>
  qmatch_abbrev_tac‘LENGTH p <= RR’ >> ‘LENGTH ARG <= RR’ suffices_by metis_tac[LESS_EQ_TRANS] >>
  simp[Abbr‘ARG’,Abbr‘RR’,Abbr‘N1’,pair_LENGTH]

QED


Theorem subadditivity2:
  univ_mach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U x +  CKC U y x + c
Proof
  rw[KC_def,core_complexity_def,CKC_def,cond_core_complexity_def] >>
  fs[univ_rf_nonempty,univ_rf_pair_nonempty,univ_mach_rf] >>
  ‘univ_rf U’ by fs[univ_mach_rf] >> fs[univ_mach_def] >>
  qx_choose_then ‘subaddprog_i’ strip_assume_tac
    (MATCH_MP unary_rec_fns_phi recfn_subaddproj) >>
  qexists_tac ‘2 * ℓ subaddprog_i’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >>
      ‘{ p | U p = SOME (pair x y) } ≠ ∅’ by simp[univ_rf_nonempty] >>
      fs[EXTENSION] >> metis_tac[]) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >>
      ‘{ p | U p = SOME x } ≠ ∅’ by simp[univ_rf_nonempty] >>
      fs[EXTENSION] >> metis_tac[]) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >> ‘univ_mach U’ by metis_tac[univ_mach_def] >>
      simp[SIMP_RULE (srw_ss()) [EXTENSION] univ_rf_pair_nonempty]) >>
  fs[PULL_EXISTS] >>
  rename [‘U p1 = SOME (pair x y)’, ‘U p2 = SOME x’, ‘U (pair x p3) = SOME y’]>>
  ‘∃a b c. p2 = pair a (pair b c)’ by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME] >> rw[] >>
  ‘∃u v. p3 = pair u v’ by metis_tac[optionTheory.NOT_SOME_NONE, pair_11] >>
  rw[] >> rfs[on2bl_SOME] >> rw[] >>
  rename [‘Phi (bl2n b) _ = SOME x’,
          ‘Phi (bl2n u) (bl2n (pair (n2bl x) v)) = SOME y’,
          ‘pair u v’] >>
  qabbrev_tac‘
    ARG = pair a (pair (n2bl subaddprog_i) (pair b (pair c (pair u v))))
  ’ >>
  ‘U ARG = SOME (pair (n2bl x) (n2bl y))’
    by simp[Abbr‘ARG’, subaddprog_correct, on2bl_def] >>
  qmatch_abbrev_tac ‘LENGTH p1 ≤ RR’ >>
  ‘LENGTH ARG ≤ RR’ suffices_by metis_tac[LESS_EQ_TRANS] >>
  simp_tac std_ss [Abbr‘ARG’, Abbr‘RR’, pair_LENGTH, LEFT_ADD_DISTRIB] >>
  cheat
QED




Theorem symmetry_of_information1a:
  univ_mach U ==>
  ∃c. ∀x y.  CKC U x (pair y (n2bl (KC U y))) + KC U y <= KC U (pair x y) + c
Proof
  rw[KC_def,core_complexity_def,CKC_def,cond_core_complexity_def] >>
  fs[univ_rf_nonempty,univ_rf_pair_nonempty,univ_mach_rf] >>
  ‘univ_rf U’ by fs[univ_mach_rf] >> fs[univ_mach_def] >>
  qx_choose_then ‘subaddprog_i’ strip_assume_tac
    (MATCH_MP unary_rec_fns_phi recfn_subaddproj) >>
  qexists_tac ‘2 * ℓ subaddprog_i’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >>
      ‘{ p | U p = SOME y } ≠ ∅’ by simp[univ_rf_nonempty] >>
      fs[EXTENSION] >> metis_tac[]) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >> ‘univ_mach U’ by metis_tac[univ_mach_def] >>
      simp[SIMP_RULE (srw_ss()) [EXTENSION] univ_rf_pair_nonempty]) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (fs[EXTENSION] >>
      ‘{ p | U p = SOME (pair x y) } ≠ ∅’ by simp[univ_rf_nonempty] >>
      fs[EXTENSION] >> metis_tac[]) >>
  fs[PULL_EXISTS] >> cheat
QED

Theorem symmetry_of_information2b:
  univ_mach U ==>
  ∃c. ∀x y.
    CKC U y (pair x (n2bl (KC U x))) + KC U x ≤
    CKC U x (pair y (n2bl (KC U y))) + KC U y + c
Proof
  cheat
QED



val _ = export_theory()
