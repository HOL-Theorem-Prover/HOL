open HolKernel Parse boolLib bossLib;
open kolmogorov_complexityTheory
open pred_setTheory
open kraft_ineqTheory
open invarianceResultsTheory 
open boolListsTheory
open kolmog_incomputableTheory
open recursivefnsTheory
open primrecfnsTheory
open unary_recfnsTheory
open kolmog_inequalitiesTheory

val _ = new_theory "prefix_free_kolmog";


(* Prefix Universal Turing Machine *)


Theorem prefix_univ_rf_not_exists:
 ~∃U. prefix_machine U ∧ univ_rf U
Proof
  fs[prefix_machine_def,univ_rf_def] >> rw[] >>
  Cases_on‘∃f. ∀g. ∃x. on2bl (Phi f x) ≠ U (g ++ n2bl x)’ >> rw[] >> fs[] >>
  Cases_on‘∃x. x ∈ P ⇎ ∃y. U x = SOME y’ >> rw[] >> fs[] >>
  fs[prefix_free_def] >> 
  ‘∃g. ∀x. on2bl (Phi nblfst_i x) = U (g++ n2bl x)’ by fs[] >>
  qexists_tac‘g++n2bl 2’ >> qexists_tac‘g++n2bl 6’ >> rw[]
  >- (qexists_tac‘n2bl (nblfst 2)’ >>
      ‘on2bl (Phi nblfst_i 2) = SOME (n2bl (nblfst 2))’ by fs[nblfst_i_def,on2bl_SOME] >>
      metis_tac[])
  >- (qexists_tac‘n2bl (nblfst 6)’ >>
      ‘on2bl (Phi nblfst_i 6) = SOME (n2bl (nblfst 6))’ by fs[nblfst_i_def,on2bl_SOME] >>
      metis_tac[])
  >- (EVAL_TAC >> rw[rich_listTheory.IS_PREFIX_APPENDS])
QED


(*
Definition univ_pf_rf_def:
  univ_pf_rf U <=> ((∀f. ∃g. ∀x. on2bl (recPhi [f; x]) = U (bar g ++ bar (n2bl x))) ∧
                    ∀p. (∀a b. p <> (bar a) ++ (bar b)) ==> U p = NONE)
End

Theorem bar_bar_pf:
  ~(bar a ++ bar b ≺ bar c ++ bar d)
Proof
  rw[GSYM bar2_def]
QED
        

Theorem univ_pf_rf_prefix_machine:
  univ_pf_rf U ==> prefix_machine U
Proof
  rw[univ_pf_rf_def,prefix_machine_def] >>
  qexists_tac‘{p | (∃g x. p = bar g ++ bar (n2bl x)) ∧ (∃y. U p = SOME y)}’ >> rw[]
  >- (rw[prefix_free_def] >> rw[GSYM bar2_def] >>
      assume_tac (Q.INST [‘s’|->‘{(g,n2bl x);(g',n2bl x')}’] bar2_PF) >>
      fs[prefix_free_def] >> metis_tac[] )
  >- (eq_tac >> rw[] >> ‘~(∀a b. x ≠ bar a ++ bar b)’ by metis_tac[optionTheory.NOT_NONE_SOME] >>
      fs[] >> qexists_tac‘a’ >> qexists_tac‘bl2n b’ >> rw[])
QED
*)

Theorem kolmog_kraft2:
  prefix_machine U ==> bls_size {x | (∃y. U x = SOME y)} n <= 1
Proof
  rw[] >> irule kraft_ineq1 >> fs[prefix_machine_def] >>
  ‘{x | (∃y. U x = SOME y)} = P’ suffices_by fs[] >> fs[EXTENSION]
QED

Theorem kolmog_kraft3:
  univ_mach U ==> bls_size {x | (∃y. U x = SOME y)} n <= 1
Proof
  rw[kolmog_kraft2,univ_mach_pf]
QED

(*

Theorem univ_pf_rf_nonempty:
  univ_pf_rf U ⇒ {p | U p = SOME x} ≠ ∅
Proof
  rw[univ_pf_rf_def,EXTENSION] >> assume_tac Phi_x_0 >>
  ‘∃k. Phi k 0 = SOME (bl2n x)’  by metis_tac[] >>
  ‘∃g. ∀m. on2bl (Phi k m) = U (bar g ++ bar (n2bl m))’ by metis_tac[] >>
  ‘on2bl (Phi k 0) = U (bar g ++ bar (n2bl 0))’ by fs[] >>
  qexists_tac‘bar g ++ bar (n2bl 0)’ >>
  ‘on2bl (Phi k 0) = SOME x’ suffices_by fs[] >>
  ‘on2bl (SOME (bl2n x)) = SOME x’ suffices_by metis_tac[] >> fs[on2bl_SOME]
QED


Theorem MIN_SET_lmult:
  s<> {} ∧ k<>0 ==> (k:num) * MIN_SET {b | b ∈ s} = MIN_SET { k*b | b ∈ s}
Proof
  rw[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] 
  >- (fs[EXTENSION] >> metis_tac[]) >>
  ‘b*k <= x*k’ by fs[] >> ‘x <= b’ by fs[] >>
  ‘x*k <= b*k’ by fs[] >> ‘k * x <= b*k’ by metis_tac[arithmeticTheory.MULT_COMM] >>
  ‘b*k <= k*x’ by metis_tac[arithmeticTheory.MULT_COMM]>>
  metis_tac[arithmeticTheory.LESS_EQUAL_ANTISYM]
QED

Theorem invariance_theorem_pf:
  ∀U T. univ_pf_rf U ==> ∃C. ∀x. (core_complexity U x) <= 
                                 (core_complexity (λy. on2bl (recPhi [T;bl2n y])) x) +
                                 (core_complexity (λy. on2bl (recPhi [T;bl2n y])) x) + (C U T)
Proof
  rw[univ_pf_rf_def,core_complexity_def] >>  fs[univ_pf_rf_def] >>
  `∃g. ∀x. on2bl (Phi T' x) = U (bar g++ bar (n2bl x))` by fs[] >>
  qexists_tac`λx y. SOME (2* LENGTH g + 2) ` >> rw[]
  >- (`univ_pf_rf U` by fs[univ_pf_rf_def] >>`{p| U p = SOME x} <> {}` by fs[univ_pf_rf_nonempty] >> fs[])
  >- (`MIN_SET (IMAGE LENGTH {p | U p = SOME x}) ∈
        IMAGE LENGTH ({p | U p = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`U_x = x'` >>
      `MIN_SET (IMAGE LENGTH { y | U (bar g ++ bar y) = SOME x}) ∈
        IMAGE LENGTH ({ y | U (bar g ++ bar y) = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`T_x = x''` >>
      `{LENGTH y | U (bar g ++ bar y) = SOME x} <> {}` by (fs[EXTENSION] >> qexists_tac`T_x`>>fs[])>>
      qabbrev_tac`a=LENGTH g` >>
      `a + MIN_SET {b | b ∈  {LENGTH y | U (bar g ++ bar y) = SOME x}} =
        MIN_SET {a + b | b ∈  {LENGTH y | U (bar g ++ bar y) = SOME x}}` by fs[MIN_SET_ladd] >>
      fs[] >>
      `{LENGTH p | U p = SOME x} <> {}` by (`IMAGE LENGTH { p | U p = SOME x} ≠ ∅` by
        fs[IMAGE_EQ_EMPTY] >>
        `{LENGTH p | p ∈ {q | U q= SOME x}} ≠ ∅` by metis_tac[IMAGE_DEF] >> fs[]) >>
      `MIN_SET {LENGTH p | U p = SOME x} ∈ {LENGTH p | U p = SOME x} ∧
        ∀q. q ∈ {LENGTH p | U p = SOME x} ⇒ MIN_SET {LENGTH p | U p = SOME x} ≤ q` by
        fs[MIN_SET_LEM] >>
      `MIN_SET {LENGTH x' | U x' = SOME x} ≤
       2*MIN_SET {(a + b) | (∃y. b = LENGTH y ∧ U (bar g ++ bar y) = SOME x)}+2`
         suffices_by fs[]>>
       DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] >>
      DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] 
       >- (fs[EXTENSION] >> qexists_tac`T_x`>>fs[]) >>
       fs[Abbr`a`] >>
       ‘LENGTH x'⁴' ≤ LENGTH (bar g ++ bar y)’ by metis_tac[] >>
       ‘LENGTH (bar g ++ bar y) = 2 * (LENGTH g + LENGTH y) + 2’ suffices_by fs[] >>
       fs[listTheory.LENGTH_APPEND,length_bar]  )
QED


(* Cleaned up invariance theorem *)


Theorem clean_invariance_theorem_pf:
  ∀U V. univ_pf_rf U ∧ (i ∈ indexes_of V ) ==> ∃C. ∀x. (core_complexity U x) <= (core_complexity V x) + (core_complexity V x) + (C U i)
Proof
  rw[indexes_of_def] >> qspecl_then [`U`,`i`] mp_tac invariance_theorem_pf >> rw[]
QED


*)

(*  New stuff might not need  *)

(*
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


Definition univ_pf_fun_def:
  univ_pf_fun = minimise (λx. if (proj 0 x = 1) ∧ (nblsnd (proj 1 x) = 1) then SOME 0 else SOME 1)
End

Theorem univ_pf_fun_correct:
  univ_pf_fun [bl2n (pair a b)] = if bl2n b = 1 then SOME 1 else NONE
Proof
  rw[] >> simp[univ_pf_fun_def,minimise_thm] >> rw[nblsnd_correct2] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[] >> qexists_tac‘1’ >> rw[]
QED

Theorem recfn_univ_lem1:
  recfn (λx. if proj 0 x = 1 ∧ nblsnd (proj 1 x) = 1 then SOME 0 else SOME 1) 2
Proof
  ‘(λx. if proj 0 x = 1 ∧ nblsnd (proj 1 x) = 1 then SOME 0n else SOME 1) =
  (SOME o (λx. if proj 0 x = 1 ∧ nblsnd (proj 1 x) = 1 then 0n else 1)) ’ by
    (rw[FUN_EQ_THM] >> rw[]) >> rw[] >> irule primrec_recfn >>
  ‘(λx. if proj 0 x = 1 ∧ nblsnd (proj 1 x) = 1 then 0 else 1) =
   pr_cond (Cn pr_eq [proj 0;K 1]) (pr_cond (Cn pr_eq [Cn pr_nblsnd [proj 1];K 1]) (K 0) (K 1) ) (K 1)’ by (fs[FUN_EQ_THM] >> rw[pr_nblsnd_correct ]) >> rw[] >> irule primrec_pr_cond >> rw[]
   >- (irule primrec_Cn >> rw[primrec_rules]) >>
   irule primrec_pr_cond >> rw[] >> irule primrec_Cn >> rw[primrec_rules] >>
   irule primrec_Cn >> simp[primrec_nblsnd] >> simp[primrec_rules]
QED

Theorem recfn_univ_pf_fun:
  recfn univ_pf_fun 1
Proof
 fs[univ_pf_fun_def] >> irule (last (CONJUNCTS recfn_rules)) >> rw[] >>simp[recfn_univ_lem1]
QED

val recfn_univ_pf_i_def =  new_specification ("recfn_univ_pf_i_def",["recfn_univ_pf_i"],MATCH_MP unary_rec_fns_phi recfn_univ_pf_fun)


Theorem univ_mach_exists:
  ∃U. univ_mach U
Proof
  simp[univ_mach_def] >> qexists_tac‘(λx. case some (a,b,c). x = (pair a (pair b c)) of
                              NONE => NONE
                            | SOME (a,b,c) => on2bl (Phi (bl2n b) (bl2n (pair a c) ) ) )’ >>
  conj_tac >-( rw[] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[]
  >- (PairCases_on‘x'’ >> fs[] >> fs[pair_11])
  >- (first_x_assum (qspec_then ‘(y,i,x)’ mp_tac) >> rw[]))
  >- (rw[] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[])
QED
    
val univ_mach_fn_def =  new_specification ("univ_mach_fn_def",["univ_mach_fn"],univ_mach_exists )



*)


(*


(* OLD STUFF *)
        
val PUTM_def = Define`PUTM x = if bar2ed x then recPhi [bl2n (FST (unbar2 0 x));bl2n (SND (unbar2 0 x))] else NONE`


val PUTM_universal = Q.store_thm("PUTM_universal",
`∀f. ∃g. ∀x. ∃y. recPhi [f;x] = PUTM (g++y)`,
fs[PUTM_def] >> rw[] >> qexists_tac`bar (n2bl f)` >> rw[] >> qexists_tac`bar (n2bl x)` >>
fs[bar2ed_def] >> rw[]
>- (fs[unbar2_bar2_inv,GSYM bar2_def] >> rw[] )
>- (fs[] >> metis_tac[])  )

Theorem PUTM_universal_input:
  ∀f. ∃g. ∀x. recPhi [f;x] = PUTM (g++(bar (n2bl x)))
Proof
  fs[PUTM_def] >> rw[] >> qexists_tac`bar (n2bl f)` >> rw[]
  >- (fs[unbar2_bar2_inv,GSYM bar2_def] >> rw[])
  >- (fs[bar2ed_def] >> metis_tac[])
QED


val PUTM_prefix_free = Q.store_thm("PUTM_prefix_free",
`prefix_free {x | ∃y.  PUTM x = SOME y}`,
irule prefix_free_subset >> qexists_tac`{x| bar2ed x}` >> rw[SUBSET_DEF,PUTM_def] >>
simp[bar2ed_def] >> irule prefix_free_subset >> qexists_tac`IMAGE bar2 UNIV` >> simp[bar2_PF]>>
simp[SUBSET_DEF,bar2_def,pairTheory.EXISTS_PROD])




Theorem print_exists:
  ∀x. ∃m. PUTM (bar2 (m,[])) = SOME x
Proof
  rw[PUTM_def,bool_list_to_num_def] >> Q.REFINE_EXISTS_TAC`n2bl m` >> simp[Phi_def] >>
  qexists_tac`dBnum (fromTerm (K @@ church x))` >> simp[] >> qexists_tac`church x` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED

Theorem kolmog_exists:
  ∀x. ∃y. kolmog_complexity x PUTM = SOME y
Proof
  rw[kolmog_complexity_def,EXTENSION] >> metis_tac[print_exists]
QED

val kolmog_def = Define`kolmog x = THE (kolmog_complexity x PUTM)`

val arg_kolmog_def = Define`arg_kolmog x =
                           @q. PUTM q = SOME x ∧ LENGTH q=(MIN_SET {LENGTH p | PUTM p = SOME x})`;

Theorem arg_kolmog_thm:
  arg_kolmog x = @q. PUTM q = SOME x ∧ LENGTH q = kolmog x
Proof
  fs[arg_kolmog_def,kolmog_def,kolmog_complexity_def] >> `{p| PUTM p = SOME x}<> {}` by
    (simp[EXTENSION] >> metis_tac[print_exists]) >> simp[]
QED


(* Kolmogorov kraft inequality *)

Theorem kolmog_prefix_free:
  prefix_free { x| ∃y. (kolmog y = LENGTH x) ∧ ( (PUTM x) = SOME y) }
Proof
  fs[kolmog_def,kolmog_complexity_def,prefix_free_def] >> rw[] >>
  `prefix_free {x | (∃y. PUTM x = SOME y)}` by fs[PUTM_prefix_free] >> fs[prefix_free_def]
QED

Theorem kolmog_kraft:
  REAL_SUM_IMAGE (\s. (2 rpow (real_neg &(LENGTH s)))) {q | q ∈ {x| ∃y. (kolmog y = LENGTH x) ∧ ((PUTM x) = SOME y) } ∧ LENGTH q <n} <=1
Proof
  `prefix_free {x| ∃y. (kolmog y = LENGTH x) ∧ ((PUTM x) = SOME y) }` by fs[kolmog_prefix_free]>>
  `bls_size {x| ∃y. (kolmog y = LENGTH x) ∧ ((PUTM x) = SOME y) } n <= 1` by fs[kraft_ineq1]>>
  fs[bls_size_def]
QED

val HUTM_w_side_inf_def = Define`HUTM_w_side_inf p =
  if bar2ed_plus p then (Phi (bl2n (FST (SND (unbar2_plus p) ) ))
                             (bl2n (bar (FST  (unbar2_plus p)) ++
                                   (SND (SND (unbar2_plus p) ))) ))
  else NONE`

val HUTM_def =  Define`HUTM p =
  if bar2ped p then (Phi (bl2n (FST (unbar2p 0 p) ) )
                         (bl2n (SND (unbar2p 0 p) ) ))
  else NONE`

val prefix_free_fn_def = Define`prefix_free_fn M <=> prefix_free {x | (∃y. Phi M (bl2n x) = SOME y)}`

val HUTMpf_def =  Define`HUTMpf p =
  if bar2ped p then
    if prefix_free_fn (bl2n (FST (unbar2p 0 p) ) )  then
      (Phi (bl2n (FST (unbar2p 0 p) ) )
           (bl2n (SND (unbar2p 0 p) ) ))
    else NONE
  else NONE`

Theorem HUTM_w_side_inf_corr:
  HUTM_w_side_inf ((bar y) ++ (bar i) ++ q) = Phi (bl2n i) (bl2n ((bar y) ++ q))
Proof
  fs[bar2ed_plus_def,HUTM_w_side_inf_def,unbar2_plus_corr] >> rw[] >> metis_tac[]
QED

Theorem HUTM_corr:
  HUTM ((bar i) ++ q) = Phi (bl2n i) (bl2n q)
Proof
  fs[unbar2p_def,bar2ped_def,HUTM_def,unbar2p_induct,bar_def] >>  rw[unbar2p_induct]
  >- (`Tpow (LENGTH i) ++ [F] ++ i ++ q = (Tpow (LENGTH i)) ++ F::(i ++ q)` by fs[] >>
      rw[unbar2p_induct] >>
      REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,rich_listTheory.TAKE_LENGTH_APPEND,
                   rich_listTheory.DROP_LENGTH_APPEND,ADD_CLAUSES]) >>
  metis_tac[]
QED


Theorem HUTMpf_corr:
  prefix_free_fn M ==> HUTMpf ((bar (n2bl M)) ++ q) = Phi M (bl2n q)
Proof
  rw[] >>  fs[unbar2p_def,bar2ped_def,HUTMpf_def,unbar2p_induct,bar_def] >>  rw[unbar2p_induct]
  >- (`Tpow (LENGTH i) ++ [F] ++ i ++ q = (Tpow (LENGTH i)) ++ F::(i ++ q)` by fs[] >>
      rw[unbar2p_induct] >>
      REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,rich_listTheory.TAKE_LENGTH_APPEND,
                   rich_listTheory.DROP_LENGTH_APPEND,ADD_CLAUSES] >>
      rw[unbar2p_induct] >>
      REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,rich_listTheory.TAKE_LENGTH_APPEND,
                   rich_listTheory.DROP_LENGTH_APPEND,ADD_CLAUSES] >>
      `Tpow (ℓ M) ++ [F] ++ (n2bl M ++ q) = Tpow (LENGTH i) ++ [F] ++ (i ++ q')` by
        metis_tac[APPEND_ASSOC] >>
      `ℓ M = LENGTH i` by fs[] >>
      `n2bl M ++ q = i++q'` by fs[] >>
      `q=q'` by (`DROP (LENGTH i) (i++q') = q'` by simp[rich_listTheory.DROP_LENGTH_APPEND] >>
                 `DROP (LENGTH i) (n2bl M ++ q) = q'` by fs[] >>
                 `DROP (ℓ M) (n2bl M ++ q) = q'` by fs[] >>
                 `DROP (LENGTH (n2bl M)) (n2bl M ++ q) = q` by
                   rw[rich_listTheory.DROP_LENGTH_APPEND] >> fs[] ) >>
      `bl2n i = M` suffices_by fs[] >> `n2bl M = i` by fs[] >>
      `bl2n (n2bl M) = bl2n i` by fs[] >> rw[bool_num_inv]
       )
  >- (`¬prefix_free_fn
           (bl2n (FST (unbar2p 0 ( Tpow (ℓ M) ++ [F] ++ n2bl M ++ q))))` by fs[] >>
       `Tpow (ℓ M) ++ [F] ++ n2bl M ++ q= Tpow (ℓ M) ++ F::(n2bl M ++ q)` by fs[] >>
       `¬prefix_free_fn
           (bl2n (FST (unbar2p 0 ( Tpow (ℓ M) ++ F::(n2bl M ++ q)))))` by metis_tac[] >>
       `unbar2p 0 (Tpow (ℓ M)  ++ F::(n2bl M ++ q)) =
         (TAKE (0 + (ℓ M) ) (n2bl M ++ q),DROP (0+ (ℓ M) ) (n2bl M ++ q))` by fs[unbar2p_induct] >>
       fs[] >> `(TAKE (LENGTH (n2bl M)) (n2bl M ++ q)) = n2bl M` by
                 metis_tac[rich_listTheory.TAKE_LENGTH_APPEND] >> fs[] )  >>
  metis_tac[]
QED

Theorem HUTM_univ:
  univ_rf HUTM
Proof
  fs[univ_rf_def] >> rw[] >> qexists_tac`bar (n2bl (f))` >> rw[HUTM_corr]
QED

(* (* Another pf machine *)
val undop_def = Define` (undop i (T::rest) = undop (i + 1) rest) ∧
                         undop i (F::rest) = (n2bl i, rest)
`;

(* never used! *)
Theorem undop_corr:
  ∀n. undop n ((Tpow f) ++ [F]++x) = (n2bl (f + n), x)
Proof
  simp[Tpow_def] >> Induct_on`f` >- simp[undop_def] >>
  simp[GENLIST_CONS,ADD1,undop_def]
QED

val CUTM_def = Define`CUTM p = Phi (bl2n  (FST (undop 0 p))) (bl2n (SND (undop 0 p)) )`

*)
(* prefix invariance theorem  *)

Theorem pf_invariance_theorem:
  ∀M. prefix_free {x | (∃y. recPhi [M;bl2n x] = SOME y)} ==>  ∃C. ∀x. (kolmog_complexity x HUTM) <= (kolmog_complexity x (λy. recPhi [M;bl2n y])) + (C HUTM M)
Proof
  rw[kolmog_complexity_def] >>  `univ_rf HUTM` by fs[HUTM_univ] >> fs[univ_rf_def] >>
  `∃g. ∀x. Phi M x = HUTM (g++ (n2bl x))` by fs[] >>
  qexists_tac`λx y. SOME (LENGTH g)` >> rw[]
  >- (`univ_rf HUTM` by fs[univ_rf_def] >>`{p| HUTM p = SOME x} <> {}` by fs[univ_rf_nonempty] >>
      fs[])
  >- (`MIN_SET (IMAGE LENGTH {p | HUTM p = SOME x}) ∈
        IMAGE LENGTH ({p | HUTM p = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`HUTM_x = x'` >>
      `MIN_SET (IMAGE LENGTH {y | HUTM (g ++ y) = SOME x}) ∈
        IMAGE LENGTH ({y | HUTM (g ++ y) = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`M_x = x''` >>
      `{LENGTH y | HUTM (g ++ y) = SOME x} <> {}` by (fs[EXTENSION] >> qexists_tac`M_x`>>fs[])>>
      qabbrev_tac`a=LENGTH g` >>
      `a + MIN_SET {b | b ∈  {LENGTH y | HUTM (g ++ y) = SOME x}} =
        MIN_SET {a + b | b ∈  {LENGTH y | HUTM (g ++ y) = SOME x}}` by fs[MIN_SET_ladd] >>
      fs[] >>
      `{LENGTH p | HUTM p = SOME x} <> {}` by (`IMAGE LENGTH { p | HUTM p = SOME x} ≠ ∅` by
        fs[IMAGE_EQ_EMPTY] >>
        `{LENGTH p | p ∈ {q | HUTM q= SOME x}} ≠ ∅` by metis_tac[IMAGE_DEF] >> fs[]) >>
      `MIN_SET {LENGTH p | HUTM p = SOME x} ∈ {LENGTH p | HUTM p = SOME x} ∧
        ∀q. q ∈ {LENGTH p | HUTM p = SOME x} ⇒ MIN_SET {LENGTH p | HUTM p = SOME x} ≤ q` by
        fs[MIN_SET_LEM] >>
      `MIN_SET {LENGTH x' | HUTM x' = SOME x} ≤
       MIN_SET {a + b | (∃y. b = LENGTH y ∧ HUTM (g ++ y) = SOME x)}` suffices_by fs[]>>
      irule SUBSET_MIN_SET >> rw[]
      >- (fs[EXTENSION] >> qexists_tac`M_x`>>fs[])
      >- (rw[SUBSET_DEF] >>qexists_tac`g++y`>>fs[Abbr`a`] )  )
QED

Theorem hutm_clean_invariance_theorem:
  ∀V. (i ∈ indexes_of V ) ==> ∃C. ∀x. (kolmog_complexity x HUTM) <= (kolmog_complexity x V) + (C HUTM i)
Proof
  rw[clean_invariance_theorem,HUTM_univ] 
QED


Theorem HUTMpf_univpf:
  ∀f. prefix_free_fn f ==> ∃g. ∀x. recPhi [f; x] = HUTMpf (g ++ n2bl x)
Proof
  rw[] >> qexists_tac`bar (n2bl (f))` >> rw[HUTMpf_corr]
QED

Theorem HUTMpf_prefix_free:
  prefix_free {x | (∃y. HUTMpf x = SOME y)}
Proof
  rw[] >> fs[prefix_free_def] >> rw[HUTMpf_def] >>
  spose_not_then assume_tac >> fs[prefix_append,bar2ped_def,prefix_free_fn_def] >>
  fs[bar_def] >>
  `a++s = Tpow (LENGTH i) ++ [F] ++ (i ++ q++s)` by fs[] >> fs[] >>
  `Tpow (LENGTH i) ++ [F] ++ i ++ q  = Tpow (LENGTH i) ++ [F] ++ ( i ++ q)` by fs[] >>fs[]>>
  rw[] >> fs[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[prefix_free_def] >>
  ` (∃y. Phi (bl2n i) (bl2n q) = SOME y) ∧
             (∃y. Phi (bl2n i) (bl2n (q++s)) = SOME y) ⇒
             ¬(q ≺ q++s)` by fs[] >> `¬(q ≺ q++s)` by fs[] >> fs[prefix_def]
QED




Theorem HUTM_prefix_free:
  ∀M. prefix_free {x | (∃y. Phi M (bl2n x) = SOME y)} ==>
      prefix_free {x | (∃p. x = bar (n2bl M) ++ p) ∧ (∃y. HUTM x = SOME y)}
Proof
  rw[] >> fs[prefix_free_def] >> rw[] >>
  `(∃y. Phi M (bl2n p) = SOME y) ∧ (∃y. Phi M (bl2n p') = SOME y) ⇒ ¬( p ≺  p')`
    by metis_tac[] >>
  `Phi M (bl2n p) = SOME y` by fs[HUTM_corr] >>
  `Phi M (bl2n p') = SOME y'` by fs[HUTM_corr] >> fs[] >>
  spose_not_then assume_tac >> fs[prefix_append]
QED


val HUTMpf_print_def = Define`HUTMpf_print x = bar ( (n2bl (dBnum (fromTerm (C @@ (C @@ I @@ church x) @@ (K @@ Omega) )))))`

Theorem bar2ped_HUTMpf_print:
  bar2ped (HUTMpf_print x)
Proof
  fs[bar2ped_def,HUTMpf_print_def]
QED


Theorem HUTMpf_print_pf:
  prefix_free_fn (bl2n (FST (unbar2p 0 (HUTMpf_print x))))
Proof
  fs[prefix_free_fn_def,HUTMpf_print_def,unbar2p_bar] >>
  simp[Phi_def,K_lemma,normal_orderTheory.bnf_bnf_of] >>
  qmatch_abbrev_tac`prefix_free s` >> `s = {[]}` suffices_by fs[] >>
  fs[Abbr`s`,EXTENSION] >> rw[] >> Cases_on`x'` >> fs[] >>
  asm_simp_tac(bsrw_ss())[bool_list_to_num_def,normal_orderTheory.bnf_bnf_of,churchnumTheory.bnf_church] >>
  Cases_on`(if h then 2 else 1) + 2 * bl2n t` >> rw[] >- (fs[] >> Cases_on`h`>>fs[]) >>
  asm_simp_tac(bsrw_ss())[churchnumTheory.church_thm]
QED

Theorem HUTMpf_print_corr:
  HUTMpf (HUTMpf_print x) = SOME x
Proof
  simp[HUTMpf_def,bar_def,bar2ped_HUTMpf_print,Phi_def,HUTMpf_print_pf,bar2ped_HUTMpf_print] >>
  qexists_tac`church x` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of,HUTMpf_print_def] >>
  asm_simp_tac(bsrw_ss())[bool_list_to_num_def,churchnumTheory.church_thm,normal_orderTheory.bnf_bnf_of,churchnumTheory.bnf_church]
QED

Theorem HUTMpf_nonempty:
  {p | HUTMpf p = SOME x} <> {}
Proof
  fs[EXTENSION,HUTMpf_def] >> qexists_tac`(HUTMpf_print x)` >>
  rw[HUTMpf_print_pf,bar2ped_HUTMpf_print] >> fs[HUTMpf_print_def,Phi_def] >>
  qexists_tac`church x` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of,bool_list_to_num_def] >>
  asm_simp_tac(bsrw_ss())[churchnumTheory.church_thm,normal_orderTheory.bnf_bnf_of,churchnumTheory.bnf_church]
QED

Theorem HUTMpf_invariance_theorem:
  prefix_free_fn M ==>
  ∃C. ∀x. (kolmog_complexity x HUTMpf) <= (kolmog_complexity x (λy. recPhi [M;bl2n y])) + (C M)
Proof
  rw[kolmog_complexity_def] >> `∃g. ∀x. recPhi [M; x] = HUTMpf (g ++ n2bl x)` by
    fs[HUTMpf_univpf] >> qexists_tac`λx. SOME (LENGTH g)` >> rw[]
  >- (fs[HUTMpf_nonempty])
  >- (`MIN_SET (IMAGE LENGTH {p | HUTMpf p = SOME x}) ∈
        IMAGE LENGTH ({p | HUTMpf p = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`HUTMpf_x = x'` >>
      `∀x'. Phi M (bl2n x') = HUTMpf (g ++ x')`  by fs[] >>
      `MIN_SET (IMAGE LENGTH {y | HUTMpf (g ++ y) = SOME x}) ∈
        IMAGE LENGTH ({y | HUTMpf (g ++ y) = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`M_x = x''` >>
      `{LENGTH y | HUTMpf (g ++ y) = SOME x} <> {}` by (fs[EXTENSION] >> qexists_tac`M_x`>>fs[])>>
      qabbrev_tac`a=LENGTH g` >>
      `a + MIN_SET {b | b ∈  {LENGTH y | HUTMpf (g ++ y) = SOME x}} =
        MIN_SET {a + b | b ∈  {LENGTH y | HUTMpf (g ++ y) = SOME x}}` by fs[MIN_SET_ladd] >>
      fs[] >>
      `{LENGTH p | HUTMpf p = SOME x} <> {}` by (`IMAGE LENGTH { p | HUTMpf p = SOME x} ≠ ∅` by
        fs[IMAGE_EQ_EMPTY] >>
        `{LENGTH p | p ∈ {q | HUTMpf q= SOME x}} ≠ ∅` by metis_tac[IMAGE_DEF] >> fs[]) >>
      `MIN_SET {LENGTH p | HUTMpf p = SOME x} ∈ {LENGTH p | HUTMpf p = SOME x} ∧
        ∀q. q ∈ {LENGTH p | HUTMpf p = SOME x} ⇒ MIN_SET {LENGTH p | HUTMpf p = SOME x} ≤ q` by
        fs[MIN_SET_LEM] >>
      `MIN_SET {LENGTH x' | HUTMpf x' = SOME x} ≤
       MIN_SET {a + b | (∃y. b = LENGTH y ∧ HUTMpf (g ++ y) = SOME x)}` suffices_by fs[]>>
      irule SUBSET_MIN_SET >> rw[]
      >- (fs[EXTENSION] >> qexists_tac`M_x`>>fs[])
      >- (rw[SUBSET_DEF] >>qexists_tac`g++y`>>fs[Abbr`a`] ))
QED




val kolmogpf_def = Define`kolmogpf x = THE (kolmog_complexity x HUTMpf)`

Theorem kolmogpf_prefix_free:
  prefix_free { x| ∃y. (kolmogpf y = LENGTH x) ∧ ( (HUTMpf x) = SOME y) }
Proof
  fs[kolmogpf_def,kolmog_complexity_def,prefix_free_def] >> rw[] >>
  `prefix_free {x | (∃y. HUTMpf x = SOME y)}` by fs[HUTMpf_prefix_free] >> fs[prefix_free_def]
QED

Theorem kolmog_HUTMpf_kraft:
  REAL_SUM_IMAGE (\s. (2 rpow (real_neg &(LENGTH s)))) {q | q ∈ {x| ∃y. (kolmogpf y = LENGTH x) ∧ ((HUTMpf x) = SOME y) } ∧ LENGTH q <n} <=1
Proof
  `prefix_free {x| ∃y. (kolmogpf y = LENGTH x) ∧ ((HUTMpf x) = SOME y) }` by fs[kolmogpf_prefix_free]>>
  `bls_size {x| ∃y. (kolmogpf y = LENGTH x) ∧ ((HUTMpf x) = SOME y) } n <= 1` by fs[kraft_ineq1]>>
  fs[bls_size_def]
QED

Theorem kolmog_kraft2:
  bls_size {x | (∃y. HUTMpf x = SOME y)} n <= 1
Proof
  fs[kraft_ineq1,HUTMpf_prefix_free]
QED


*)



val _ = export_theory();

