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



Definition univ_pf_def:
  univ_pf U <=> univ_mach U ∧ prefix_free {p | (∃x. U p = SOME x)}
End


Theorem univ_pf_univ_mach:
  univ_pf U ==> univ_mach U
Proof
  fs[univ_pf_def]
QED

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

Definition recfn_predicate_def:
  recfn_predicate P <=> ∀n. P n = SOME 0n ∨ P n = SOME 1
End

        (*
Theorem recfn_cond_thm:
  recfn_predicate P ==> recfn_cond P f g n = if P n = SOME 1n then f n else g n
Proof
  Cases_on‘f n = NONE’ >> Cases_on‘g n = NONE’ >> rw[recfn_predicate_def,recfn_cond_def,recCn_def]
  >- (‘IS_SOME (f n)’ by fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >> fs[quantHeuristicsTheory.SOME_THE_EQ_SYM])
  >- (‘IS_SOME (f n) ∧ IS_SOME (g n) ∧ IS_SOME (P n)’ by
      fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >> ‘∃a b. f n = SOME a ∧ g n = SOME b’ by
        fs[optionTheory.IS_SOME_EXISTS]>> rw[] >> ‘P n = SOME 0’ by metis_tac[] >> rw[])
  >- (fs[])
  >- ()
  
,optionTheory.option_CLAUSES] >> [optionTheory.NOT_SOME_NONE]
QED *)

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


(* NEED TO CHANGE univ_mach to be
univ_mach U <=> (∀i y x.
                 U (pair y (pair i x)) = on2bl (Phi (bl2n i) (bl2n (pair y x)))) ∧
                  ∀m. (∀i y x. m ≠ pair y (pair i x)) ⇒ U m = NONE
*)

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

Theorem univ_pf_nonempty:
  {U | univ_pf U} <> {}
Proof
  fs[EXTENSION,univ_pf_def,univ_mach_def] >>
  qexists_tac‘(λa. )’
QED

Theorem kolmog_kraft2:
  univ_pf U ==> bls_size {x | (∃y. U x = SOME y)} n <= 1
Proof
  fs[kraft_ineq1,HUTMpf_prefix_free] >> 
QED



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






val _ = export_theory();

