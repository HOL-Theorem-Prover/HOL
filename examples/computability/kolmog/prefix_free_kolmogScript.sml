open HolKernel Parse boolLib bossLib;
open kolmogorov_complexityTheory
open kraft_ineqTheory

val _ = new_theory "prefix_free_kolmog";


(* Prefix Universal Turing Machine *)


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

