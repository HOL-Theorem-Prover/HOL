
open HolKernel Parse boolLib bossLib;

val _ = new_theory "kolmog_complex2";




val _ = export_theory();



(*

Theorem univ_rf_no_pf:
  univ_rf U ==> ¬prefix_free {x | ∃y. U x = SOME y}
Proof
  rw[prefix_free_def] >> fs[univ_rf_def,kolmog_complexity_def] >>
  `∀y. {p | U p = SOME y} ≠ ∅` by
    (`univ_rf U` by fs[univ_rf_def] >> fs[univ_rf_nonempty]) >>
  fs[] >> qexists_tac`[T]` >> qexists_tac`[T;T]` >>rw[]
QED



(*
Theorem comp_univ_comp_npkolmog:
  univ_rf U ∧ (computable (λx. THE (kolmog_complexity x U) ) ) ==> computable np_kolmog
Proof
  rw[] >> fs[computable_def,np_kolmog_def,univ_rf_def,computable_def] >>
  fs[kolmog_complexity_def] >>
  `∀n. {y | Phi (nfst (bl2n y)) (nsnd (bl2n y)) = SOME n} <> ∅` by
        fs[EXTENSION,Phi_bl2nx_npair] >> simp[] >>
  `∀x. {p | U p = SOME x} <> ∅` by
    (rw[] >> `univ_rf U` by simp[univ_rf_def] >> drule univ_rf_nonempty >> fs[]) >>
  fs[] >>
  qexists_tac`numdB (fromTerm (LAM "n" ) )`

  `∃g. ∀x. Phi i x = U (g ++ n2bl x)` by fs[] >>
  `∀x. SOME (THE (kolmog_complexity x U)) = U (g ++ n2bl x)` by fs[] >>
  fs[kolmog_complexity_def] >> `univ_rf U` by fs[univ_rf_def] >>
  Cases_on`∀x. {p | U p = SOME x} <> ∅`
  >- (`SOME (MIN_SET {LENGTH p | U p = SOME x}) = U (g ++ n2bl x)` by fs[] >>
       >> qexists_tac`i` >> rw[])
  >- metis_tac[univ_rf_nonempty]
QED

Theorem univ_comp_kol_incomp:
  univ_rf U ==> ¬(computable (λx. THE (kolmog_complexity x U) ) )
Proof

QED
*)


(*
(*  TODO next, show any kolmogorov complexity for a universal function is incomputable *)



Theorem incomp_all_kolmog:
  univ_rf U ==> ¬(computable (λx. THE (kolmog_complexity x U) ) )
Proof
  rw[] >> strip_tac >>
QED

*)


(* not sure if needed anymore
Theorem dBnum_fromTerm_church:
  dBnum (fromTerm (church y)) = 35
Proof
  Induct_on`y` >>
  fs[churchnumTheory.church_def] >>
  fs[churchDBTheory.fromTerm_funpow_app] >>
  fs[pure_dBTheory.dLAM_def] >>
  fs[enumerationsTheory.dBnum_def] >>
  fs[pure_dBTheory.lift_sub]
QED

Theorem prime_tm_npair:
  prime_tm x y = npair x y
Proof
  simp[prime_tm_def] >>
  simp[enumerationsTheory.dBnum_def,pure_dBTheory.fromTerm_thm] >>
  simp[churchnumTheory.church_def] >>
  simp[churchDBTheory.fromTerm_funpow_app] >>
  pure_dBTheory.fromTerm_thm,pure_dBTheory.fromTerm_eqn
QED



Theorem kolmog_fn_ub:
  computable f ==> ∃c. ∀m.
  plain_kolmog (f m) <= 2 * ((plain_kolmog m) + THE (kolmog_fn2 f)) + c
Proof
  rw[] >> qexists_tac`10` >> rw[] >>
  `(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
         ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j` by fs[recfn_index2_def] >>
  `Phi (recfn_index2 f) m = SOME (f m)` by fs[] >>
  `Phi (prime_tm (THE (kolmog_fn2 f)) m) 0 = SOME (f m)` by fs[kolmog_fn2_def,prime_tm_corr] >>
  `plain_kolmog (f m) ≤ ℓ (prime_tm (THE (kolmog_fn2 f)) m)` by fs[plain_kolmog_smallest] >>
  `ℓ (prime_tm (THE (kolmog_fn2 f)) m) <= 2 * (THE (kolmog_fn2 f) + plain_kolmog m) + 10`
    suffices_by fs[] >>

QED

Theorem kol_fkmin_lb:
  computable plain_kolmog ==> ∃c. ∀m. plain_kolmog (fkmin m) <= (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) + c
Proof
  rw[] >> qexists_tac`m` >> rw[] >> cheat
QED

Theorem kolmog_length_ub:
  ∃c. ∀m. plain_kolmog m <= (ℓ m) + c
Proof
  `∃i0. ∀x. Phi i0 x = SOME x` by stuff >>
  `∀m. plain_kolmog m <= ℓ (prime_tm i0 m)`
    by (rw[] >> `Phi (prime_tm i0 m) 0 = SOME m` by fs[prime_tm_corr] >> fs[plain_kolmog_smallest]) >>
  `∃k. ∀m. ℓ (prime_tm i0 m) <= LENGTH ((n2bl m) ++ (n2bl i0)) +k`
    by (simp[prime_tm_def,pure_dBTheory.fromTerm_def,enumerationsTheory.dBnum_def] >> ) >>
  `∀m. LENGTH ((n2bl m) ++ (n2bl i0)) +k  <= (ℓ m) + ((ℓ i0) + k)` by (rw[]>>fs[LENGTH_APPEND]) >>
  qexists_tac`ℓ i0 + k` >> strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

Theorem kolmog_length_ub_corrol:
  ∃c. ∀m. plain_kolmog m <= 2*(ℓ m) + c
Proof

QED

Theorem kol_fkmin_ub:
  computable plain_kolmog ==> ∃c. ∀m. (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) <= 2*(LENGTH (n2bl m)) + c
Proof
  cheat
QED

Theorem compkol_lb:
  computable plain_kolmog ==> ∃c. ∀m. m <=  2*(LENGTH (n2bl m)) + c
Proof
  rw[] >> `∃c. ∀m. m <= (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) + c ` by
            metis_tac[kfkmin_lb,kol_fkmin_lb,LESS_EQ_TRANS] >>
  `∃c. ∀m. (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) <= 2*(LENGTH (n2bl m)) + c ` by metis_tac[kol_fkmin_ub] >> qexists_tac`c+c'` >>
  `∀m. plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x)))+c ≤
         2 * ℓ m + c'+c` by fs[] >>
  rw[] >> `plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x))) + c ≤
             2 * ℓ m + c' + c` by fs[] >>
  `m ≤ plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x))) + c` by fs[] >>
  fs[LESS_EQ_TRANS]
QED

Theorem exists_log_lb:
  ∃m. ¬(m<= 2*(LENGTH (n2bl m)) + c)
Proof
  cheat
QED

Theorem part_hutter:
  computable plain_kolmog ==> F
Proof
  strip_tac >> `∃c. ∀m. m <=  2*(LENGTH (n2bl m)) + c` by  fs[compkol_lb] >>
  `∃m. ¬(m<= 2*(LENGTH (n2bl m)) + c)` by fs[exists_log_lb] >> metis_tac[]
QED

*)


(* unproven *)

(* j-machine is passed an n.

   Then, for every string y of length 2n with complexity < 2n, then generate
   the list of triples (yi,Mi,ti), where yi is one of the ys, and
   Mi (0) = SOME yi, and that computation takes ti steps
*)

(*
Theorem part2:
  computable kolmog ==>
  ∃j. ∀n. ∃l. Phi j n = SOME (nlist_of l) ∧
              (∀e. MEM e l <=> ∃yi Mi ti. yMt_pred e n yi Mi ti)
Proof
     rw[computable_def] >> arg_plain_kolmog2_def]
QED
*)

(* unproven *)

(* Not needed *)

(*
val yMt_set_def = Define‘
  yMt_set n = {(yi,Mi,t) | ∃e. yMt_pred e n yi Mi t }
’;

val big_T_def = Define`big_T n = MAX_SET (IMAGE SND (IMAGE SND (yMt_set n)))`
*)
(*

For our argument, we basically need to show that big_T is computable,
Therefore using part3 and part4 we can run our computable TM (prime_tm M x) for a computable time
(big_T) and we will be able to determine whether or not (M,x) halted

Since max and nsnd are comptuable, we should be able to use part22 to show big_T is computable

prtermTheory.primrec_max,primrecfnsTheory.primrec_nsnd

*)

(* unproven *)



Theorem terminated_ge:
  (b < a) ==> (terminated (steps b cs) ==> terminated (steps a cs))
Proof
  rw[] >> `∃c. c>0 ∧  a = b+c` by (qexists_tac`a-b` >> fs[]) >> rw[] >>
  `step1 (steps b cs) = steps b cs` by fs[terminated_step_in_place] >>
  `terminated (steps (c + b) cs)` suffices_by fs[] >>
  simp[steps_def,FUNPOW_ADD] >>
  Induct_on`c` >> rw[] >> Cases_on`c` >> fs[]
  >- (fs[steps_def])
  >- (fs[FUNPOW,steps_def] >> metis_tac[])
QED

Theorem log_ub:
  1<a ∧ 0 < b ==> (LOG a b = m ==> b<a ** SUC m)
Proof
  rw[] >> fs[LOG]
QED

Theorem finite_logeq:
  1<a ==> FINITE {b | LOG a b = m}
Proof
  rw[] >> `{b | LOG a b = m} SUBSET {b | b<a ** SUC m}` by
             (fs[SUBSET_DEF] >> rw[]>> Cases_on`x` >> fs[LOG]) >>
  `FINITE {b | b < a ** SUC m}` by (`FINITE (count (a ** SUC m))`
     suffices_by metis_tac[count_def] >>
  fs[FINITE_COUNT] ) >> metis_tac[SUBSET_FINITE_I]
QED

Theorem finite_log2:
  FINITE {x | LOG 2 x = LOG 2 (SUC m)}
Proof
  qabbrev_tac`n = LOG 2 (SUC m) ` >> `(1:num)<2` by fs[] >> fs[finite_logeq]
QED

Theorem FUNPOW_id:
  f x = x ==> FUNPOW f n x = x
Proof
  rw[] >> Induct_on`n` >> fs[] >> rw[FUNPOW]
QED

Theorem terminated_imp:
  ¬terminated (steps (t-1) (mk_initial_state M x)) ∧
  terminated (steps t (mk_initial_state M x))
    ==>
  Phi M x = SOME (cs_to_num (steps t (mk_initial_state M x)))
Proof
  rw[] >> fs[Phi_steps] >> `comp_count (mk_initial_state M x) = SOME t`
    suffices_by fs[] >>
  fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac >>
  `∃c.0<c ∧ n+c = t` by (qexists_tac`t-n` >> fs[]) >> rw[] >>
  ‘steps (n + c) (mk_initial_state M x) =
   steps (n + c - 1) (mk_initial_state M x)’
  by (
   `step1 (steps n (mk_initial_state M x)) = (steps n (mk_initial_state M x))`
     by fs[terminated_step_in_place] >> fs[steps_def] >>
   `FUNPOW step1 (c + n) (mk_initial_state M x) =
      FUNPOW step1 ((c-1) + n) (mk_initial_state M x)`
   suffices_by fs[] >>fs[FUNPOW_ADD] >>
   fs[FUNPOW_id]
  ) >> metis_tac[]
QED

Theorem terminated_down:
  (¬(terminated (steps 0 (mk_initial_state M x)) ) ∧ terminated (steps t (mk_initial_state M x)))
    ==> ∃tl. tl<t ∧ ¬terminated (steps tl (mk_initial_state M x)) ∧  terminated (steps (tl+1) (mk_initial_state M x))
Proof
  rw[] >> Induct_on`t` >> fs[] >>
  rw[] >> Cases_on` terminated (steps t (mk_initial_state M x))` >>  fs[]
  >- (qexists_tac`tl` >> fs[])
  >- (qexists_tac`t` >> fs[ADD1])
QED

Theorem terminated_impdown:
  (¬(terminated (steps 0 (mk_initial_state M x)) ) ∧ terminated (steps t (mk_initial_state M x)))
    ==> ∃tl. Phi M x = SOME (cs_to_num (steps tl (mk_initial_state M x) ))
Proof
  rw[] >> `∃tll. tll<t ∧ ¬terminated (steps tll (mk_initial_state M x)) ∧
                 terminated (steps (tll+1) (mk_initial_state M x))` by
            metis_tac[terminated_down] >> qabbrev_tac`tk = tll+1` >>
  `tk-1 = tll` by fs[Abbr`tk`] >> rw[] >>
  `Phi M x = SOME (cs_to_num (steps (tk) (mk_initial_state M x) ))` by
    metis_tac[terminated_imp]>> qexists_tac`tk` >> fs[]
QED

Theorem correctness_on_nontermination_contrapos:
 (∃x. Phi i n = SOME x) ==> ∃y. comp_count (mk_initial_state i n) = SOME y
Proof
  metis_tac[correctness_on_nontermination,optionTheory.option_CLAUSES]
QED

Theorem correctness_on_termination_contrapos:
 ( Phi i n = NONE) ==> comp_count (mk_initial_state i n) = NONE
Proof
  metis_tac[correctness_on_termination,optionTheory.option_CLAUSES]
QED

Theorem prime_tm_mk_comp_initial_state_NONE:
  comp_count (mk_initial_state (prime_tm M x) 0) = NONE <=>
  comp_count (mk_initial_state M x) = NONE
Proof
  eq_tac >> rw[]
  >- (`Phi (prime_tm M x) 0 = NONE` by fs[correctness_on_nontermination] >>
      `Phi M x = NONE` by fs[prime_tm_corr] >>
      fs[correctness_on_termination_contrapos])
  >- (`Phi M x = NONE` by fs[correctness_on_nontermination] >>
      `Phi (prime_tm M x) 0 = NONE` by fs[prime_tm_corr] >>
      fs[correctness_on_termination_contrapos])
QED

Theorem prime_tm_mk_comp_initial_state_SOME:
  (∃t1. comp_count (mk_initial_state (prime_tm M x) 0) = SOME t1) <=>
  (∃t2. comp_count (mk_initial_state M x) = SOME t2)
Proof
  eq_tac >> rw[]
  >- (`terminated (steps t1 (mk_initial_state (prime_tm M x) 0)) ∧
       Phi (prime_tm M x) 0 = SOME (cs_to_num (steps t1 (mk_initial_state (prime_tm M x) 0)))` by
        metis_tac[correctness_on_termination] >>
      `Phi M x = SOME (cs_to_num (steps t1 (mk_initial_state (prime_tm M x) 0)))` by
        fs[prime_tm_corr] >>
      fs[correctness_on_nontermination_contrapos])
  >- (`terminated (steps t2 (mk_initial_state M x)) ∧
       Phi M x = SOME (cs_to_num (steps t2 (mk_initial_state M x)))` by
         metis_tac[correctness_on_termination] >>
      `Phi (prime_tm M x) 0 = SOME (cs_to_num (steps t2 (mk_initial_state M x)))` by
        fs[prime_tm_corr] >>
      fs[correctness_on_nontermination_contrapos])
QED

Theorem prime_tm_termination:
  (∃t1. terminated (steps t1 (mk_initial_state (prime_tm M x) 0))) <=>
  (∃t2. terminated (steps t2 (mk_initial_state M x)))
Proof
  `(∃t1. comp_count (mk_initial_state (prime_tm M x) 0) = SOME t1) <=>
  (∃t2. comp_count (mk_initial_state M x) = SOME t2)` by fs[prime_tm_mk_comp_initial_state_SOME] >>
  fs[comp_count_def,OLEAST_def]
QED


Theorem terminated_le:
  (b <= a) ==> (terminated (steps b cs) ==> terminated (steps a cs))
Proof
  rw[] >> Cases_on`a=b` >> fs[] >> `b<a` by fs[] >> metis_tac[terminated_ge]
QED


Theorem ELL_FINITE:
  FINITE {m | ℓ m = k}
Proof
  simp[ELL_log2list] >> irule SUBSET_FINITE_I >>
  qexists_tac`IMAGE PRE (set (log2list k))` >> simp[SUBSET_DEF] >> rw[] >> qexists_tac`x+1`>>fs[]
QED

Theorem ELL_terminated_FINITE:
  FINITE {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧
                  ¬terminated (steps (t − 1) (mk_initial_state m 0))) ∧ ℓ m = k}
Proof
  fs[finite_and,ELL_FINITE]
QED

Theorem non_terminated_down:
  (¬terminated (steps t (mk_initial_state m x))) ==>
  (∀a. a<=t ==>  (¬terminated (steps a (mk_initial_state m x))))
Proof
  rw[] >> strip_tac >> metis_tac[terminated_le]
QED

Theorem comp_count_terminated:
  (terminated (steps x (mk_initial_state m y)) ∧
  ¬terminated (steps (x − 1) (mk_initial_state m y))) ==>
  THE (comp_count (mk_initial_state m y)) = x
Proof
  rw[] >> `Phi m y = SOME (cs_to_num (steps x (mk_initial_state m y)))` by fs[terminated_imp]>>
  fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m y)` >> fs[] >>
  `(∀a. a<=x-1 ==> (¬terminated (steps a (mk_initial_state m y))))` by
    metis_tac[non_terminated_down] >>  fs[comp_count_def,OLEAST_def] >> rw[]>>
  numLib.LEAST_ELIM_TAC >> rw[] >- metis_tac[] >>
  `(∀a. a<x ==> (¬terminated (steps a (mk_initial_state m y))))` by fs[] >>
  metis_tac[DECIDE``x:num < y ∨ x=y ∨ y<x ``]
QED

Theorem ELL_SURJ_terminate:
  SURJ (λm. THE (comp_count (mk_initial_state m 0)))
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧
                  ¬terminated (steps (t − 1) (mk_initial_state m 0))) ∧ ℓ m = k}
  {t |(∃m.  terminated (steps t (mk_initial_state m 0)) ∧
           ¬terminated (steps (t − 1) (mk_initial_state m 0)) ∧
           ℓ m = k)}
Proof
  fs[SURJ_DEF] >> rw[] >> qexists_tac`m`
  >- (metis_tac[comp_count_terminated])
  >- (rw[] >- (qexists_tac`x` >> fs[comp_count_terminated])
      >- (fs[comp_count_terminated] ) )
QED

Theorem terminated_imp2:
 ((∀t'. terminated (steps t' (mk_initial_state M x)) ⇒ t ≤ t') ∧
     terminated (steps t (mk_initial_state M x))) ⇒
     Phi M x = SOME (cs_to_num (steps t (mk_initial_state M x)))
Proof
  rw[] >> Cases_on`t=0`
  >- ( fs[Phi_steps] >> `comp_count (mk_initial_state M x) = SOME t`
      suffices_by fs[] >>
      fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >>
  `¬terminated (steps (t − 1) (mk_initial_state M x))` by
    (strip_tac >> fs[] >> `t<=t-1` by fs[] >> fs[PRE_SUB1])  >>
  fs[terminated_imp]
QED

Theorem comp_count_terminated2:
  (terminated (steps t (mk_initial_state m y)) ∧
  (∀t'. terminated (steps t' (mk_initial_state m y)) ⇒ t ≤ t')) ==>
  THE (comp_count (mk_initial_state m y)) = t
Proof
  rw[] >> Cases_on`t=0`
  >- (`Phi m y = SOME (cs_to_num (steps t (mk_initial_state m y)))` by fs[terminated_imp2]>>
      `comp_count (mk_initial_state m y) = SOME t` suffices_by fs[] >>
      fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >>
  `¬terminated (steps (t − 1) (mk_initial_state m y))` by
    (strip_tac >> fs[] >> `t<=t-1` by fs[] >> fs[])  >> fs[comp_count_terminated]
QED


Theorem ELL_terminated_FINITE2:
  FINITE {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧
               (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ) ∧ ℓ m = k}
Proof
  fs[finite_and,ELL_FINITE]
QED

Theorem ELL_SURJ_terminate2:
  SURJ (λm. THE (comp_count (mk_initial_state m 0)))
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧
                 (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ) ∧ ℓ m = k}
  {t |(∃m. terminated (steps t (mk_initial_state m 0)) ∧
           (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
           ℓ m = k)}
Proof
  fs[SURJ_DEF] >> rw[] >> qexists_tac`m`
  >- (metis_tac[comp_count_terminated2])
  >- (rw[] >- (qexists_tac`x` >> fs[comp_count_terminated2])
      >- (fs[comp_count_terminated2] ) )
QED


Theorem terminated_tmax:
  (∃t. terminated (steps t (mk_initial_state (prime_tm M x) 0))) ==>
  terminated (steps (tmax (ℓ (prime_tm M x))) (mk_initial_state (prime_tm M x) 0))
Proof
  rw[] >> Cases_on`terminated (steps 0 (mk_initial_state (prime_tm M x) 0))`
  >- (Cases_on`0<tmax (ℓ (prime_tm M x))` >>fs[]>> metis_tac[terminated_ge]) >>
  `∃tl. tl < t ∧ ¬terminated (steps tl (mk_initial_state (prime_tm M x) 0)) ∧
        terminated (steps (tl + 1) (mk_initial_state (prime_tm M x) 0))` by
    fs[terminated_down] >>
  rw[tmax_def]>> qabbrev_tac`s = {t |
            (∃m.
                 terminated (steps t (mk_initial_state m 0)) ∧
                 (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
                 ℓ m = ℓ (prime_tm M x))}` >>
  `s <> {}` by
    (fs[Abbr`s`,EXTENSION] >> qexists_tac`tl+1` >> qexists_tac`prime_tm M x` >> rw[] >>
     `∀a. a ≤ tl ⇒ ¬terminated (steps a (mk_initial_state (prime_tm M x) 0))` by
       metis_tac[non_terminated_down] >> Cases_on`tl + 1 ≤ t'` >> rw[] ) >>
  `(tl+1) ∈ s` by (fs[Abbr`s`,IN_DEF] >> qexists_tac`prime_tm M x` >> rw[] >>
                   Cases_on`tl + 1 ≤ t'` >> fs[] >> `t'<=tl` by fs[]>> metis_tac[non_terminated_down])>>
  `FINITE s` by (fs[Abbr`s`] >>
                 metis_tac[ELL_SURJ_terminate2,FINITE_SURJ,ELL_terminated_FINITE2]) >>
  `tl+1<=MAX_SET s` by metis_tac[in_max_set] >>metis_tac[terminated_le]
QED



Theorem part4:
  tmax (ℓ (prime_tm M x) ) < n ⇒
  (terminated (steps n
                     (mk_initial_state (prime_tm M x) 0 ))
      <=>
   (M,x) ∈ HALT)
Proof
  rw[] >> eq_tac >> rw[HALT_def]
  >- (metis_tac[prime_tm_termination])
  >- (`terminated (steps (tmax (ℓ (prime_tm M x))) (mk_initial_state (prime_tm M x) 0))`
        suffices_by (metis_tac[terminated_ge]) >>
      `∃t1. terminated (steps t1 (mk_initial_state (prime_tm M x) 0))` by
        metis_tac[prime_tm_termination] >>
      metis_tac[terminated_tmax])
QED

(*

Theorem Phi_halt:
  Phi (THE (Phi i x)) y = Phi i y ==>
Proof

QED

Theorem partall:
  (computable plain_kolmog ∧ computable arg_plain_kolmog) ==> F
Proof
  strip_tac >> fs[computable_def] >>
  `Phi i 0 = SOME (plain_kolmog 0)` by fs[] >>
  `Phi i' 0 = SOME (arg_plain_kolmog 0)`by fs[] >>
  `Phi (arg_plain_kolmog ((plain_kolmog 0))) 0 = SOME (plain_kolmog 0)` by fs[] >>
  `Phi (arg_plain_kolmog (plain_kolmog 0)) 0  = Phi i 0` by fs[] >>

  `Phi (arg_plain_kolmog (arg_plain_kolmog 0)) 0 = SOME (arg_plain_kolmog 0)` by fs[]>>
  `Phi (arg_plain_kolmog (arg_plain_kolmog 0)) 0 = Phi i' 0` by fs[] >>

  `Phi i' (arg_plain_kolmog 0) = SOME (arg_plain_kolmog (arg_plain_kolmog 0))` by fs[] >>

  `Phi (THE (Phi i' (arg_plain_kolmog 0))) 0 = Phi i' 0` by metis_tac[optionTheory.THE_DEF]>>

  pop_assum (K ALL_TAC) >> simp[plain_kolmog_def,kolmog_complexity_def]
QED



val newymt_def = Define`newymt e n yi Mi ti ⇔
         plain_kolmog yi <= 2 * n ∧
         terminated (steps ti (mk_initial_state Mi 0)) ∧
         cs_to_num (steps ti (mk_initial_state Mi 0)) = yi ∧
         (∀t'. terminated (steps t' (mk_initial_state Mi 0)) ⇒ ti ≤ t') ∧
         e = yi ⊗ Mi ⊗ ti`

val newymt_set_def = Define‘
  newymt_set n = {(yi,Mi,t) | ∃e. newymt e n yi Mi t }
’;

val newbig_T_def = Define`newbig_T n = MAX_SET (IMAGE SND (IMAGE SND (newymt_set n)))`

Theorem plain_kolmog_ub:
  comp_count (mk_initial_state m 0) = SOME t ==> plain_kolmog
     (cs_to_num
        (steps (THE (comp_count (mk_initial_state m 0)))
           (mk_initial_state m 0))) <= ℓ m
Proof
  rw[] >> fs[plain_kolmog_def,kolmog_complexity_def] >> rw[Phi_bl2nx_0]
  >- (`∃x. Phi (bl2n x) 0 = SOME (cs_to_num
          (steps t
             (mk_initial_state m 0)))` by fs[Phi_bl2nx_0] >> fs[EXTENSION] >> metis_tac[])>>
  qabbrev_tac`s = {LENGTH y | Phi (bl2n y) 0 = SOME (cs_to_num
           (steps t
              (mk_initial_state m 0)))}` >> `s<> {}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0]>>
  `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `ℓ m ∈ s` suffices_by fs[] >>
  `(n2bl m) ∈ {y | Phi (bl2n y) 0 =SOME
            (cs_to_num
               (steps t
                  (mk_initial_state m 0)))}` by
         fs[IN_DEF,Phi_steps] >>
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[])
QED



Theorem newymt_SURJ:
  SURJ
  (λm. (cs_to_num (steps (THE (comp_count (mk_initial_state m 0))) (mk_initial_state m 0)),
        m,
        THE (comp_count (mk_initial_state m 0)) ) )
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧
           (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t')) ∧ ℓ m <= 2 * n}
  (newymt_set n)
Proof
  fs[SURJ_DEF] >> rw[]
  >- (fs[IN_DEF,newymt_set_def,newymt_def] >>
      qexists_tac`(cs_to_num (steps (THE (comp_count (mk_initial_state m 0)))
                                    (mk_initial_state m 0)),
                   m,
                   THE (comp_count (mk_initial_state m 0)))` >> simp[] >>rw[]
      >- (`THE (comp_count (mk_initial_state m 0))=t` by fs[comp_count_terminated2] >>
          `plain_kolmog (cs_to_num (steps (THE (comp_count (mk_initial_state m 0)))
            (mk_initial_state m 0))) <= ℓ m` suffices_by (fs[]) >>
          irule plain_kolmog_ub >> irule correctness_on_nontermination_contrapos >>
          qexists_tac`cs_to_num (steps t (mk_initial_state m 0))` >> fs[terminated_imp2] )
      >- (simp[comp_count_def,OLEAST_def] >> rw[] >> fs[] >> numLib.LEAST_ELIM_TAC >>
          rw[] >> qexists_tac`t` >> fs[] )
      >- (`THE (comp_count (mk_initial_state m 0))=t` by fs[comp_count_terminated2] >>
          `t<= t'` suffices_by fs[] >>  fs[] ) ) >>
  qexists_tac`FST (SND x)` >> rw[]
  >- (qexists_tac`SND (SND x)` >> rw[] >> fs[newymt_set_def,newymt_def] >>
      `FST (SND x) = Mi` by fs[] >> fs[] )
  >- (fs[newymt_set_def,newymt_def] >>
      `THE (comp_count (mk_initial_state Mi 0))=t` by fs[comp_count_terminated2] >>
          irule plain_kolmog_ub       fs[plain_kolmog_ub])
  >- (fs[newymt_set_def,newymt_def] >> rw[comp_count_terminated2] >>
      `THE (comp_count (mk_initial_state Mi 0)) = t` by fs[comp_count_terminated2] >> fs[])
QED

Theorem FINITE_newymt_set:
  FINITE (newymt_set n)
Proof
  fs[newymt_set_def,newymt_def]
QED

Theorem newpart3plus:
  tmax (ℓ (prime_tm M x) ) <= newbig_T (prime_tm M x)
Proof
  rw[] >> fs[tmax_def,newbig_T_def] >> irule SUBSET_MAX_SET >>
  rw[] >- metis_tac[ELL_SURJ_terminate,FINITE_SURJ,ELL_terminated_FINITE]
  >- metis_tac[FINITE_newymt_set,IMAGE_FINITE] >> fs[SUBSET_DEF] >> rw[] >>
  simp[newymt_set_def,newymt_def] >>
  qexists_tac`(m,x')` >> rw[] >>
  qexists_tac`(cs_to_num (steps x' (mk_initial_state m 0)),m,x')` >> rw[]
  >- (fs[plain_kolmog_def,kolmog_complexity_def] >>
      `{y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))} <> ∅` by
        fs[EXTENSION,Phi_bl2nx_0] >> fs[] >>
       `x' = THE (comp_count (mk_initial_state m 0)) ` by metis_tac[comp_count_terminated]>>
       `Phi m 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))` by
         (fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m 0)` >> fs[comp_count_def])>>
       `ℓ m <= 2 * prime_tm M x` by
         (`ℓ m <= (prime_tm M x)` by fs[ELL_LE] >> `prime_tm M x <= 2 * (prime_tm M x)` by fs[]>>
          fs[]) >>
       qabbrev_tac`s={LENGTH y |
       Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` >>
       `MIN_SET s <= ℓ m` suffices_by fs[] >>
       `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >>
       `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >> `ℓ m∈s` suffices_by fs[] >>
       `(n2bl m) ∈ {y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` by
         fs[IN_DEF] >>
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[])    )
  >- (`∀a. a ≤ (x'-1) ⇒ ¬terminated (steps a (mk_initial_state m 0))` by
        metis_tac[non_terminated_down] >> Cases_on`x'<=t'` >> fs[])
QED


Theorem FINITE_yMt_set:
  FINITE (yMt_set n)
Proof
  cheat (*  fs[newymt_set_def,newymt_def]  *)
QED

Theorem arg_kolmog_size_genlist:
  LENGTH (n2bl (arg_plain_kolmog (bl2n (GENLIST (λn. T) n) ))) < n
Proof
  cheat (*  fs[arg_plain_kolmog] *)
QED




val Z_lam2_def = Define‘
  Z_lam2 M =
   λx. case comp_count (mk_initial_state M 0) of
           NONE => NONE
         | SOME s =>
           let results =
                 OGENLIST  (λmi. if terminated (steps s (mk_initial_state mi 0))
                                 then
                                   SOME (cs_to_num (steps s
                                                      (mk_initial_state mi 0)))
                                 else NONE)
                           (4**n DIV 2)
           in
             SOME (LEAST x. ¬MEM x results ∧ ℓ x = 2*n)
’;

Theorem Z_lam_size:
  ℓ (Z_lam M n x) = 2 * n
Proof

QED

Theorem Z_lam_machine_size:

Proof

QED

Theorem oldpart3plus:
  tmax (ℓ (prime_tm M x) ) <= big_T (ℓ (prime_tm M x))
Proof
  rw[] >> fs[tmax_def,big_T_def] >> irule in_max_set >>
  rw[]
  >- metis_tac[FINITE_yMt_set,IMAGE_FINITE] >> fs[IN_DEF] >> rw[] >>
  simp[yMt_set_def,yMt_pred_def] >>
  qexists_tac`(m1,t1)` >> rw[] >- () >> qexists_tac`(y1,m1,t1)` >> rw[] >>qexists_tac`(y1,m1,t1)` >> rw[] >>


  qexists_tac`(arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[] >- (rw[]) >>
  qexists_tac`(bl2n (GENLIST (λn. T) (2*prime_tm M x)),arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[] >> qexists_tac`(bl2n (GENLIST (λn. T) (2*prime_tm M x)),arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[]
  >- ()
  >- ()
  >- ()
  >- ()
  >- ()


  >- (fs[plain_kolmog_def,kolmog_complexity_def] >>
      `{y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))} <> ∅` by
        fs[EXTENSION,Phi_bl2nx_0] >> fs[] >>
       `x' = THE (comp_count (mk_initial_state m 0)) ` by metis_tac[comp_count_terminated]>>
       `Phi m 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))` by
         (fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m 0)` >> fs[comp_count_def])>>
       `ℓ m <= 2 * prime_tm M x` by
         (`ℓ m <= (prime_tm M x)` by fs[ELL_LE] >> `prime_tm M x <= 2 * (prime_tm M x)` by fs[]>>
          fs[]) >>
       qabbrev_tac`s={LENGTH y |
       Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` >>
       `MIN_SET s <= ℓ m` suffices_by fs[] >>
       `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >>
       `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >> `ℓ m∈s` suffices_by fs[] >>
       `(n2bl m) ∈ {y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` by
         fs[IN_DEF] >>
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[])    )
  >- (`∀a. a ≤ (x'-1) ⇒ ¬terminated (steps a (mk_initial_state m 0))` by
        metis_tac[non_terminated_down] >> Cases_on`x'<=t'` >> fs[])
QED

*)


(* OLD PART 3
Theorem part3:
  computable plain_kolmog ∧ ((Z_lam (prime_tm M x) (ℓ (prime_tm M x)) (0:num)) = SOME y)  ==>
  tmax (ℓ (prime_tm M x) ) < big_T (prime_tm M x)
Proof
  rw[] >>
  `∃z. Phi z = Z_lam (prime_tm M x) (ℓ (prime_tm M x)) ∧ ℓ z < 2 * (ℓ (prime_tm M x))` by
    fs[Z_lam_computable_size] >>
  Cases_on`tmax (ℓ (prime_tm M x)) < big_T (prime_tm M x)` >> fs[] >>
  `plain_kolmog y = (2*(ℓ (prime_tm M x)))` by metis_tac[Z_lam_output_size] >>
  fs[plain_kolmog_def,kolmog_complexity_def] >>
  `{y' | Phi (bl2n y') 0 = SOME y} <> ∅` by fs[EXTENSION,Phi_bl2nx_0] >>
  fs[] >>
  `ℓ z < MIN_SET {LENGTH y' | Phi (bl2n y') 0 = SOME y}` by fs[] >>
  qabbrev_tac`s={LENGTH y' | Phi (bl2n y') 0 = SOME y}` >>
  `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >>
  `MIN_SET s ∈ s ∧ ∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `(n2bl z) ∈ {y' | Phi (bl2n y') 0 = SOME y}` by fs[IN_DEF] >>
  `LENGTH (n2bl z) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl z` >> fs[])>>
  `MIN_SET s <= ℓ z` by fs[] >> fs[]
QED
*)


(*
Theorem big_T_Tmax_imp:
  (Big_T (LOG 2 (prime_tm M x) ) > tmax (LOG 2 (prime_tm M x) )) ==>
   ( terminated (steps (big_T  (LOG 2 (prime_tm M x))) (mk_initial_state (prime_tm M x) 0 ))  <=> ((M,x)∈HALT ))
Proof
  rw[] >> eq_tac >> rw[]
  >- (fs[HALT_def] >> qexists_tac`big_T (LOG 2 (prime_tm M x))` >>
      `∃m. comp_count  (mk_initial_state (prime_tm M x) 0) = SOME m` by
        (fs[comp_count_def]>>
         `¬((OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0))) = NONE)` by
           (fs[OLEAST_EQ_NONE] >> qexists_tac` (big_T (LOG 2 (prime_tm M x)))` >> fs[]) >>
        qexists_tac`THE (OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0)))`>>
        `IS_SOME  (OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0)))`
          suffices_by fs[quantHeuristicsTheory.SOME_THE_EQ ]  >>
        fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
        qexists_tac`n` >> fs[]) >>
      `terminated (steps m (mk_initial_state (prime_tm M x) 0)) ∧ Phi (prime_tm M x) 0 =
       SOME (cs_to_num (steps m (mk_initial_state (prime_tm M x) 0)))` by
        (fs[correctness_on_termination] >> fs[comp_count_def,OLEAST_EQ_SOME]) >>
      fs[prime_tm_corr] >>
      `tmax (LOG 2 (prime_tm M x)) = m` by (fs[tmax_def] >> fs[comp_count_def])

       `terminated (steps (tmax (LOG (prime_tm M x) 2)) (mk_initial_state M x))` suffices_by
         metis_tac[terminated_ge] >>  )
  >- (fs[HALT_def] >> Cases_on`terminated (steps 0 (mk_initial_state M x))`
      >- (fs[])
      `terminated (steps (tmax (LOG 2 (prime_tm M x)))
       (mk_initial_state (prime_tm M x) 0))` suffices_by metis_tac[terminated_ge] >>
      fs[tmax_def] >> qmatch_abbrev_tac`terminated (steps (MAX_SET ts)
                                        (mk_initial_state (prime_tm M x) 0))` >>
      `FINITE ts` by (cheat) >>
      `ts <> {}` by (cheat) >>
      `MAX_SET ts ∈ ts ∧ ∀y. y ∈ ts ⇒ y ≤ MAX_SET ts` by fs[MAX_SET_DEF] >>  )
  fs[big_T_def] >> fs[tmax_def],yMt_set_def,IMAGE_DEF] >>  >>
  comp_count_def,correctness_on_termination
QED

*)

(*
val find_m_of_size_n_gen_y_def = Define`find_m_of_size_n_gen_y = LAM "n" (LAM "y"
  (dt @@ (ceqnat @@ VAR "y")
      @@ (cmap @@ (C @@ cpair @@ cnil)
               @@ (ctabulate ) )) )`

Theorem kol_dove:
  (∀x. Phi f x = SOME (kolmog x)) ==>
Proof

QED

val _ = Q.store_thm("_",
`∀n. n>const1 ==> ∃Z. tm_size Z <2*n ∧ `,
)

val _ Q.store_thm("_",
`¬∃f. ∀x. kolmog x = recPhi [f;x] ==> ∀y. LENGTH y = l ==> kolmog y`,
)



Theorem ub_tmax: big_T n > tmax n
Proof
  fs[big_T_def,tmax_def]
QED

val ub_implies_halt = Q.store_thm("ub_implies_halt",
`big_T > t_max (tm_size M') ==> (M',[]) ∈ HALT`,
)

val m_prime_implies_halt = Q.store_thm("m_prime_implies_halt",
`(primt_tm M,[]) ∈ HALT ==> (M,x)∈HALT`,
)

(* maybe want arg kolmog *)

val kolmog_non_comp = Q.store_thm("kolmog_non_comp",
`¬∃f. ∀x. kolmog x = recPhi [f;x]`,
strip_tac >> )



(* Not sure if needed  *)

(*

val pr_log2_pr = Q.store_thm("pr_log2_pr",
`primrec (pr_log2) 1`,
simp[pr_log2_def] >> irule primrec_WFM >> irule primrec_pr2 >> simp[restr_def]>>
qexists_tac`` )

val pr_nbar = Q.store_thm("pr_nbar",
`nbar n = n* 2**(pr_log2 [n] +1)+ (3*2**(pr_log2 [n])) - 1 `,
Induct_on`n` >> simp[nbar_def])

val recfn_nbar = Q.store_thm("recfn_nbar",
`recfn (rec1 (SOME o nbar)) 1`,
irule recfn_rec1 >> qexists_tac`SOME o (λl. nbar (HD l))` >> rw[] >> irule primrec_recfn >>
)



val leastR_def = Define`leastR R A = @a. a IN A /\ !b. b IN A ==> ~R b a`

val order_def = tDefine"order"`(order A R 0 = leastR R A) /\
                (order A R (SUC n) = leastR R (A DIFF IMAGE (\i. order A R i) (count (SUC n))))`(WF_REL_TAC`measure (SND o SND)` >> simp[])

val tmorder_def = Define`tmorder x = order {p | universal_tm p = x} `

val listlex_def = Define`(listlex [] x <=> x<>[])/\(listlex (h::t) [] <=> F)/\
                         (listlex (h1::t1) (h2::t2) <=>
                         (LENGTH t1 < LENGTH t2) \/ ((LENGTH t1 = LENGTH t2) /\ ((h1=h2) /\ listlex t1 t2 \/ ~h1 /\ h2 )  ) )`

val listlex_length = Q.store_thm("listlex_length",
`!a b. LENGTH a < LENGTH b ==> listlex a b`,
Cases_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def])

val listlex_length2 = Q.store_thm("listlex_length2",
`!a b. listlex a b ==> (LENGTH a <= LENGTH b)`,
Induct_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def] >> rpt strip_tac >>
simp[])

val listlex_empty = Q.store_thm("listlex_empty[simp]",
`listlex a [] <=> F`,
Cases_on `a` >> simp[listlex_def])

val listlex_same_length = Q.store_thm("listlex_same_length",
`!B l w. (!b. B b ==> (LENGTH b = l)) /\ B w ==> ?v. B v /\ (!b. listlex b v ==> ~B b)`,
Induct_on `l` >> simp[] >- (rw[] >> qexists_tac`[]` >> simp[] >> metis_tac[]) >>
rw[] >> Cases_on`?hf. B' hf /\ (HD hf = F)`
>- (fs[] >>
    `?c. B' c /\ (HD c= F) /\ (!d. listlex d c ==> ~B' d)`
      by (first_x_assum(qspec_then`{t|B' (F::t)}`MP_TAC) >> simp[] >>
          disch_then(qspec_then`TL hf`MP_TAC) >> Cases_on `hf` >> simp[]
          >- (res_tac >> fs[]) >> fs[] >> impl_tac
              >- (rw[] >> res_tac>> fs[]) >>
              rw[] >> qexists_tac`F::v` >> simp[]>> rpt strip_tac >> Cases_on`d` >> fs[]
              >- (res_tac >> fs[])
              >- (fs[listlex_def] >- (res_tac >> fs[]) >> rw[] >> metis_tac[] ))>> metis_tac[])
>- (fs[] >>first_x_assum(qspec_then`{t|B' (T::t)}`MP_TAC) >> simp[] >> Cases_on `w`
    >- (res_tac >> fs[]) >> `h = T` by metis_tac[HD] >> rw[] >>
        pop_assum(qspec_then`t`MP_TAC) >> impl_tac
        >- (rw[] >> res_tac >> fs[]) >> rw[] >> qexists_tac`T::v` >> fs[] >> Cases_on `b`
            >- (rpt strip_tac >> res_tac >> fs[]) >> rw[listlex_def] >> strip_tac
                >- (res_tac >> fs[])
                >- (metis_tac[])
                >- (metis_tac[HD]) ) )

val WF_listlex = Q.store_thm("WF_listlex",`WF listlex`,
simp[relationTheory.WF_DEF] >> rw[] >>
`?v. B' v /\ !v'. B' v' ==> LENGTH v <= LENGTH v'`
  by (`WF (inv_image $< (LENGTH:bool list -> num) )` by (simp[relationTheory.WF_inv_image])>>
  fs[relationTheory.WF_DEF] >> metis_tac[NOT_LESS])>>
  qspecl_then[`{l|B' l /\ (LENGTH l = LENGTH v)}`,`LENGTH v`,`v`] MP_TAC listlex_same_length >>
  rw[] >> qexists_tac`v'` >> rw[] >> strip_tac >> `LENGTH b <> LENGTH v` by metis_tac[] >>
  `LENGTH v' < LENGTH b` by metis_tac[LESS_OR_EQ] >>
  `listlex v' b` by metis_tac[listlex_length] >>
  metis_tac[LESS_EQUAL_ANTISYM,listlex_length2,prim_recTheory.LESS_REFL] )

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
                            if n=0 then []
                            else if EVEN n then
                                T::num_to_bool_list((n-2) DIV 2)
                            else
                                F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC `$<` >> intLib.ARITH_TAC)

val solomonoff_prior_def = Define`
solomonoff_prior x = suminf (\n. let b = num_to_bool_list n in
                                     if universal_tm b = x
                                     then inv(2 pow (LENGTH b))
                                     else 0) `


val existence_of_universal_semimeasure = Q.store_thm("existence_of_universal_semimeasure",
`?M. (semimeasure M) /\ (universal_semimeasure M setX) /\ (continous M) /\ (lower_semicompute M)`,
qexists_tac `solomonoff_prior` >> conj_tac)

val summed_square_error_a_def = Define`summed_square_a_error mu a n =
                                       sum for (x IN Bstar:length x = n-1)
                                       (mu x) *(sqrt (cond_M a x) - sqrt (cond_mu a x))**2`

val summed_square_error_def = Define`summed_square_error mu n =
                                     sum for (a in B) summed_square_a_error mu a n`

val KL_dis_def = Define`KL_dis P Q = sum for (a in B) P(a)*log (P(a)/Q(a))`

val hellinger_dis_def = Define`hellinger_dis P Q = sum for (a in B) (sqrt(P(a)) - sqrt(Q(a)))**2`

val KL_greater_hellinger = Q.store_thm("KL_greater_hellinger",
`hellinger_dis P Q <= KL_dis P Q`,
)

val KL_M_dis_def = Define`KL_M_dis mu x = KL_dis (\y. cond_M y x) (\y. cond_mu y x)`

val sum_KL_M_dis_def = Define`sum_KL_M_dis mu n = sum for (x:length x = n-1)
                                                  (mu x) * (KL_M_dis mu x)`

val solomonoff_thm_claim_1 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==> summed_square_error mu n <= sum_KL_M_dis mu n`,
 )

val solomonoff_thm_claim_11 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==>
 sum for (n in N) summed_square_error mu n <= sum for (n in N) sum_KL_M_dis mu n`,
rw[sum_of_stuff,solomonoff_thm_claim_1] )

val solomonoff_thm_claim_2 = Q.store_thm("solomonoff_thm_claim_2",
`(computable_measure mu) ==> sum for (n in N) sum_KL_M_dis mu n <= (kolmog_complexity mu)*(log 2)`,
  )

val solomonoff_theorem = Q.store_thm("solomonoff_theorem",
`(computable_measure mu) ==>
 (sum for (n in N) summed_square_error mu n <= (kolmog_complexity mu)*(log 2) )`
rw[LESS_EQ_TRANS,solomonoff_thm_claim_11,solomonoff_thm_claim_2])
 *)



*)

*)
