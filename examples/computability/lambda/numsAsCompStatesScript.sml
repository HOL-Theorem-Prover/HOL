open HolKernel Parse boolLib bossLib;

open prtermTheory
open arithmeticTheory


val _ = new_theory "numsAsCompStates";

val _ = Datatype ‘compstate = CS num’;

val terminated_def = Define‘
  terminated (CS cs) ⇔ (pr_bnf [cs] = 1)
’

val step1_def = Define‘
  step1 (CS cs) = CS (pr_noreduct [cs])
’;

val steps_def = Define‘
  steps n cs = FUNPOW step1 n cs
’;

Theorem steps_pr_steps[simp]:
  ∀cs. steps n (CS cs) = CS (pr_steps [n; cs])
Proof
  simp[pr_steps_def,steps_def] >> Induct_on ‘n’ >>
  simp[arithmeticTheory.FUNPOW_SUC, step1_def] >>
  simp[SimpL “$==>”, Once pr_noreduct_correct] >> rw[] >>
  qmatch_abbrev_tac ‘_ = pr_noreduct [t]’ >> fs[] >>
  simp[pr_noreduct_correct]
QED

val cs_to_num_def = Define‘
  cs_to_num (CS cs) = pr_forcenum [cs]
’;

val mk_initial_state_def = Define‘
  mk_initial_state i n = CS (pr_dAPP [i; pr_church [n]])
’;

val comp_count_def = Define‘
  comp_count cs = OLEAST n. terminated (steps n cs)
’;

Theorem correctness_on_termination:
  (cs0 = mk_initial_state i n) ∧
  (comp_count cs0 = SOME m)
 ⇒
  terminated (steps m cs0) ∧
  (Phi i n = SOME (cs_to_num (steps m cs0)))
Proof
  simp[mk_initial_state_def, terminated_def, comp_count_def, steps_pr_steps] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
  Cases_on ‘steps m cs0’ >> simp[cs_to_num_def, terminated_def] >>
  rw[] >> fs[steps_pr_steps] >>
  REWRITE_TAC [GSYM recPhi_correct, recPhi_def] >>
  fs[recursivefnsTheory.recCn_def, pr_steps_correct] >>
  qabbrev_tac ‘M = toTerm (numdB i) @@ church n’ >> rw[] >> fs[] >>
  ‘bnf_of M = SOME (steps m M)’ by metis_tac [stepsTheory.bnf_steps] >>
  simp[]
QED

val lemma = stepsTheory.bnf_steps
  |> SIMP_RULE (srw_ss()) [ASSUME “bnf_of t = NONE”]
  |> Q.GEN ‘u’
  |> SIMP_RULE (srw_ss()) []
  |> DISCH_ALL

Theorem bnf_of_EQ_NONE_steps:
  (bnf_of t = NONE) ⇔ (∀n. ¬bnf (steps n t))
Proof
  eq_tac
  >- (spose_not_then strip_assume_tac >>
      ‘bnf_of t = SOME (steps n t)’ by metis_tac[stepsTheory.bnf_steps] >> fs[])
  >- (strip_tac >> Cases_on ‘bnf_of t’ >> simp[] >> fs[stepsTheory.bnf_steps] >>
      rw[] >> rfs[])
QED

Theorem correctness_on_nontermination:
  (cs0 = mk_initial_state i n) ∧ (comp_count cs0 = NONE) ⇒
  (Phi i n = NONE)
Proof
  csimp[mk_initial_state_def, comp_count_def, terminated_def, steps_pr_steps,
        pr_steps_correct] >>
  rw[] >> simp[recfunsTheory.Phi_def] >> simp[bnf_of_EQ_NONE_steps]
QED

Theorem Phi_steps:
  Phi i n = let cs0 = mk_initial_state i n
            in
              case comp_count cs0 of
                  NONE => NONE
                | SOME c => SOME (cs_to_num (steps c cs0))
Proof
  Cases_on ‘Phi i n’ >> rw[]
  >- (Cases_on ‘comp_count (mk_initial_state i n)’ >> simp[] >>
      drule (correctness_on_termination |> Q.GEN ‘cs0’ |> SIMP_RULE bool_ss[])>>
      simp[]) >>
  Cases_on ‘comp_count (mk_initial_state i n)’ >> simp[]
  >- (drule (correctness_on_nontermination |> Q.GEN ‘cs0’
                                           |> SIMP_RULE bool_ss[]) >>
      simp[]) >>
  fs[comp_count_def, mk_initial_state_def, pr_steps_correct] >>
  pop_assum mp_tac >> DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  simp[terminated_def] >> fs[recfunsTheory.Phi_def] >>
  simp[cs_to_num_def] >> rw[] >>
  qabbrev_tac ‘M = toTerm (numdB i) @@ church n’ >>
  rename [‘bnf_of M = SOME r’, ‘bnf (steps m M)’] >>
  ‘bnf_of M = SOME (steps m M)’ by metis_tac[stepsTheory.bnf_steps] >> fs[]
QED

Theorem unterminated_take_steps:
  (step1 cs = cs') ∧ cs' ≠ cs ⇒ ¬terminated cs
Proof
  Cases_on ‘cs’ >> simp[terminated_def, step1_def] >> rw[] >> strip_tac >>
  fs[pr_noreduct_correct]
QED

Theorem terminated_step_in_place:
  terminated cs ⇒ (step1 cs = cs)
Proof metis_tac[unterminated_take_steps]
QED


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
  fs[comp_count_def] >> fs[whileTheory.OLEAST_EQ_SOME] >> rw[] >> strip_tac >>
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

Theorem terminated_le:
  (b <= a) ==> (terminated (steps b cs) ==> terminated (steps a cs))
Proof
  rw[] >> Cases_on`a=b` >> fs[] >> `b<a` by fs[] >> metis_tac[terminated_ge]
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
    metis_tac[non_terminated_down] >>  fs[comp_count_def,whileTheory.OLEAST_def] >> rw[]>>
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
  fs[pred_setTheory.SURJ_DEF] >> rw[] >> qexists_tac`m`
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
      fs[comp_count_def] >> fs[whileTheory.OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >>
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
      fs[comp_count_def] >> fs[whileTheory.OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >> 
  `¬terminated (steps (t − 1) (mk_initial_state m y))` by 
    (strip_tac >> fs[] >> `t<=t-1` by fs[] >> fs[])  >> fs[comp_count_terminated]
QED




val _ = export_theory();
