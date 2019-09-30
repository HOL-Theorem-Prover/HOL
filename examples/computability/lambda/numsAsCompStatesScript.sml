open HolKernel Parse boolLib bossLib;

open prtermTheory

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


val _ = export_theory();
