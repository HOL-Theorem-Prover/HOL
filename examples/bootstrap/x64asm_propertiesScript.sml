
open HolKernel Parse boolLib bossLib BasicProvers;
open wordsTheory wordsLib arithmeticTheory listTheory pairTheory mp_then
     combinTheory x64asm_syntaxTheory x64asm_semanticsTheory relationTheory;

val _ = new_theory "x64asm_properties";

Inductive steps:
  (∀s (n:num).
    steps (s,n) (s,n))
  ∧
  (∀s1 s2 n.
    step s1 s2 ⇒ steps (s1,n) (s2,n))
  ∧
  (∀s1 s2 n.
    step s1 s2 ⇒ steps (s1,n+1) (s2,n))
  ∧
  (∀s1 n1 s2 n2 s3 n3.
    steps (s1,n1) (s2,n2) ∧
    steps (s2,n2) (s3,n3) ⇒ steps (s1,n1) (s3,n3))
End

Theorem step_consts:
  step (State t0) (State t1) ⇒
  t1.instructions = t0.instructions ∧
  ∀w x. read_mem w t0 = SOME x ⇒ read_mem w t1 = SOME x
Proof
  fs [step_cases] \\ rw [] \\ fs []
  \\ EVAL_TAC \\ fs []
  \\ fs [write_mem_def,AllCaseEqs(),read_mem_def] \\ rw []
  \\ fs [APPLY_UPDATE_THM]
  \\ rw [] \\ fs []
QED

Theorem steps_consts:
  ∀x y.
    steps x y ⇒
    (∀t1 m. y = (State t1,m) ⇒ ∃t0 n. x = (State t0,n)) ∧
    ∀t0 n t1 m.
      x = (State t0,n) ∧ y = (State t1,m) ⇒
      t1.instructions = t0.instructions ∧
      ∀w x. read_mem w t0 = SOME x ⇒ read_mem w t1 = SOME x
Proof
  ho_match_mp_tac steps_strongind \\ rw []
  \\ imp_res_tac step_consts \\ fs [] \\ rw [] \\ fs []
  \\ pop_assum mp_tac \\ fs [step_cases] \\ rw [] \\ fs []
QED

Theorem steps_inst:
  steps (State t0,n) (State t1,m) ⇒ t1.instructions = t0.instructions
Proof
  rw [] \\ imp_res_tac steps_consts \\ fs []
QED

Theorem steps_trans:
  ∀x y z. steps x y ∧ steps y z ⇒ steps x z
Proof
  fs [FORALL_PROD] \\ metis_tac [steps_rules]
QED

Theorem steps_refl[simp]:
  ∀x. steps x x
Proof
  once_rewrite_tac [steps_cases] \\ fs [FORALL_PROD]
QED

Theorem IMP_steps_state:
  (∃mid. steps (start,n) mid ∧ ∃s. steps mid (State s,n) ∧ P s) ⇒
  ∃s. steps (start,n) (State s,n) ∧ P s
Proof
  rw [] \\ metis_tac [steps_trans]
QED

Theorem IMP_steps_alt:
  (∃y. steps x y ∧ ∃t1. steps y (State t1,n) ∧ P t1) ⇒
  ∃t1. steps x (State t1,n) ∧ P t1
Proof
  metis_tac [steps_trans]
QED

Theorem IMP_steps:
  (∃mid outcome. steps start mid ∧ steps mid outcome ∧ P outcome) ⇒
  ∃outcome. steps start outcome ∧ P outcome
Proof
  rw [] \\ qexists_tac ‘outcome’ \\ fs []
  \\ PairCases_on ‘start’ \\ PairCases_on ‘mid’ \\ PairCases_on ‘outcome’
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem IMP_step:
  (∃mid outcome. step (FST start) (mid) ∧ steps (mid,SND start) outcome ∧ P outcome) ⇒
  ∃outcome. steps start outcome ∧ P outcome
Proof
  rw [] \\ qexists_tac ‘outcome’ \\ fs []
  \\ PairCases_on ‘start’ \\ PairCases_on ‘outcome’
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 2) \\ fs []
QED

Theorem IMP_step':
  (∃mid outcome. step s mid ∧ steps (mid,n) outcome ∧ P outcome) ⇒
  ∃outcome. steps (s,SUC n) outcome ∧ P outcome
Proof
  rw [] \\ qexists_tac ‘outcome’ \\ fs []
  \\ PairCases_on ‘outcome’
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> last)
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [ADD1]
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 3) \\ fs []
QED

Theorem IMP_start:
  P start ⇒
  ∃outcome. steps start outcome ∧ P outcome
Proof
  rw [] \\ qexists_tac ‘start’ \\ fs [] \\ PairCases_on ‘start’
  \\ match_mp_tac (steps_rules |> CONJUNCTS |> el 1 |> DISCH T) \\ fs []
QED

Theorem steps_imp_RTC_step:
  ∀s t. steps s t ⇒ step⃰ (FST s) (FST t)
Proof
  ho_match_mp_tac steps_ind \\ fs []
  \\ metis_tac [RTC_TRANSITIVE,transitive_def]
QED

Theorem step_determ:
  step x y ∧ step x z ==> y = z
Proof
  once_rewrite_tac [step_cases] \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ ntac 2 (fs [take_branch_cases] \\ fs [] \\ rw [] \\ fs [])
  \\ rfs [APPEND_11_LENGTH]
QED

Theorem not_step_Halt[simp]:
  ~step (Halt e1 o1) u
Proof
  once_rewrite_tac [step_cases] \\ fs []
QED

Theorem RTC_step_determ:
  ∀x e1 o1 e2 o2.
    step⃰ x (Halt e1 o1) ∧ step⃰ x (Halt e2 o2) ⇒ e2 = e1 ∧ o2 = o1
Proof
  qsuff_tac ‘∀x y. step⃰ x y ⇒
    ∀e1 o1 e2 o2.
       y = (Halt e1 o1) ∧ step⃰ x (Halt e2 o2) ⇒ e2 = e1 ∧ o2 = o1’
  THEN1 metis_tac []
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rpt strip_tac \\ rpt var_eq_tac \\ fs []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [RTC_CASES1] \\ fs []
  \\ rw [] \\ fs [] \\ imp_res_tac step_determ \\ rw [] \\ res_tac
QED

Theorem steps_IMP_NRC_step:
  ∀s k res r. steps (s,k) (res,r) ⇒ ∃k. NRC step k s res
Proof
  ho_match_mp_tac (steps_ind |> SIMP_RULE std_ss [FORALL_PROD]
    |> Q.SPEC ‘λ(x,y) (t,r). P x y t r’ |> SIMP_RULE std_ss [] |> GEN_ALL) \\ rw []
  THEN1 (qexists_tac ‘0’ \\ fs [])
  THEN1 (qexists_tac ‘SUC 0’ \\ fs [])
  THEN1 (qexists_tac ‘SUC 0’ \\ fs [])
  \\ metis_tac [NRC_ADD_I]
QED

Theorem NRC_step_determ:
  ∀k s res1 res2. NRC step k s res1 ∧ NRC step k s res2 ⇒ res1 = res2
Proof
  Induct \\ fs [NRC] \\ rw []
  \\ imp_res_tac step_determ \\ rw [] \\ res_tac
QED

Triviality steps_NRC:
  ∀x y. steps x y ⇒ ∃k. NRC step ((SND x - SND y) + k) (FST x) (FST y) ∧ SND y ≤ SND x
Proof
  ho_match_mp_tac steps_ind \\ rw [] \\ fs []
  THEN1 (qexists_tac ‘0’ \\ fs [])
  THEN1 (qexists_tac ‘SUC 0’ \\ fs [])
  THEN1 (qexists_tac ‘0’ \\ fs [])
  \\ qexists_tac ‘k+k'’
  \\ ‘k + k' + n1 − n3 = (k + n1 − n2) + (k' + n2 − n3)’ by fs []
  \\ metis_tac [NRC_ADD_I]
QED

Theorem step_mono:
  step (State t1) (State t2) ⇒ t1.output ≼ t2.output
Proof
  rw [step_cases] \\ fs [write_reg_def,inc_def,set_pc_def,set_stack_def,write_mem_def,
    AllCaseEqs(),unset_reg_def,put_char_def] \\ rw [] \\ fs []
QED

Theorem NRC_step_mono:
  ∀n t1 t2. NRC step n (State t1) (State t2) ⇒ t1.output ≼ t2.output
Proof
  Induct \\ fs [NRC_SUC_RECURSE_LEFT] \\ rw []
  \\ Cases_on ‘z’ \\ fs [] \\ res_tac
  \\ imp_res_tac step_mono
  \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS
QED

Theorem asm_output_PREFIX:
  NRC step k (State t) (State t1) ∧
  steps (State t,k) (State t2,0) ⇒
  t1.output ≼ t2.output
Proof
  rw [] \\ drule steps_NRC \\ fs [] \\ rw []
  \\ imp_res_tac NRC_ADD_E
  \\ imp_res_tac NRC_step_determ \\ rw []
  \\ imp_res_tac NRC_step_mono
QED

Theorem lprefix_chain_step:
  lprefix_chain {fromList t'.output | step⃰ (State t) (State t')}
Proof
  fs [lprefix_lubTheory.lprefix_chain_def] \\ rw []
  \\ fs [llistTheory.LPREFIX_fromList,llistTheory.from_toList]
  \\ imp_res_tac RTC_NRC
  \\ ‘n ≤ n' ∨ n' ≤ n’ by fs []
  \\ fs [LESS_EQ_EXISTS] \\ rw []
  \\ metis_tac [NRC_ADD_E,NRC_step_determ,NRC_step_mono,
                rich_listTheory.IS_PREFIX_TRANS]
QED

val _ = export_theory();
