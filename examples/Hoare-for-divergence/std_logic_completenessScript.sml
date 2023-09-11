open preamble while_langTheory while_lang_lemmasTheory std_logicTheory;

val _ = new_theory "std_logic_completeness";

Theorem Hoare_strengthen:
  ∀P P' p Q. (∀s. P s ⇒ P' s) ∧ Hoare P' p Q ⇒ Hoare P p Q
Proof
  rw [] \\ match_mp_tac (last (CONJUNCTS Hoare_rules))
  \\ qexists_tac ‘P'’ \\ fs [] \\ metis_tac []
QED

Theorem Hoare_While:
  (∀s. P s ⇒ Inv s) ∧ (∀s. Inv s ∧ ¬guard x s ⇒ Q s) ∧
  (∀s0. Hoare (λs. Inv s ∧ guard x s ∧ s = s0) p (λs. Inv s ∧ m s < ((m s0):num))) ⇒
  Hoare P (While x p) Q
Proof
  rw []
  \\ match_mp_tac (last (CONJUNCTS Hoare_rules))
  \\ qexists_tac ‘Inv’ \\ fs []
  \\ qexists_tac ‘λs. Inv s ∧ ¬guard x s’ \\ fs []
  \\ once_rewrite_tac [Hoare_cases] \\ fs []
  \\ disj1_tac \\ qexists_tac ‘measure m’ \\ fs []
QED

Triviality NRC_lemma:
  ∀k0 k1 m t0 t1.
    NRC (λs t. guard f s ∧ terminates s c t) k0 m t0 ∧
    NRC (λs t. guard f s ∧ terminates s c t) k1 m t1 ∧
    ¬guard f t0 ∧ ¬guard f t1 ⇒
    t0 = t1 ∧ k0 = k1
Proof
  Induct \\ fs [NRC]
  THEN1 (Cases_on ‘k1’ \\ fs [] \\ rw [] \\ CCONTR_TAC \\ fs [] \\ fs [NRC])
  \\ fs [PULL_EXISTS]
  \\ Cases_on ‘k1’ \\ fs []
  THEN1 (rw [] \\ CCONTR_TAC \\ fs [] \\ fs [NRC])
  \\ fs [NRC,PULL_EXISTS] \\ rw []
  \\ imp_res_tac terminates_deterministic \\ fs []
  \\ rw [] \\ fs [] \\ res_tac
QED

Theorem Hoare_terminates:
  Hoare (λs. ∃t. terminates s c t ∧ Q t) c Q
Proof
  qid_spec_tac ‘Q’ \\ Induct_on ‘c’
  THEN1
   (fs [terminates_Skip]
    \\ once_rewrite_tac [Hoare_cases] \\ fs [FUN_EQ_THM])
  THEN1
   (rw [] \\ once_rewrite_tac [Hoare_cases] \\ fs [] \\ disj1_tac
    \\ fs [FUN_EQ_THM] \\ rw [] \\ fs [terminates_Assign])
  THEN1
   (rw [] \\ once_rewrite_tac [Hoare_cases] \\ fs [] \\ disj1_tac
    \\ fs [FUN_EQ_THM] \\ rw [] \\ fs [terminates_Print])
  THEN1
   (rw [] \\ once_rewrite_tac [Hoare_cases] \\ fs [] \\ disj1_tac
    \\ first_x_assum (qspec_then ‘Q’ assume_tac)
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ first_x_assum (qspec_then ‘(λs. ∃t. terminates s c' t ∧ Q t)’ assume_tac)
    \\ match_mp_tac Hoare_strengthen
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [terminates_Seq]
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
  THEN1
   (rw [] \\ once_rewrite_tac [Hoare_cases] \\ fs [] \\ disj1_tac \\ rw []
    \\ rpt (first_x_assum (qspec_then ‘Q’ assume_tac))
    \\ match_mp_tac Hoare_strengthen
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [] \\ fs [terminates_If] \\ rw [])
  \\ rw [] \\ match_mp_tac (GEN_ALL Hoare_While) \\ fs []
  (* witness for measure *)
  \\ qexists_tac ‘λs. @n. ∃t. NRC (λs t. guard f s ∧ terminates s c t) n s t ∧ ¬guard f t’
  \\ fs []
  \\ qexists_tac ‘λs. (∃t. terminates s (While f c) t ∧ Q t)’
  \\ fs [] \\ rw []
  THEN1 fs [terminates_While,terminates_If,terminates_Skip]
  \\ qmatch_abbrev_tac ‘_ QQ’
  \\ first_x_assum (qspec_then ‘QQ’ assume_tac)
  \\ match_mp_tac Hoare_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ unabbrev_all_tac \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ simp [Once terminates_While]
  \\ fs [terminates_If]
  \\ rw [] \\ fs [terminates_Seq]
  \\ fs [PULL_EXISTS]
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
  \\ ‘∃n. NRC (λs t. guard f s ∧ terminates s c t) n m t ∧ ¬guard f t’ by
        (match_mp_tac terminates_While_NRC \\ fs [])
  \\ ‘∀k t1. NRC (λs t. guard f s ∧ terminates s c t) k m t1 ∧ ¬guard f t1 ⇔
             t1 = t ∧ n = k’ by
   (rw [] \\ eq_tac \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac NRC_lemma \\ fs [])
  \\ ‘∀n t. NRC (λs t. guard f s ∧ terminates s c t) n s t ∧ ¬guard f t ⇔
         ∃k. NRC (λs t. guard f s ∧ terminates s c t) k m t ∧ ¬guard f t ∧ n = k + 1’ by
    (Cases \\ fs [] \\ fs [NRC] \\ fs [ADD1]
     \\ ‘∀t. terminates s c t ⇔ t = m’ by metis_tac [terminates_deterministic] \\ fs [])
  \\ fs [CONJ_ASSOC]
QED

Theorem Hoare_completeness:
  ∀P c Q. HoareSem P c Q ⇒ Hoare P c Q
Proof
  fs [HoareSem_def] \\ rw []
  \\ match_mp_tac Hoare_strengthen
  \\ qexists_tac ‘λs. ∃t. terminates s c t ∧ Q t’
  \\ fs [Hoare_terminates]
QED

val _ = export_theory();
