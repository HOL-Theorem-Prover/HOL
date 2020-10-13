open preamble while_langTheory while_lang_lemmasTheory std_logicTheory;

val _ = new_theory "std_logic_soundness";

Theorem Hoare_soundness:
  ∀P c Q. Hoare P c Q ⇒ HoareSem P c Q
Proof
  ho_match_mp_tac Hoare_ind \\ rw [HoareSem_def]
  \\ fs [terminates_Skip,terminates_Assign,terminates_Print]
  THEN1 (fs [terminates_Seq] \\ metis_tac [])
  THEN1 (fs [terminates_If] \\ metis_tac [])
  THENL [all_tac,  metis_tac []]
  \\ pop_assum mp_tac \\ qid_spec_tac ‘s’
  \\ qspec_then ‘R’ mp_tac WF_INDUCTION_THM \\ asm_rewrite_tac []
  \\ disch_then ho_match_mp_tac
  \\ rw [] \\ fs [PULL_FORALL]
  \\ once_rewrite_tac [terminates_While]
  \\ fs [terminates_Seq,terminates_If]
  \\ reverse (rw [])
  THEN1 (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [terminates_Skip])
  \\ fs [terminates_Seq]
  \\ first_assum drule
  \\ disch_then drule \\ strip_tac
  \\ fs [PULL_EXISTS]
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac)
  \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs []
QED

val _ = export_theory();
