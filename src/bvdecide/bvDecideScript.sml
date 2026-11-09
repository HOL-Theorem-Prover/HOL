(* The theorem the tactic instantiates: a DAG whose blasted CNF a
   certificate refutes, checked by cv_compute, holds everywhere. *)
Theory bvDecide
Ancestors
  cv_type lratCheck bvBlast
Libs
  cv_transLib

val cv_check_dag_thm = bvBlastTheory.cv_check_dag_thm;

Theorem check_dag_cv:
  from_list from_bvBlast_node dag = dagc ∧
  cv_check_dag (cv$Num (dimindex(:'a))) dagc (cv_canon_steps c) = cv$Num 1 ⇒
  ∀(env : num -> 'a word) benv. eval_dag env benv dag
Proof
  strip_tac >> irule blast_dag_sound >> qexists_tac ‘dec_steps c’ >>
  ‘b2c (check_dag (dimindex(:'a)) dag (dec_steps c)) = cv$Num 1’
    by (rewrite_tac[cv_check_dag_thm, cv_canon_steps_thm] >> gvs[]) >>
  Cases_on ‘check_dag (dimindex(:'a)) dag (dec_steps c)’ >>
  gvs[cvTheory.b2c_def, check_dag_def]
QED

(* WORD_SIMP_CONV turns ~x into -x + -1w, which would blast as two adders *)
Theorem word_not_alt:
  -x + -1w = ~x ∧ -1w + -x = ~x
Proof
  rewrite_tac[wordsTheory.WORD_NOT, wordsTheory.word_sub_def] >>
  metis_tac[wordsTheory.WORD_ADD_COMM]
QED

