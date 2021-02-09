open preamble while_langTheory while_lang_lemmasTheory div_logicTheory
     std_logicTheory std_logic_completenessTheory;

val _ = new_theory "div_logic_completeness";

Theorem Pohjola_strengthen:
  ∀P P' p D. (∀s. P s ⇒ P' s) ∧ Pohjola P' p D ⇒ Pohjola P p D
Proof
  rw [] \\ match_mp_tac (last (CONJUNCTS Pohjola_rules))
  \\ qexists_tac ‘P'’ \\ fs [] \\ metis_tac []
QED

Theorem Pohjola_case_split = Pohjola_rules |> CONJUNCTS |> el 7;

Inductive div_at_iteration:
  (∀f s c l D.
     guard f s ∧
     diverges s c l ∧ D l ⇒
     div_at_iteration 0 s f c D)
  ∧
  (∀f s c t D.
     guard f s ∧
     terminates s c t ∧
     div_at_iteration n t f c D ⇒
     div_at_iteration (SUC n) s f c D)
End

Theorem div_at_iteration_11:
  ∀i j s f c D.
    div_at_iteration i s f c D ∧
    div_at_iteration j s f c D ⇒ i = j
Proof
  Induct \\ Cases_on ‘j’
  \\ once_rewrite_tac [div_at_iteration_cases] \\ rw []
  \\ fs [diverges_cases]
  \\ metis_tac [terminates_deterministic]
QED

Theorem choice_div_at_iteration:
  (∃i. div_at_iteration i s f c D ∧ g (@i. div_at_iteration i s f c D) n) ⇔
  (∃i. div_at_iteration i s f c D ∧ g i n)
Proof
  eq_tac \\ rw []
  \\ qsuff_tac ‘∀j. div_at_iteration j s f c D ⇔ i = j’
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ imp_res_tac div_at_iteration_11 \\ fs []
QED

Theorem While_lemma:
  (∀i. ¬div_at_iteration i s f c D) ∧
  diverges s (While f c) l ∧ D l ⇒
  ∃ts. ts 0 = s ∧ ∀i. guard f (ts i) ∧ terminates (ts i) c (ts (i+1)) ∧
                      ∃k. NRC step (i + k) (While f c,ts 0) (While f c,ts i)
Proof
  rw []
  \\ qabbrev_tac ‘ts = λi. @t. NRC (λx y. terminates x c y) i s t’
  \\ qexists_tac ‘ts’ \\ fs []
  \\ conj_tac THEN1 (unabbrev_all_tac \\ fs [])
  \\ qsuff_tac ‘∀i. ∃t. NRC (λx y. terminates x c y) i s t ∧ guard f t ∧
                        ∃k. NRC step (i + k) (While f c,s) (While f c,t)’
  THEN1
   (strip_tac \\ gen_tac
    \\ unabbrev_all_tac
    \\ first_assum (qspec_then ‘i’ strip_assume_tac)
    \\ drule NRC_terminates
    \\ first_x_assum (qspec_then ‘i+1’ strip_assume_tac)
    \\ drule NRC_terminates
    \\ fs [] \\ rw []
    \\ rfs [GSYM ADD1,NRC_SUC_RECURSE_LEFT] \\ fs []
    \\ metis_tac [])
  \\ gen_tac \\ ntac 3 (last_x_assum mp_tac)
  \\ qid_spec_tac ‘s’ \\ qid_spec_tac ‘i’ \\ Induct \\ fs [NRC]
  THEN1 (simp [diverges_While] \\ fs [diverges_Seq,diverges_If] \\ rw [] \\ fs []
         \\ qexists_tac ‘0’ \\ fs [])
  \\ rw []
  \\ qpat_x_assum ‘diverges _ _ _’ mp_tac
  \\ simp [diverges_While]
  \\ fs [diverges_Seq,diverges_If]
  \\ rw [] \\ fs []
  \\ first_assum (qspec_then ‘0’ mp_tac)
  \\ once_rewrite_tac [div_at_iteration_cases]
  \\ fs [diverges_Seq] THEN1 metis_tac []
  \\ disch_then kall_tac \\ fs [PULL_EXISTS]
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
  \\ first_x_assum drule
  \\ impl_tac THEN1
   (fs [] \\ rw []
    \\ CCONTR_TAC
    \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ fs []
    \\ simp [Once div_at_iteration_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ rw []
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
  \\ fs [terminates_cases]
  \\ drule RTC_Seq
  \\ disch_then (qspec_then ‘While f c’ mp_tac)
  \\ simp [RTC_eq_NRC] \\ rw []
  \\ qexists_tac ‘SUC (SUC (n+k))’
  \\ fs [ADD_CLAUSES]
  \\ simp [Once NRC]
  \\ simp [Once step_cases]
  \\ simp [Once NRC]
  \\ simp [Once step_cases]
  \\ ‘SUC (i + (k + n)) = n + SUC (k + i)’ by fs []
  \\ asm_rewrite_tac []
  \\ match_mp_tac NRC_ADD_I
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
  \\ rw [Once NRC] \\ simp [Once step_cases]
QED

Theorem LUB_INSERT_LNIL:
  LUB (LNIL INSERT s) = LUB s
Proof
  fs [lprefix_lubTheory.build_lprefix_lub_def]
  \\ fs [lprefix_lubTheory.build_lprefix_lub_f_def]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ fs [lprefix_lubTheory.build_lprefix_lub_f_def]
  \\ rw [] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ fs [lprefix_lubTheory.lprefix_chain_nth_def]
  \\ AP_TERM_TAC \\ rw [FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ metis_tac []
QED

Theorem Pohjola_diverges:
  Pohjola (λs. ∃l. diverges s c l ∧ D l) c D
Proof
  qid_spec_tac ‘D’ \\ Induct_on ‘c’
  THEN1 fs [not_diverges,Pohjola_rules]
  THEN1 fs [not_diverges,Pohjola_rules]
  THEN1 fs [not_diverges,Pohjola_rules]
  THEN1 (* Seq *)
   (rw [] \\ match_mp_tac Pohjola_case_split \\ fs [PULL_EXISTS]
    \\ qexists_tac ‘λs. ∃l. diverges s c l’ \\ rw []
    \\ rpt (first_x_assum (qspec_then ‘D’ assume_tac))
    \\ once_rewrite_tac [Pohjola_cases] \\ rw []
    THEN1
     (disj1_tac \\ match_mp_tac Pohjola_strengthen \\ fs []
      \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
      \\ fs [diverges_Seq] \\ rw []
      \\ imp_res_tac diverges_deterministic \\ fs []
      \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
      \\ fs [diverges_cases])
    \\ disj2_tac \\ disj1_tac
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ match_mp_tac Hoare_strengthen \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘Hoare _ _ Q’
    \\ assume_tac Hoare_terminates
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ fs [diverges_Seq] \\ rw [] \\ fs [Abbr‘Q’]
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
  THEN1 (* If *)
   (rw [] \\ simp [Once Pohjola_cases] \\ disj1_tac
    \\ rpt (first_x_assum (qspec_then ‘D’ assume_tac))
    \\ fs [PULL_EXISTS,diverges_If] \\ rw []
    \\ match_mp_tac Pohjola_strengthen \\ fs []
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [] \\ rw [])
  (* While *)
  \\ rw [] \\ match_mp_tac Pohjola_case_split \\ fs [PULL_EXISTS]
  \\ qexists_tac ‘λs. ∃i. div_at_iteration i s f c D’ \\ rw []
  THEN1
   ((* While case: finite number of loop iterations and then loop body diverges *)
    match_mp_tac Pohjola_strengthen \\ fs []
    \\ qexists_tac ‘λs. ∃i. div_at_iteration i s f c D’ \\ rw []
    THEN1 metis_tac []
    \\ simp [Once Pohjola_cases] \\ disj2_tac \\ disj1_tac
    \\ qexists_tac ‘measure (λs. @i. div_at_iteration i s f c D)’ \\ simp []
    \\ qexists_tac ‘λs. ~(div_at_iteration 0 s f c D)’
    \\ fs [PULL_EXISTS] \\ fs [choice_div_at_iteration] \\ rw []
    THEN1 (Cases_on ‘i’ \\ fs [Once div_at_iteration_cases])
    THEN1
     (match_mp_tac Hoare_completeness
      \\ fs [HoareSem_def] \\ rw []
      \\ ‘∀j. div_at_iteration j s f c D ⇔ j = i’ by metis_tac [div_at_iteration_11]
      \\ simp [] \\ pop_assum kall_tac
      \\ Cases_on ‘i’ \\ fs []
      \\ pop_assum mp_tac
      \\ pop_assum mp_tac
      \\ simp [Once div_at_iteration_cases,ADD1] \\ rw []
      \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
      \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ rpt (first_x_assum (qspec_then ‘D’ assume_tac))
    \\ match_mp_tac Pohjola_strengthen \\ fs []
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [] \\ rw []
    \\ pop_assum mp_tac
    \\ simp [Once div_at_iteration_cases,ADD1] \\ rw []
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
  (* While case: infinite number of loop iterations: loop body always terminates *)
  \\ simp [Once Pohjola_cases] \\ disj1_tac \\ rw []
  \\ drule While_lemma
  \\ disch_then drule \\ fs [] \\ strip_tac \\ rw []
  \\ qexists_tac ‘λi s. FST s = FST (ts i)’
  \\ qexists_tac ‘λi. DROP (LENGTH (output_of (ts i))) (output_of (ts (i+1)))’
  \\ fs [] \\ reverse (rw [])
  THEN1 (match_mp_tac Hoare_completeness \\ simp [HoareSem_def]
         \\ Cases \\ fs [output_of_def] \\ rw []
         \\ qexists_tac ‘(FST (ts (i+1)),
                          DROP (LENGTH (output_of (ts i))) (output_of (ts (i + 1))))’
         \\ fs [output_of_def,guard_def]
         \\ first_assum (qspec_then ‘i’ strip_assume_tac)
         \\ first_x_assum (qspec_then ‘i+1’ strip_assume_tac)
         \\ Cases_on ‘ts i’ \\ fs [guard_def]
         \\ Cases_on ‘ts (i + 1)’ \\ fs [guard_def,output_of_def]
         \\ imp_res_tac terminates_ignores_history)
  \\ fs [ignores_output_def]
  \\ qmatch_abbrev_tac ‘_ l1’
  \\ qsuff_tac ‘l = l1’ THEN1 (rw [] \\ fs [])
  \\ fs [diverges_cases]
  \\ ‘∀i j. i ≤ j ⇒ output_of (ts i) ≼ output_of (ts j)’ by
   (fs [LESS_EQ_EXISTS,PULL_EXISTS] \\ Induct_on ‘p’ \\ fs []
    \\ rw [] \\ first_x_assum (qspec_then ‘i’ assume_tac)
    \\ first_x_assum (qspec_then ‘i+p’ strip_assume_tac)
    \\ fs [terminates_cases,RTC_eq_NRC]
    \\ imp_res_tac NRC_step_output_mono \\ fs [ADD1]
    \\ imp_res_tac IS_PREFIX_TRANS \\ fs [])
  \\ ‘lprefix_chain {fromList (output_of (ts i)) | i | T}’ by
   (fs [lprefix_lubTheory.lprefix_chain_def] \\ rw []
    \\ fs [lprefix_lubTheory.lprefix_rel_def,PULL_EXISTS,LPREFIX_fromList,from_toList]
    \\ ‘i ≤ i' ∨ i' ≤ i’ by fs [] \\ res_tac \\ fs [])
  \\ ‘l1 = LUB { fromList (output_of (ts i)) |i| T }’ by
    (unabbrev_all_tac
     \\ qabbrev_tac ‘diff = (λi.
                      DROP (LENGTH (output_of (ts i)))
                        (output_of (ts (i + 1))))’
     \\ match_mp_tac EQ_TRANS
     \\ qexists_tac ‘FLAT (fromSeq
           (λn. if n = 0 then output_of (ts 0) else diff (n-1)))’
     \\ conj_tac THEN1
      (once_rewrite_tac [EQ_SYM_EQ]
       \\ simp [Once fromSeq_LCONS]
       \\ fs [o_DEF] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
     \\ fs [div_logic_soundnessTheory.FLAT_EQ_LUB]
     \\ once_rewrite_tac [EQ_SYM_EQ]
     \\ match_mp_tac EQ_TRANS
     \\ qexists_tac ‘LUB (LNIL INSERT {fromList (output_of (ts i)) | i | T})’
     \\ conj_tac THEN1 fs [LUB_INSERT_LNIL]
     \\ AP_TERM_TAC
     \\ fs [EXTENSION,PULL_EXISTS]
     \\ qsuff_tac ‘∀i. output_of (ts i) = FLAT (GENLIST
                (λn. if n = 0 then output_of (ts 0) else diff (n − 1)) (SUC i))’
     THEN1
      (disch_then (fn th => simp [Once th])
       \\ rw [] \\ eq_tac \\ rw []
       THEN1 (qexists_tac ‘0’ \\ fs [])
       THEN1 metis_tac []
       \\ Cases_on ‘x'’ \\ fs [] \\ metis_tac [])
     \\ Induct \\ fs []
     \\ once_rewrite_tac [GENLIST]
     \\ rewrite_tac [SNOC_APPEND,FLAT_APPEND]
     \\ pop_assum (assume_tac o GSYM) \\ fs []
     \\ fs [Abbr‘diff’]
     \\ first_x_assum (qspecl_then [‘i’,‘i+1’] mp_tac) \\ fs [ADD1]
     \\ fs [IS_PREFIX_APPEND] \\ rw [] \\ fs [DROP_LENGTH_APPEND])
  \\ first_x_assum (qspec_then ‘n’ kall_tac)
  \\ fs []
  \\ match_mp_tac lprefix_lubTheory.IMP_build_lprefix_lub_EQ
  \\ fs [lprefix_lubTheory.lprefix_rel_def,PULL_EXISTS,LPREFIX_fromList,from_toList]
  \\ fs [lprefix_chain_RTC_step]
  \\ rw []
  THEN1
   (fs [RTC_eq_NRC]
    \\ qexists_tac ‘n’ \\ fs []
    \\ first_x_assum (qspec_then ‘n’ strip_assume_tac)
    \\ drule NRC_ADD_E \\ strip_tac
    \\ imp_res_tac NRC_step_deterministic
    \\ fs [] \\ rw []
    \\ imp_res_tac NRC_step_output_mono \\ fs [output_of_def])
  \\ first_x_assum (qspec_then ‘i’ strip_assume_tac)
  \\ imp_res_tac NRC_RTC \\ Cases_on ‘ts i’ \\ fs [output_of_def]
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
QED

Theorem Pohjola_completeness:
  ∀P c D. PohjolaSem P c D ⇒ Pohjola P c D
Proof
  fs [PohjolaSem_def] \\ rw []
  \\ match_mp_tac Pohjola_strengthen
  \\ qexists_tac ‘λs. ∃l. diverges s c l ∧ D l’
  \\ fs [Pohjola_diverges]
QED

val _ = export_theory();
