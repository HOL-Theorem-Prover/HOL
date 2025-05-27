open preamble while_langTheory lprefix_lubTheory

val _ = new_theory "while_lang_lemmas";

Theorem step_exists: (* one can always take a step *)
  ∀s. ∃t. step s t
Proof
  strip_tac \\ PairCases_on ‘s’
  \\ EVERY (map qid_spec_tac [‘s2’,‘s1’,‘s0’])
  \\ Induct \\ once_rewrite_tac [step_cases] \\ fs []
  \\ rw [] \\ fs [EXISTS_PROD]
  \\ Cases_on ‘s0 = Skip’ \\ fs [] \\ metis_tac []
QED

Theorem terminates_or_diverges: (* every program either terminates or diverges *)
  ∀s p.
    (∃t. terminates s p t) ∨ (∃output. diverges s p output)
Proof
  metis_tac [diverges_cases]
QED

Theorem step_deterministic:
  ∀s t1 t2. step s t1 ∧ step s t2 ⇒ t1 = t2
Proof
  strip_tac \\ PairCases_on ‘s’
  \\ EVERY (map qid_spec_tac [‘s2’,‘s1’,‘s0’])
  \\ Induct \\ once_rewrite_tac [step_cases] \\ fs []
  \\ Cases_on ‘s0 = Skip’ \\ fs []
  \\ fs [PULL_EXISTS,FORALL_PROD]
  \\ metis_tac []
QED

Theorem NRC_step_deterministic:
  ∀n x y z. NRC step n x y ∧ NRC step n x z ⇒ y = z
Proof
  Induct \\ fs [NRC] \\ rw []
  \\ imp_res_tac step_deterministic \\ rw [] \\ res_tac
QED

Theorem terminates_deterministic:
  ∀s p t1 t2. terminates s p t1 ∧ terminates s p t2 ⇒ t1 = t2
Proof
  rw [terminates_cases]
  \\ imp_res_tac RTC_NRC
  \\ ‘n' ≤ n ∨ n ≤ n'’ by decide_tac
  \\ fs [LESS_EQ_EXISTS] \\ rw []
  \\ imp_res_tac NRC_ADD_E
  \\ imp_res_tac NRC_step_deterministic
  \\ rveq
  \\ ‘∀n t1 t2. NRC step n (Skip,t1) (Skip,t2) ⇒ t1 = t2’ by
     (Induct \\ fs [NRC] \\ rw [] \\ fs [Once step_cases] \\ rveq \\ fs [])
  \\ res_tac \\ rveq \\ fs []
QED

Theorem diverges_deterministic:
  ∀s p t1 t2. diverges s p t1 ∧ diverges s p t2 ⇒ t1 = t2
Proof
  rw [diverges_cases]
QED

Inductive exec:
  (∀s:state.
     exec s Skip s)
  ∧
  (∀s n x.
     exec s (Assign n x) (subst n x s))
  ∧
  (∀s x.
     exec s (Print x) (print x s))
  ∧
  (∀p q s0 s1 s2.
     exec s0 p s1 ∧ exec s1 q s2 ⇒
     exec s0 (Seq p q) s2)
  ∧
  (∀x p q s.
     exec s (if guard x s then p else q) s1 ⇒
     exec s (If x p q) s1)
  ∧
  (∀x p s.
     ~guard x s ⇒
     exec s (While x p) s)
  ∧
  (∀x p s s1 s2.
     guard x s ∧
     exec s p s1 ∧
     exec s1 (While x p) s2 ⇒
     exec s (While x p) s2)
End

Theorem NRC_step:
  ∀n s t. NRC step n (Skip,s) (Skip,t) ⇒ s = t
Proof
  Induct \\ fs [NRC] \\ simp [Once step_cases]
QED

Theorem terminates_Skip:
  terminates s Skip t
  ⇔
  s = t
Proof
  fs [terminates_cases]
  \\ eq_tac \\ rw []
  \\ imp_res_tac RTC_NRC
  \\ imp_res_tac NRC_step
QED

Theorem terminates_Assign:
  terminates s (Assign n x) t
  ⇔
  t = subst n x s
Proof
  fs [terminates_cases]
  \\ reverse eq_tac \\ rw []
  THEN1
   (match_mp_tac NRC_RTC \\ qexists_tac ‘SUC 0’
    \\ fs [NRC] \\ fs [Once step_cases])
  \\ imp_res_tac RTC_NRC
  \\ pop_assum mp_tac
  \\ Induct_on ‘n'’ \\ fs [NRC]
  \\ simp [Once step_cases] \\ rw []
  \\ imp_res_tac NRC_step
  \\ fs []
QED

Theorem terminates_Print:
  terminates s (Print x) t
  ⇔
  t = print x s
Proof
  fs [terminates_cases]
  \\ reverse eq_tac \\ rw []
  THEN1
   (match_mp_tac NRC_RTC \\ qexists_tac ‘SUC 0’
    \\ fs [NRC] \\ fs [Once step_cases])
  \\ imp_res_tac RTC_NRC
  \\ pop_assum mp_tac
  \\ Induct_on ‘n’ \\ fs [NRC]
  \\ simp [Once step_cases] \\ rw []
  \\ imp_res_tac NRC_step
  \\ fs []
QED

Theorem terminates_If:
  terminates s (If x p q) t
  ⇔
  terminates s (if guard x s then p else q) t
Proof
  fs [terminates_cases]
  \\ reverse eq_tac \\ rw []
  \\ TRY
     (once_rewrite_tac [RTC_CASES1] \\ fs []
      \\ goal_assum (first_x_assum o mp_then Any mp_tac)
      \\ fs [Once step_cases] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ simp [Once RTC_CASES1]
  \\ fs [Once step_cases]
QED

Theorem terminates_While:
  terminates s (While f c) t
  ⇔
  terminates s (If f (Seq c (While f c)) Skip) t
Proof
  fs [terminates_cases]
  \\ reverse eq_tac \\ rw []
  \\ TRY
     (once_rewrite_tac [RTC_CASES1] \\ fs []
      \\ goal_assum (first_x_assum o mp_then Any mp_tac)
      \\ fs [Once step_cases] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ simp [Once RTC_CASES1]
  \\ fs [Once step_cases]
QED

Definition real_step_def:
  real_step (p,s) (q,t) ⇔ p ≠ Skip ∧ step (p,s) (q,t)
End

Theorem terminates:
  terminates s p t ⇔
    RTC real_step (p,s) (Skip,t)
Proof
  eq_tac \\ qid_spec_tac ‘s’ \\ qid_spec_tac ‘p’ \\ qid_spec_tac ‘t’
  \\ fs [terminates_cases,RTC_eq_NRC,PULL_EXISTS]
  THEN1
   (Induct_on ‘n’ \\ fs [] \\ rw [NRC]
    THEN1 (qexists_tac ‘0’ \\ fs [])
    \\ Cases_on ‘p = Skip’ \\ Cases_on ‘z’ \\ rw []
    THEN1 (res_tac \\ fs [Once step_cases] \\ rw [])
    \\ res_tac
    \\ qexists_tac ‘SUC n'’ \\ fs [NRC]
    \\ simp [Once EXISTS_PROD,real_step_def]
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
  \\ Induct_on ‘n’ \\ fs [] \\ rw [NRC]
  THEN1 (qexists_tac ‘0’ \\ fs [])
  \\ Cases_on ‘z’ \\ fs [] \\ res_tac
  \\ qexists_tac ‘SUC n'’ \\ fs [NRC]
  \\ fs [real_step_def]
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem NRC_real_step_Skip:
  NRC real_step n (Skip,s) (Skip,t) ⇔ n = 0 ∧ s = t
Proof
  Cases_on ‘n’ \\ fs [NRC,real_step_def,FORALL_PROD]
QED

Theorem NRC_real_step_not_Skip:
  p ≠ Skip ⇒
  (NRC real_step n (p,s) (Skip,t) ⇔
   ∃k m. real_step (p,s) m ∧ NRC real_step k m (Skip,t) ∧ n = k + 1)
Proof
  Cases_on ‘n’ \\ fs [NRC,ADD1]
QED

Theorem real_steps_Seq:
  ∀n p q s t.
    NRC real_step n (Seq p q,s) (Skip,t) ⇔
    ∃n1 n2 m.
      NRC real_step n1 (p,s) (Skip,m) ∧
      NRC real_step n2 (q,m) (Skip,t) ∧ n = n1 + n2 + 1
Proof
  Induct \\ fs [NRC] \\ rw []
  \\ simp [Once real_step_def,EXISTS_PROD]
  \\ simp [Once step_cases]
  \\ Cases_on ‘p = Skip’ \\ fs []
  THEN1 (Cases_on ‘s’ \\ fs [NRC_real_step_Skip] \\ fs [ADD1])
  \\ fs [ADD1,PULL_EXISTS,NRC_real_step_not_Skip]
  \\ fs [EXISTS_PROD,DECIDE “n + 1 = k + (n2 + 2) ⇔ n = k + (n2 + 1):num”]
  \\ fs [real_step_def]
  \\ metis_tac []
QED

Theorem terminates_eq_exec:
  terminates s p t ⇔ exec s p t
Proof
  eq_tac
  THEN1
   (fs [terminates,RTC_eq_NRC,PULL_EXISTS]
    \\ strip_tac \\ qid_spec_tac ‘s’ \\ qid_spec_tac ‘t’ \\ qid_spec_tac ‘p’
    \\ completeInduct_on ‘n’ \\ strip_tac
    \\ Cases_on ‘p’ \\ fs []
    THEN1
     (once_rewrite_tac [exec_cases] \\ fs []
      \\ rw [] \\ imp_res_tac NRC_real_step_Skip \\ fs [])
    THEN1
     (once_rewrite_tac [exec_cases] \\ fs []
      \\ Cases_on ‘n’ \\ fs [NRC,Once EXISTS_PROD,real_step_def]
      \\ simp [Once step_cases]
      \\ rw [] \\ imp_res_tac NRC_real_step_Skip \\ fs [])
    THEN1
     (once_rewrite_tac [exec_cases] \\ fs []
      \\ Cases_on ‘n’ \\ fs [NRC,Once EXISTS_PROD,real_step_def]
      \\ simp [Once step_cases]
      \\ rw [] \\ imp_res_tac NRC_real_step_Skip \\ fs [])
    THEN1
     (fs [real_steps_Seq] \\ once_rewrite_tac [exec_cases]
      \\ fs [] \\ rw []
      \\ first_assum (qspec_then ‘n1’ mp_tac)
      \\ first_assum (qspec_then ‘n2’ mp_tac)
      \\ fs [] \\ rw [] \\ ntac 2 res_tac
      \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
    THEN1
     (Cases_on ‘n’ \\ fs [NRC]
      \\ fs [EXISTS_PROD]
      \\ fs [real_step_def,Once step_cases,FORALL_PROD]
      \\ once_rewrite_tac [exec_cases] \\ fs []
      \\ rw [] \\ first_assum (qspec_then ‘n'’ mp_tac) \\ fs [])
    \\ Cases_on ‘n’ \\ fs [NRC] \\ fs [EXISTS_PROD]
    \\ fs [real_step_def,Once step_cases,FORALL_PROD]
    \\ Cases_on ‘n'’ \\ fs [NRC] \\ fs [EXISTS_PROD]
    \\ fs [real_step_def,Once step_cases,FORALL_PROD]
    \\ once_rewrite_tac [exec_cases] \\ fs []
    \\ reverse (rw [])
    THEN1 (Cases_on ‘n’ \\ fs [NRC] \\ PairCases_on ‘z’ \\  fs [real_step_def])
    THEN1 (Cases_on ‘n’ \\ fs [NRC] \\ PairCases_on ‘z’ \\  fs [real_step_def])
    \\ fs [real_steps_Seq] \\ rw []
    \\ first_assum (qspec_then ‘n1’ mp_tac)
    \\ first_x_assum (qspec_then ‘n2’ mp_tac)
    \\ PairCases_on ‘m’
    \\ fs [] \\ rw [] \\ ntac 2 res_tac
    \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [])
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘p’
  \\ qid_spec_tac ‘s’
  \\ ho_match_mp_tac exec_ind \\ rw []
  \\ fs [terminates_If,terminates_Skip,terminates_Assign,terminates_Print]
  THEN1
   (fs [terminates,RTC_eq_NRC,real_steps_Seq]
    \\ rpt (goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []))
  \\ fs [terminates_If,terminates_Skip,terminates_While]
  \\ fs [terminates,RTC_eq_NRC,real_steps_Seq]
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
  \\ qexists_tac ‘SUC (SUC n')’
  \\ fs [NRC] \\ simp [Once EXISTS_PROD, real_step_def, Once step_cases]
  \\ fs [NRC] \\ simp [Once EXISTS_PROD, real_step_def, Once step_cases]
QED

Theorem terminates_Seq:
  terminates s (Seq p q) t
  ⇔
  ∃m. terminates s p m ∧ terminates m q t
Proof
  fs [terminates_eq_exec]
  \\ simp [Once exec_cases]
QED

Theorem terminates_While_NRC:
  ∀m f c t. terminates m (While f c) t ⇒
            ∃n. NRC (λs t. guard f s ∧ terminates s c t) n m t ∧ ¬guard f t
Proof
  rewrite_tac [terminates_eq_exec]
  \\ Induct_on ‘exec’ \\ rw []
  THEN1 (qexists_tac ‘0’ \\ fs [])
  \\ qexists_tac ‘SUC n’ \\ fs [NRC]
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs []
QED

Theorem not_diverges[simp]:
  ~diverges s Skip l ∧
  ~diverges s (Assign n x) l ∧
  ~diverges s (Print x) l
Proof
  fs [diverges_cases,terminates_Skip,terminates_Assign,terminates_Print]
QED

Theorem RTC_Seq:
  ∀s t c p c1.
    RTC step (c,s) (c1,t) ⇒
    RTC step (Seq c p,s) (Seq c1 p,t)
Proof
  simp [Once RTC_eq_NRC,PULL_EXISTS]
  \\ Induct_on ‘n’ \\ fs [NRC] \\ rw []
  \\ Cases_on ‘z’ \\ fs []
  \\ first_x_assum drule \\ strip_tac
  \\ Cases_on ‘c = Skip’
  THEN1 (fs [Once step_cases] \\ rw [])
  \\ once_rewrite_tac [RTC_CASES1]
  \\ disj2_tac
  \\ simp [Once step_cases,PULL_EXISTS]
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
QED

Theorem step_output_mono:
  ∀s t. step s t ⇒ output_of (SND s) ≼ output_of (SND t)
Proof
  ho_match_mp_tac step_ind
  \\ fs [subst_def,FORALL_PROD,output_of_def,print_def]
QED

Theorem NRC_step_output_mono:
  ∀k c s c' s'. NRC step k (c,s) (c',s') ⇒ output_of s ≼ output_of s'
Proof
  Induct \\ fs [NRC] \\ rw [] \\ Cases_on ‘z’ \\ fs []
  \\ imp_res_tac step_output_mono \\ fs []
  \\ res_tac \\ imp_res_tac IS_PREFIX_TRANS \\ fs []
QED

Theorem lprefix_chain_RTC_step:
  lprefix_chain {fromList out | (∃q t. RTC step x (q,t,out))}
Proof
  fs [lprefix_lubTheory.lprefix_chain_def] \\ rw []
  \\ fs [lprefix_lubTheory.lprefix_rel_def,PULL_EXISTS,LPREFIX_fromList,
         from_toList]
  \\ fs [RTC_eq_NRC]
  \\ rename [‘s1 ≼ s2 ∨ s2 ≼ s1’, ‘NRC _ a _ (_,_,s1)’, ‘NRC _ b _ (_, _, s2)’]
  \\ ‘a ≤ b ∨ b ≤ a’ by fs []
  \\ fs [LESS_EQ_EXISTS] \\ rw []
  \\ drule NRC_ADD_E \\ strip_tac
  \\ imp_res_tac NRC_step_deterministic
  \\ fs [] \\ rw []
  \\ imp_res_tac NRC_step_output_mono \\ fs [output_of_def]
QED

Theorem diverges_Seq:
  diverges s (Seq c c') l ⇔
  diverges s c l ∨ ∃t. terminates s c t ∧ diverges t c' l
Proof
  fs [diverges_cases,terminates_Seq]
  \\ Cases_on ‘∃t. terminates s c t’
  THEN1
   (fs []
    \\ ‘∀x. terminates s c x ⇔ x = t’ by metis_tac [terminates_deterministic]
    \\ simp [] \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ match_mp_tac lprefix_lubTheory.IMP_build_lprefix_lub_EQ
    \\ simp [lprefix_chain_RTC_step]
    \\ simp [lprefix_lubTheory.lprefix_rel_def,PULL_EXISTS,LPREFIX_fromList,from_toList]
    \\ pop_assum kall_tac \\ rw []
    THEN1
     (fs [RTC_eq_NRC,PULL_EXISTS]
      \\ fs [terminates_cases]
      \\ drule RTC_Seq
      \\ disch_then (qspec_then ‘c'’ mp_tac)
      \\ simp [RTC_eq_NRC] \\ rw []
      \\ rename [‘NRC step b _ (Seq Skip _, _)’, ‘out ≼ _’,
                 ‘NRC step a _ (_, _, out)’]
      \\ Cases_on ‘a ≤ b’ \\ fs []
      THEN1
       (fs [LESS_EQ_EXISTS] \\ rw []
        \\ drule NRC_ADD_E \\ strip_tac
        \\ imp_res_tac NRC_step_deterministic
        \\ fs [] \\ rw []
        \\ imp_res_tac NRC_step_output_mono \\ fs [output_of_def]
        \\ Cases_on ‘t’ \\ fs [output_of_def]
        \\ ‘NRC step 0 (c',q',r) (c',q',r)’ by fs []
        \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs [])
      \\ qpat_x_assum ‘NRC step a _ _’ assume_tac
      \\ rename [‘_ _ _ (x1,x2,x3)’]
      \\ qexists_tac ‘x3’
      \\ qexists_tac ‘x1’
      \\ qexists_tac ‘x2’ \\ fs []
      \\ qexists_tac ‘a - b - 1’
      \\ ‘a = b + SUC (a − b - 1)’ by decide_tac
      \\ ‘NRC step (b + SUC (a − b − 1)) (Seq c c',s) (x1,x2,x3)’ by metis_tac []
      \\ drule NRC_ADD_E \\ strip_tac
      \\ imp_res_tac NRC_step_deterministic \\ rw []
      \\ pop_assum mp_tac \\ fs [NRC]
      \\ simp [Once step_cases])
    \\ rename [‘_ (x1,x2,x3)’]
    \\ qexists_tac ‘x3’
    \\ qexists_tac ‘x1’
    \\ qexists_tac ‘x2’ \\ fs []
    \\ once_rewrite_tac [RTC_CASES_RTC_TWICE]
    \\ goal_assum (first_assum o mp_then (Pos last) mp_tac) \\ fs []
    \\ simp [Once RTC_CASES2] \\ disj2_tac
    \\ qexists_tac ‘(Seq Skip c',t)’
    \\ once_rewrite_tac [step_cases] \\ fs []
    \\ match_mp_tac RTC_Seq
    \\ fs [terminates_cases])
  \\ fs [] \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM]
  \\ fs [terminates_cases]
  \\ gen_tac \\ reverse eq_tac \\ fs [PULL_EXISTS] \\ rw []
  THEN1 (drule RTC_Seq \\ metis_tac [])
  \\ rpt (last_x_assum mp_tac)
  \\ qid_spec_tac ‘c’
  \\ qid_spec_tac ‘c'’
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘q’
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘out’
  \\ fs [RTC_eq_NRC] \\ fs [PULL_EXISTS,PULL_FORALL]
  \\ Induct_on ‘n’
  \\ fs [NRC] \\ rw []
  THEN1 (qexists_tac ‘c’ \\ qexists_tac ‘t’ \\ qexists_tac ‘0’ \\ fs [])
  \\ fs [NRC] \\ rw []
  \\ PairCases_on ‘z’
  \\ Cases_on ‘c = Skip’
  THEN1 (first_x_assum (qspecl_then [‘s’,‘0’] mp_tac) \\ fs [])
  \\ qpat_x_assum ‘step _ _’ mp_tac
  \\ once_rewrite_tac [step_cases] \\ fs [] \\ rw []
  \\ first_x_assum drule
  \\ impl_tac THEN1
   (rw [] \\ first_x_assum (qspecl_then [‘t'’,‘SUC n'’] mp_tac)
    \\ fs [NRC,GSYM IMP_DISJ_THM])
  \\ rw []
  \\ qexists_tac ‘q'’
  \\ qexists_tac ‘t'’
  \\ qexists_tac ‘SUC n'’
  \\ fs [NRC]
  \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
QED

Theorem diverges_If:
  diverges s (If f p q) l = diverges s (if guard f s then p else q) l
Proof
  fs [diverges_cases,terminates_If]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [fromList_11]
  THEN1
   (pop_assum mp_tac \\ simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
  THEN1
   (simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
  THEN1
   (pop_assum mp_tac \\ simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
  THEN1
   (simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
QED

Theorem diverges_While:
  diverges s (While g c) l ⇔
  diverges s (If g (Seq c (While g c)) Skip) l
Proof
  fs [diverges_cases,terminates_While]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [fromList_11]
  THEN1
   (pop_assum mp_tac \\ simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
  THEN1
   (simp [Once RTC_CASES1] \\ rw []
    \\ fs [Once step_cases] \\ rfs [] \\ metis_tac [RTC_REFL])
QED

Theorem NRC_terminates:
  ∀i s t.
    NRC (λx y. terminates x c y) i s t ⇒
    ∀t1. NRC (λx y. terminates x c y) i s t1 ⇔ (t = t1)
Proof
  Induct \\ fs [NRC] \\ rw [] \\ rename [‘terminates s c y’]
  \\ ‘∀x. terminates s c x ⇔ x = y’ by metis_tac [terminates_deterministic]
  \\ fs []
QED

Theorem terminates_history:
  ∀s c t.
    terminates s c t ⇒
      ∃new. SND t = SND s ++ new ∧
            ∀xs. terminates (FST s,xs) c (FST t,xs ++ new)
Proof
  fs [terminates_eq_exec]
  \\ ho_match_mp_tac exec_ind \\ fs []
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rpt (disch_then assume_tac)
  \\ once_rewrite_tac [exec_cases] \\ fs [] \\ rpt gen_tac \\ simp [PULL_EXISTS]
  \\ TRY (Cases_on ‘s’ \\ fs [subst_def,print_def,guard_def] \\ NO_TAC)
  \\ Cases_on ‘s’ \\ Cases_on ‘s'’ \\ Cases_on ‘t’ \\ fs [] \\ rw []
  \\ fs [guard_def] \\ metis_tac [APPEND_ASSOC]
QED

Theorem terminates_ignores_history:
  terminates (s,out1) c (t,out2) ⇒
  terminates (s,[]) c (t,DROP (LENGTH out1) out2)
Proof
  rw [] \\ drule terminates_history
  \\ fs [] \\ rw []
  \\ fs [DROP_LENGTH_APPEND]
  \\ first_x_assum (qspec_then ‘[]’ mp_tac) \\ fs []
QED

Theorem exec_FST:
  exec s c s1 ⇒
  exec (FST s,[]) c s2 ⇒
    FST s2 = FST s1
Proof
  fs [GSYM terminates_eq_exec] \\ strip_tac
  \\ Cases_on ‘s’ \\ Cases_on ‘s1’
  \\ drule terminates_ignores_history \\ fs [] \\ rw []
  \\ imp_res_tac terminates_deterministic \\ rw []
QED

val _ = export_theory();
