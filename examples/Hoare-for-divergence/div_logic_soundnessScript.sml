open preamble while_langTheory while_lang_lemmasTheory div_logicTheory
     std_logicTheory std_logic_soundnessTheory;

val _ = new_theory "div_logic_soundness";

Theorem lprefix_chain_IMAGE_GENLIST:
  lprefix_chain (IMAGE (fromList ∘ FLAT ∘ GENLIST f) univ(:nat))
Proof
  rw[IMAGE_COMPOSE] >>
  match_mp_tac lprefix_lubTheory.prefix_chain_lprefix_chain >>
  rw[lprefix_lubTheory.prefix_chain_def,IS_PREFIX_APPEND] >>
  rename1 ‘FLAT(GENLIST _ n) = FLAT(GENLIST _ m) ++ _’ >>
  Cases_on ‘n < m’ >-
   (imp_res_tac LESS_ADD >> rveq >> fs[] >>
    simp[GENLIST_APPEND |> ONCE_REWRITE_RULE[ADD_SYM]]) >>
  fs[NOT_LESS] >>
  imp_res_tac LESS_EQ_ADD_EXISTS >> rveq >>
  simp[GENLIST_APPEND]
QED

Theorem output_finite:
  (∀j. LENGTH (ts (j:num)) ≤ i) ∧
  (∀i j. i ≤ j ⇒ ts i ≼ ts j) ⇒
  ∃lim. ∀j. lim ≤ j ⇒ ts j = ts lim
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ last_x_assum mp_tac \\ rw []
  \\ simp [GSYM NOT_LESS]
  \\ Induct_on ‘i’ \\ fs []
  THEN1
   (reverse (Cases_on ‘LENGTH ((ts 0))’)
    THEN1 (qexists_tac ‘0’ \\ fs [])
    \\ first_x_assum (qspec_then ‘0’ mp_tac)
    \\ fs [] \\ rw [] \\ qexists_tac ‘j’ \\ fs []
    \\ Cases_on ‘ts j’ \\ fs [])
  \\ first_x_assum (qspec_then ‘j’ mp_tac) \\ rw [] \\ res_tac
  \\ fs [IS_PREFIX_APPEND]
  \\ Cases_on ‘l’ \\ fs []
  \\ qexists_tac ‘j'’ \\ fs []
QED

Theorem LUB_FLAT_GENLIST:
  ∀f. LFLATTEN (fromSeq (fromList o f)) =
      LUB (IMAGE (fromList o FLAT o GENLIST f) UNIV)
Proof
  rw [] \\ qmatch_abbrev_tac ‘ll = LUB lset’
  \\ qsuff_tac ‘lprefix_chain lset ∧ lprefix_lub lset ll’
  THEN1 metis_tac [lprefix_lubTheory.build_prefix_lub_intro]
  \\ conj_tac THEN1 fs [Abbr‘lset’,lprefix_chain_IMAGE_GENLIST]
  \\ fs [lprefix_lubTheory.lprefix_lub_def]
  \\ simp [LPREFIX_NTH]
  \\ qsuff_tac ‘∀i v. LNTH i ll = SOME v ⇔
                      ∃j. i < LENGTH (FLAT (GENLIST f j)) ∧
                          v = EL i (FLAT (GENLIST f j))’
  THEN1 (simp [Abbr‘lset’,PULL_EXISTS,LNTH_fromList,Abbr‘ll’]
         \\ metis_tac [])
  \\ ‘∀j. ll = FLAT (FLAT (GENLIST f j) ::: fromSeq (λn. f (n+j)))’ by
   (Induct THEN1 (simp [Abbr‘ll’,FLAT_def]
                  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ simp [Abbr‘ll’,FLAT_def]
    \\ fs [] \\ simp [Once fromSeq_LCONS]
    \\ fs [ADD1,o_DEF]
    \\ fs [FLAT_def,GSYM LAPPEND_ASSOC,LAPPEND_fromList]
    \\ fs [GSYM ADD1,GENLIST] \\ fs [SNOC_APPEND])
  \\ rw [] \\ reverse eq_tac \\ fs [PULL_EXISTS]
  THEN1
   (rw [] \\ first_x_assum (qspec_then ‘j’ mp_tac)
    \\ rw[] \\ fs [FLAT_def]
    \\ fs [LNTH_LAPPEND,LNTH_fromList])
  \\ rw [] \\ CCONTR_TAC \\ fs []
  \\ Cases_on ‘∃j. i < LENGTH (FLAT (GENLIST f j))’ \\ fs []
  THEN1
   (first_x_assum $ drule_at Concl \\ fs []
    \\ first_x_assum (qspec_then ‘j’ mp_tac)
    \\ rw[] \\ fs [FLAT_def]
    \\ fs [LNTH_LAPPEND,LNTH_fromList])
  \\ fs [NOT_LESS]
  \\ ‘∀j. LENGTH ((FLAT o GENLIST f) j) ≤ i’ by fs []
  \\ drule output_finite
  \\ impl_tac THEN1
   (simp [LESS_EQ_EXISTS,PULL_EXISTS]
    \\ once_rewrite_tac [ADD_COMM]
    \\ rewrite_tac [listTheory.GENLIST_APPEND,IS_PREFIX_APPEND3,FLAT_APPEND])
  \\ strip_tac
  \\ qpat_x_assum ‘∀j. l1 = _’ (qspec_then ‘lim’ mp_tac)
  \\ ‘∀x. FLAT (GENLIST f (lim + x)) = FLAT (GENLIST f lim)’ by fs []
  \\ fs [DROP_LENGTH_NIL]
  \\ fs [FLAT_def,o_DEF]
  \\ ‘∀n. f (lim + n) = []’ by
   (rw [] \\ first_assum (qspec_then ‘SUC n’ mp_tac)
    \\ rewrite_tac [ADD_CLAUSES,GENLIST,SNOC_APPEND,FLAT_APPEND] \\ fs [])
  \\ ‘LFLATTEN (fromSeq (λn. [||])) = LNIL:'a llist’ by fs [LFLATTEN_EQ_NIL]
  \\ fs [LAPPEND_NIL_2ND]
  \\ CCONTR_TAC \\ fs [LNTH_fromList]
  \\ rpt (first_x_assum (qspec_then ‘lim’ assume_tac)) \\ fs []
QED

Theorem FLAT_EQ_LUB:
  ∀f. FLAT (fromSeq f) = LUB (IMAGE (fromList o FLAT o GENLIST f) UNIV)
Proof
  fs [FLAT_def,LUB_FLAT_GENLIST]
QED

Theorem Pohjola_soundness:
  ∀P c Q. Pohjola P c Q ⇒ PohjolaSem P c Q
Proof
  ho_match_mp_tac Pohjola_ind \\ rw [PohjolaSem_def]
  THEN1 (fs [diverges_Seq] \\ metis_tac [])
  THEN1 (fs [diverges_Seq]
         \\ imp_res_tac Hoare_soundness
         \\ fs [HoareSem_def] \\ metis_tac [])
  THEN1 (fs [diverges_If] \\ metis_tac [])
  THEN1
   (first_x_assum drule \\ rw []
    \\ goal_assum (first_assum o mp_then (Pos last) mp_tac) \\ fs []
    \\ fs [diverges_cases]
    \\ ‘∀i. ∃t k. NRC (λs1 s2. terminates s1 p s2 ∧ guard x s2) i s t ∧
                  output_of t = output_of s ++ FLAT (GENLIST ev i) ∧ H i t’ by
      (Induct THEN1 fs []
       \\ fs [NRC_SUC_RECURSE_LEFT,GENLIST]
       \\ fs [PULL_EXISTS]
       \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
       \\ first_x_assum (qspec_then ‘i’ assume_tac)
       \\ imp_res_tac Hoare_soundness
       \\ fs [HoareSem_def]
       \\ first_x_assum (qspec_then ‘FST t,[]’ mp_tac)
       \\ impl_tac THEN1
        (Cases_on ‘t’ \\ fs [output_of_def,ignores_output_def] \\ metis_tac [])
       \\ strip_tac
       \\ drule terminates_history \\ fs []
       \\ disch_then (qspec_then ‘SND t’ assume_tac) \\ fs []
       \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
       \\ Cases_on ‘s'’ \\ Cases_on ‘t’ \\ fs [guard_def,output_of_def,ADD1]
       \\ fs [ignores_output_def] \\ metis_tac [])
    \\ last_x_assum (qspec_then ‘i’ kall_tac)
    \\ conj_tac
    THEN1
     (CCONTR_TAC \\ fs [] \\ fs [terminates_eq_exec]
      \\ qpat_x_assum ‘D (FLAT (output_of s:::fromSeq ev))’ kall_tac
      \\ qabbrev_tac ‘c = While x p’
      \\ last_x_assum kall_tac
      \\ last_x_assum mp_tac
      \\ last_x_assum kall_tac
      \\ last_x_assum kall_tac
      \\ last_x_assum mp_tac
      \\ pop_assum mp_tac
      \\ EVERY (map qid_spec_tac [‘H’,‘ev’])
      \\ pop_assum mp_tac
      \\ EVERY (map qid_spec_tac [‘t’,‘c’,‘s’])
      \\ fs [markerTheory.Abbrev_def]
      \\ ho_match_mp_tac exec_strongind
      \\ rw [] \\ fs []
      \\ last_x_assum assume_tac
      \\ last_x_assum assume_tac
      \\ last_x_assum kall_tac
      \\ first_assum (qspec_then ‘SUC 0’ strip_assume_tac)
      \\ fs [NRC]
      \\ fs [GSYM terminates_eq_exec]
      \\ imp_res_tac terminates_deterministic \\ rveq
      \\ qpat_x_assum ‘guard x _’ mp_tac \\ simp []
      \\ first_x_assum match_mp_tac
      \\ qexists_tac ‘ev o SUC’
      \\ qexists_tac ‘H o SUC’
      \\ rw [] \\ first_x_assum (qspec_then ‘SUC i’ mp_tac)
      \\ fs [NRC,PULL_EXISTS] \\ rw []
      \\ imp_res_tac terminates_deterministic \\ rveq
      \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
      \\ fs [GENLIST_CONS])
    \\ match_mp_tac EQ_TRANS
    \\ qexists_tac ‘FLAT (fromSeq (λn. if n = 0 then output_of s else ev (n-1)))’
    \\ conj_tac THEN1
     (once_rewrite_tac [EQ_SYM_EQ]
      \\ simp [Once fromSeq_LCONS]
      \\ fs [o_DEF] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ fs [FLAT_EQ_LUB]
    \\ match_mp_tac lprefix_lubTheory.IMP_build_lprefix_lub_EQ
    \\ fs [lprefix_chain_RTC_step,lprefix_chain_IMAGE_GENLIST]
    \\ fs [lprefix_lubTheory.lprefix_rel_def,PULL_EXISTS]
    \\ ‘∀i. ∃t. NRC (λs1 s2. terminates s1 p s2 ∧ guard x s2) i s t ∧
                output_of t = output_of s ⧺ FLAT (GENLIST ev i) ∧ H i t ∧
                ∃k. NRC step (i + k) (While x p,s) (While x p,t)’
      by(strip_tac >>
         first_x_assum(qspec_then ‘i’ strip_assume_tac) >>
         rpt(goal_assum drule) >>
         qhdtm_x_assum ‘NRC’ mp_tac >>
         qhdtm_x_assum ‘guard’ mp_tac >>
         rpt(pop_assum kall_tac) >>
         MAP_EVERY qid_spec_tac [‘s’] >>
         Induct_on ‘i’ >- (rw[] >> qexists_tac ‘0’ >> rw[]) >>
         rw[NRC] >>
         qhdtm_x_assum ‘terminates’ (strip_assume_tac o REWRITE_RULE[terminates_cases]) >>
         dxrule_then strip_assume_tac RTC_NRC >>
         res_tac >>
         Q.REFINE_EXISTS_TAC ‘SUC(k + _)’ >>
         simp[GSYM ADD_SUC,NRC] >>
         simp[Once step_cases] >>
         simp[Once step_cases] >>
         ConseqConv.CONSEQ_CONV_TAC(
          ConseqConv.DEPTH_CONSEQ_CONV(
            ConseqConv.ONCE_CONSEQ_REWRITE_CONV
              ([],[NRC_ADD_I],[]))) >>
         simp[Once CONJ_SYM] >> goal_assum drule >>
         qpat_x_assum ‘NRC step n _ _’ mp_tac >>
         rpt(pop_assum kall_tac) >>
         rename1 ‘Seq _ r’ >>
         qid_spec_tac ‘p’ >> qid_spec_tac ‘s’ >> Induct_on ‘n’ >-
           (rw[] >> qexists_tac ‘1’ >> simp[Once step_cases]) >>
         rw[NRC] >>
         Q.REFINE_EXISTS_TAC ‘SUC _’ >>
         rw[NRC] >>
         rename1 ‘step _ mid’ >> Cases_on ‘mid’ >>
         simp[Once step_cases] >>
         Cases_on ‘p = Skip’ >> rveq >-
           (simp[] >>
            qhdtm_x_assum ‘step’ (strip_assume_tac o ONCE_REWRITE_RULE[step_cases]) >>
            fs[] >> rveq >>
            imp_res_tac NRC_step >> rveq >>
            qexists_tac ‘0’ >> simp[]) >>
         simp[PULL_EXISTS] >>
         goal_assum drule >>
         res_tac >>
         goal_assum drule)
    \\ last_x_assum (qspec_then ‘ARB’ kall_tac)
    \\ conj_tac
    THEN1
     (Cases \\ fs [] THEN1 metis_tac [RTC_rules,PAIR]
      \\ fs [GENLIST_CONS,o_DEF]
      \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ fs []
      \\ fs [RTC_eq_NRC,PULL_EXISTS]
      \\ Cases_on ‘t’ \\ goal_assum drule
      \\ fs [output_of_def]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ fs [RTC_eq_NRC] \\ rw []
    \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ rw []
    \\ pop_assum mp_tac \\ once_rewrite_tac [ADD_COMM] \\ strip_tac
    \\ drule NRC_ADD_E \\ strip_tac
    \\ imp_res_tac NRC_step_deterministic \\ rveq \\ fs []
    \\ Cases_on ‘t'’ \\ fs [output_of_def] \\ rveq
    \\ qexists_tac ‘SUC n’ \\ fs [GENLIST_CONS,o_DEF]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
    \\ drule NRC_step_output_mono
    \\ fs [output_of_def,LPREFIX_fromList,from_toList])
  THEN1
   (pop_assum mp_tac \\ qid_spec_tac ‘s’
    \\ qspec_then ‘R’ mp_tac WF_INDUCTION_THM \\ asm_rewrite_tac []
    \\ disch_then ho_match_mp_tac \\ rw []
    \\ reverse (Cases_on ‘b s’) \\ fs []
    THEN1
     (res_tac
      \\ fs [diverges_While]
      \\ fs [diverges_If]
      \\ fs [diverges_Seq]
      \\ qexists_tac ‘l’ \\ fs [])
    \\ simp [diverges_While]
    \\ fs [diverges_If]
    \\ fs [diverges_Seq]
    \\ qpat_x_assum ‘∀s. Hoare _ _ _’ (qspec_then ‘s’ assume_tac)
    \\ drule Hoare_soundness \\ fs [HoareSem_def]
    \\ metis_tac [])
  \\ metis_tac []
QED

val _ = export_theory();
