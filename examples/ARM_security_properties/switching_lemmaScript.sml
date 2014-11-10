open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory;
open priv_constraints_cpsr_pcTheory priv_constraints_lrTheory priv_constraints_bisimTheory tacticsLib;
open user_lemma_basicsTheory;
(* user_lemma_primitive_operationsTheory;*)
open ARM_proverLib;

(****************************************************************)
(*                    SWITCHING LEMMA                           *)
(*                        Narges                                *)
(****************************************************************)

val _ =  new_theory("switching_lemma");

val let_ss = simpLib.mk_simpset [boolSimps.LET_ss];

val _ = set_trace "Goalstack.show_proved_subtheorems" 0;

val tautology_fun_def = Define `tautology_fun (g:word32)
					    (s1:arm_state) (s2:arm_state) =
			       (T)`;

val have_same_mem_accesses_def =
Define `have_same_mem_accesses (g:word32)
					    (s1:arm_state) (s2:arm_state) =
			       (s1.accesses = s2.accesses) /\
                               (s1.memory = s2.memory)`;

val assert_mode_no_access_violation_def =
Define `assert_mode_no_access_violation k s=
			(~ access_violation s) /\
			((s.psrs (0,CPSR)).M = k)
      `;

val assert_mode_access_violation_def =
Define `assert_mode_access_violation k s=
			(access_violation s) /\
			((s.psrs (0,CPSR)).M = k)
      `;


val take_svc_exception1_def =
Define `take_svc_exception1 =
(read_reg <|proc := 0|> 15w ||| exc_vector_base <|proc := 0|>
              ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
              ||| read_sctlr <|proc := 0|>) >>=
           (λ(pc,ExcVectorBase,cpsr,scr,sctlr).
              (condT (cpsr.M = 22w)
                 (write_scr <|proc := 0|> (scr with NS := F))
                 ||| write_cpsr <|proc := 0|> (cpsr with M := 19w)) >>=
              (λ(u1,u2).
                 (write_spsr <|proc := 0|> cpsr
                    ||| write_reg <|proc := 0|> 14w
                          (if cpsr.T then
                             pc + 0xFFFFFFFEw
                           else
                             pc + 0xFFFFFFFCw)
                    ||| read_cpsr <|proc := 0|> >>=
                        (λcpsr.
                           write_cpsr <|proc := 0|>
                             (cpsr with
                              <|IT := 0w; J := F; E := sctlr.EE; I := T;
                                T := sctlr.TE|>))
                    ||| branch_to <|proc := 0|>
                          (ExcVectorBase + 8w)) >>=
                 (λ(u1,u2,u3,u4). constT ())))`;

val trans_tautology_fun_thm =
    store_thm("trans_tautology_fun_thm",
	      ``trans_fun tautology_fun``,
	      RW_TAC let_ss [ trans_fun_def,tautology_fun_def]
		     THEN RW_TAC (srw_ss()) [] );

val refl_rel_tautology_fun_thm =
    store_thm("refl_rel_tautology_fun_thm",
	      ``refl_rel tautology_fun``,
	      RW_TAC (srw_ss()) [refl_rel_def, tautology_fun_def]
	     );

val reflex_tautology_fun_thm =
    store_thm("reflex_tautology_fun_thm",
	      ``!u. (reflexive_comp  tautology_fun (assert_mode u))``
	    ,
	    RW_TAC (srw_ss()) [reflexive_comp_def,tautology_fun_def,assert_mode_def]);


val trans_have_same_mem_accesses_thm =
    store_thm("trans_have_same_mem_accesses_thm",
	      ``trans_fun have_same_mem_accesses``,
	      RW_TAC let_ss [ trans_fun_def,have_same_mem_accesses_def]
		     THEN RW_TAC (srw_ss()) [] );

val reflex_have_same_mem_accesses_thm =
    store_thm("reflex_have_same_mem_accesses_thm",
	      ``!u. (reflexive_comp  have_same_mem_accesses (assert_mode u))``
	    ,
	    RW_TAC (srw_ss()) [reflexive_comp_def,have_same_mem_accesses_def,assert_mode_def]);

val preserve_relation_in_priv_mode_thm_tac =
    let
	val tac = UNDISCH_ALL_TAC
		  THEN FULL_SIMP_TAC (bool_ss) [ARM_MODE_def,ARM_READ_CPSR_def,
						assert_mode_def,
						have_same_mem_accesses_def]
		  THEN RW_TAC (srw_ss()) []
		  THEN RW_TAC (srw_ss()) []
		  THEN IMP_RES_TAC similar_states_have_same_av_thm1
   		  THEN IMP_RES_TAC similar_states_have_same_mode_thm

		  THEN IMP_RES_TAC untouched_states_implies_mmu_setup_thm
		  THEN IMP_RES_TAC trivially_untouched_av_lem2
		  THEN FULL_SIMP_TAC (srw_ss()) []
    in
	RW_TAC (bool_ss) [preserve_relation_mmu_def,tautology_fun_def,
			  preserve_priv_bisimilarity_def,
			  satisfy_priv_constraints_v3_def,
			  satisfy_priv_constraints_v2a_def,
			  satisfy_priv_constraints_v2_def]
	       THEN PAT_ASSUM ``∀g s1 s2.X`` (fn thm =>
						 ASSUME_SPECL_TAC
						     [``g:bool[32]``,``s1:arm_state``,
						      ``s2:arm_state``] thm)
	       THEN FULL_SIMP_TAC (bool_ss)
	       [assert_mode_no_access_violation_def]
	       THEN UNDISCH_ALL_TAC
	       THEN FULL_SIMP_TAC (bool_ss) []
	       THEN RW_TAC (srw_ss()) []
	       THEN RW_TAC (srw_ss()) []
	       THENL
	       [PAT_ASSUM ``∀g s1 s2 a  .X``
			  (fn thm =>
			      ASSUME_SPECL_TAC [``g:bool[32]``,``s1:arm_state``,
						``s1':arm_state``,``a:'a``] thm) THEN tac,
		PAT_ASSUM ``∀g s1 s2 a  .X``
			  (fn thm =>
			      ASSUME_SPECL_TAC [``g:bool[32]``,``s2:arm_state``,
						``s2':arm_state``,``a:'a``] thm)
			  THEN tac,
		PAT_ASSUM ``∀g s1 s2 a  .X``
			  (fn thm =>
			      THROW_AWAY_TAC (concl thm))
			  THEN FULL_SIMP_TAC (bool_ss) [ARM_MODE_def,ARM_READ_CPSR_def,
						   assert_mode_def,
						   have_same_mem_accesses_def]
			  THEN IMP_RES_TAC similar_states_have_same_av_thm1
			  THEN IMP_RES_TAC similar_states_have_same_mode_thm
			  THEN IMP_RES_TAC untouched_states_implies_mmu_setup_thm
			  THEN IMP_RES_TAC trivially_untouched_av_lem2
			  THEN IMP_RES_TAC similar_states_have_same_cpsr_thm
			  THEN IMP_RES_TAC similar_states_have_same_pc_thm
			  THEN RES_TAC
			  THEN METIS_TAC []]
    end

val preserve_relation_in_priv_mode_v3_thm =
    store_thm ("preserve_relation_in_priv_mode_v3_thm",
	       ``! f m n.
	      preserve_priv_bisimilarity f n ==>
	      (satisfy_priv_constraints_v3 f m n )==>
	      (preserve_relation_mmu
		   f
		   (assert_mode_no_access_violation m )
		   (assert_mode n) have_same_mem_accesses tautology_fun) ==>
	      preserve_relation_mmu
	      f
	      (assert_mode_no_access_violation m )
	      (assert_mode n) priv_mode_constraints_v3 priv_mode_similar``,
  preserve_relation_in_priv_mode_thm_tac
	      );

val preserve_relation_in_priv_mode_v2a_thm =
    store_thm ("preserve_relation_in_priv_mode_v2a_thm",
	       ``! f m n.
	      preserve_priv_bisimilarity f n ==>
	      (satisfy_priv_constraints_v2a f m n )==>
	      (preserve_relation_mmu
		   f
		   (assert_mode_no_access_violation m )
		   (assert_mode n) have_same_mem_accesses tautology_fun) ==>
	      preserve_relation_mmu
	      f
	      (assert_mode_no_access_violation m )
	      (assert_mode n) priv_mode_constraints_v2a priv_mode_similar``,
  preserve_relation_in_priv_mode_thm_tac
	      );

val preserve_relation_in_priv_mode_v2_thm =
    store_thm ("preserve_relation_in_priv_mode_v2_thm",
	       ``! f m n.
	      preserve_priv_bisimilarity f n ==>
	      (satisfy_priv_constraints_v2 f m n )==>
	      (preserve_relation_mmu
		   f
		   (assert_mode_no_access_violation m )
		   (assert_mode n) have_same_mem_accesses tautology_fun) ==>
	      preserve_relation_mmu
	      f
	      (assert_mode_no_access_violation m )
	      (assert_mode n) priv_mode_constraints_v2 priv_mode_similar``,
  preserve_relation_in_priv_mode_thm_tac
	      );

val access_violation_implies_no_mode_changing_thm =
    store_thm ("access_violation_implies_no_mode_changing_thm",
	       ``!f g . const_comp f ==>
	      (preserve_relation_mmu f (assert_mode 16w)
	      (assert_mode 16w) priv_mode_constraints_v3 priv_mode_similar
	      ==>
              (preserve_relation_mmu (f>>=g)  (assert_mode_access_violation 16w )
	      (assert_mode_access_violation 16w )
	      priv_mode_constraints_v3 priv_mode_similar))
	       /\
	      (
             preserve_relation_mmu f (assert_mode 16w)
	      (assert_mode 16w) priv_mode_constraints_v2a priv_mode_similar
	      ==>
	      (preserve_relation_mmu (f>>=g)  (assert_mode_access_violation 16w )
	      (assert_mode_access_violation 16w )
	      priv_mode_constraints_v2a priv_mode_similar))
``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_def,
				  seqT_def,
				  const_comp_def,
				  assert_mode_def,
				  assert_mode_access_violation_def,
				  ARM_MODE_def,
				  ARM_READ_CPSR_def]
		      THEN PAT_ASSUM ``! g s1 s2.X``
		      (fn thm => ASSUME_SPECL_TAC [``g':bool[32]``,
						   ``s1:arm_state``,
						   ``s2:arm_state``] thm)
		      THEN RES_TAC
		      THEN PAT_ASSUM ``! s s x.X``
		      (fn thm =>
			  ASSUME_SPECL_TAC [``s1:arm_state``,
					    ``s1':arm_state``,
					    ``a:'a``] thm
					   THEN ASSUME_SPECL_TAC [``s2:arm_state``,
								  ``s2':arm_state``,
								  ``a:'a``] thm)
		      THEN RES_TAC
		      THEN FULL_SIMP_TAC (srw_ss()) []);


val access_violation_implies_no_mode_changing_v1_thm =
    store_thm ("access_violation_implies_no_mode_changing_v1_thm",
	       ``!f g . const_comp f ==>
	      (preserve_relation_mmu f (assert_mode 16w)
	      (assert_mode 16w) priv_mode_constraints_v3 priv_mode_similar
	      ==>
              (preserve_relation_mmu (f>>=g)  (assert_mode_access_violation 16w )
	      (assert_mode_access_violation 16w )
	      priv_mode_constraints_v3 priv_mode_similar))
	       /\
	      (
             preserve_relation_mmu f (assert_mode 16w)
	      (assert_mode 16w) priv_mode_constraints_v2 priv_mode_similar
	      ==>
	      (preserve_relation_mmu (f>>=g)  (assert_mode_access_violation 16w )
	      (assert_mode_access_violation 16w )
	      priv_mode_constraints_v2 priv_mode_similar))
``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_def,
				  seqT_def,
				  const_comp_def,
				  assert_mode_def,
				  assert_mode_access_violation_def,
				  ARM_MODE_def,
				  ARM_READ_CPSR_def]
		      THEN PAT_ASSUM ``! g s1 s2.X``
		      (fn thm => ASSUME_SPECL_TAC [``g':bool[32]``,
						   ``s1:arm_state``,
						   ``s2:arm_state``] thm)
		      THEN RES_TAC
		      THEN PAT_ASSUM ``! s s x.X``
		      (fn thm =>
			  ASSUME_SPECL_TAC [``s1:arm_state``,
					    ``s1':arm_state``,
					    ``a:'a``] thm
					   THEN ASSUME_SPECL_TAC [``s2:arm_state``,
								  ``s2':arm_state``,
								  ``a:'a``] thm)
		      THEN RES_TAC
		      THEN FULL_SIMP_TAC (srw_ss()) []);


val user_pr_taut_imp_priv_pr_thm =
    store_thm ("user_pr_taut_imp_priv_pr_thm",
``!f. preserve_relation_mmu
	      (f)
	      (assert_mode 16w )
	      (assert_mode 16w )  tautology_fun tautology_fun
	      ==>
	      ((preserve_relation_mmu
	      (f)
	      (assert_mode 16w )
	      (assert_mode 16w )
	      priv_mode_constraints_v3 priv_mode_similar)
    /\
	 (preserve_relation_mmu
	      (f)
	      (assert_mode 16w )
	      (assert_mode 16w )
	      priv_mode_constraints_v2a priv_mode_similar)
    /\
	 (preserve_relation_mmu
	      (f)
	      (assert_mode 16w )
	      (assert_mode 16w )
	      priv_mode_constraints_v2 priv_mode_similar))``
,
 RW_TAC (srw_ss()) [preserve_relation_mmu_def,
		    assert_mode_def,
		    tautology_fun_def]
	THEN	PAT_ASSUM ``! g s1 s2.X``
	(fn thm => ASSUME_SPECL_TAC [``g:bool[32]``,
				     ``s1:arm_state``,
				     ``s2:arm_state``] thm)
	THEN RES_TAC
	THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v3_def,
				       priv_mode_constraints_v2a_def,
				       priv_mode_constraints_v2_def,
				       priv_mode_constraints_v1_def,
				       priv_mode_similar_def,
				       ARM_MODE_def,
				       ARM_READ_CPSR_def
				      ]
	THEN FULL_SIMP_TAC (let_ss) [untouched_def,ARM_MODE_def,
				     ARM_READ_CPSR_def]
	THEN RW_TAC (srw_ss()) []
);



val deduce_pr_from_pr_av_and_pr_no_av_thm =
    store_thm ("deduce_pr_from_pr_av_and_pr_no_av_thm",
``! m f uf uy is .
	      preserve_relation_mmu
	      f
	      (assert_mode_access_violation 16w )
	      (assert_mode_access_violation 16w )
	      uf uy
	      ==>
	      preserve_relation_mmu
	      f
	      (assert_mode_no_access_violation 16w )
	      (assert_mode m)
	      uf uy
	      ==>
	        preserve_relation_mmu
	      f
	      (assert_mode 16w)
	      (comb_mode 16w m )
	      uf uy
	   ``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_def]
		      THEN NTAC 2(PAT_ASSUM ``! g s1 s2.X``
					    (fn thm =>
						ASSUME_SPECL_TAC [``g:bool[32]``,
								  ``s1:arm_state``,
								  ``s2:arm_state``] thm))
		      THEN RES_TAC
		      THEN FULL_SIMP_TAC (srw_ss())
		      [ assert_mode_access_violation_def,
			assert_mode_no_access_violation_def,
			assert_mode_def,
			assert_mode_def,
			comb_mode_def,
			ARM_MODE_def,
			ARM_READ_CPSR_def]
		      THEN Cases_on `access_violation s1`
		      THEN RES_TAC
		      THEN IMP_RES_TAC (SPEC ``16w:bool[5]`` similar_states_have_same_mode_thm)
		      THEN IMP_RES_TAC (similar_states_have_same_av_thm1)
		      THEN IMP_RES_TAC (similar_states_have_same_av_thm2)
		      THEN FULL_SIMP_TAC (srw_ss()) []
	      );


(*val uy1 = ``priv_mode_similar``;*)
val uf1 = ``have_same_mem_accesses``;
val uy1 = ``tautology_fun``;
val uargs = [uf1,uy1,``27w:bool[5]``,``_pthm``];
val pthms = [trans_have_same_mem_accesses_thm,
	     reflex_have_same_mem_accesses_thm,
	     tautology_fun_def,
	     have_same_mem_accesses_def,
	     errorT_thm];

fun prove_write_read_bisimilarity trm1 trm2 =
    RW_TAC (let_ss) [preserve_relation_mmu_def,
		     read_cpsr_def,read__psr_def,readT_def,
		     write_cpsr_def,write__psr_def,writeT_def,
		     similar_def,untouched_def, have_same_mem_accesses_def,
		     seqT_def,errorT_def,tautology_fun_def,
		     priv_mode_similar_def,assert_mode_def]
	   THEN RW_TAC (srw_ss()) []
	   THEN FULL_SIMP_TAC (srw_ss()) []
	   THEN (FIRST_PROVE [
			UNDISCH_TAC ``s1.psrs (0,CPSR) =
			s2.psrs (0,CPSR)``
				    THEN EVAL_TAC
				    THEN RW_TAC (srw_ss()) []
				    THEN RW_TAC (srw_ss()) [],
			UNDISCH_TAC ``psr ≠ CPSR``
				    THEN EVAL_TAC
				    THEN RW_TAC (srw_ss()) []
				    THEN RW_TAC (srw_ss()) [],
			UNDISCH_TAC ``ARM_MODE s1 = 27w`` THEN
				    UNDISCH_TAC ``ARM_MODE s2 = 27w`` THEN
				    UNDISCH_TAC ``s1.psrs (0,CPSR) = s2.psrs (0,CPSR)``
				    THEN EVAL_TAC
				    THEN RW_TAC (srw_ss()) []
				    THEN RW_TAC (srw_ss()) [],
			(UNDISCH_TAC ``equal_user_register s1 s2``
				     THEN EVAL_TAC
				     THEN RW_TAC (srw_ss()) []),
 			ASSUME_TAC (SPECL [``s1:arm_state``,
					   trm1, ``g:bool[32]``]
					  trivially_untouched_av_lem2)
				   THEN ASSUME_TAC (
			SPECL [``s2:arm_state``,
			       trm2, ``g:bool[32]``]
			      trivially_untouched_av_lem2)
				   THEN RES_TAC
				   THEN FULL_SIMP_TAC (srw_ss()) []
				   THEN METIS_TAC [] ]);


val read_write_cpsr_abt_irq_thm =
    store_thm("read_write_cpsr_abt_irq_thm",
	      ``!u. (u<>16w) ==>
           preserve_relation_mmu
	     (read_cpsr <|proc:=0|> >>=
                  (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>)))
	     (assert_mode u) (assert_mode u) ^uf1 ^uy1``,
	      let val trm1 = ``   (s1 with
   		 psrs updated_by
   		      ((0,CPSR) =+
				s1.psrs (0,CPSR) with
		     <|IT := 0w; J := F; E := sctlr.EE;
		     A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
           (s2.psrs (0,CPSR)).A); I := T; T := sctlr.TE|>))``
		  val trm2 = ``  (s2 with
                   psrs updated_by
     		      ((0,CPSR) =+
			    s2.psrs (0,CPSR) with
		       <|IT := 0w; J := F; E := sctlr.EE;
                          A :=
                         ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                          (s2.psrs (0,CPSR)).A); I := T; T := sctlr.TE|>))``
	      in
		  prove_write_read_bisimilarity trm1 trm2
	      end
	     );

val read_write_cpsr_undef_svc_thm =
    store_thm("read_write_cpsr_undef_svc_thm",
	      ``!u. (u<>16w) ==> preserve_relation_mmu
	     (read_cpsr <|proc:=0|> >>=
				 (λcpsr. write_cpsr <|proc:=0|>
				(cpsr with
                                 <|IT := 0w; J := F; E := sctlr.EE;
                                    I := T; T := sctlr.TE|>)))
	     (assert_mode u) (assert_mode u) ^uf1 ^uy1``,
	      let val trm1 = ``   (s1 with
                              psrs updated_by
                                 ((0,CPSR) =+
	                          s1.psrs (0,CPSR) with
                               <|IT := 0w; J := F; E := sctlr.EE;
                              I := T; T := sctlr.TE|>))``
		  val trm2 = ``  (s2 with
                   psrs updated_by
                             ((0,CPSR) =+
	                        s2.psrs (0,CPSR) with
                               <|IT := 0w; J := F; E := sctlr.EE;
                              I := T; T := sctlr.TE|>))``
	      in
		  prove_write_read_bisimilarity trm1 trm2
	      end
	     );


val write_scr_cpsr_thm =
    store_thm("write_scr_cpsr_thm",
	      `` ∀g s1 s2 comp scr u.
	     ((comp = (condT (F) (write_scr <|proc := 0|> (scr with NS := F))
			    ||| write_cpsr <|proc := 0|> ((s1.psrs (0,CPSR) with M := u)))) \/
	     (comp = (condT (F) (write_scr <|proc := 0|> (scr with NS := F))
			    ||| write_cpsr <|proc := 0|> ((s2.psrs (0,CPSR) with M := u))))) ==>
	     (~access_violation s1)==>
	     mmu_requirements s1 g ⇒
	     mmu_requirements s2 g ⇒
	     similar g s1 s2 ⇒
	     (assert_mode 16w s1) ==>
	     (assert_mode 16w s2) ==>
	     (∃a s1' s2'.
               ( comp s1 = ValueState a s1') ∧
	       ( comp s2 = ValueState a s2') ∧
               untouched g s1 s1' ∧ untouched g s2 s2'
	       ∧ (assert_mode u s1') /\
		(assert_mode u s2') /\
	     (^uf1 g s1 s1') ∧
             (^uf1 g s2 s2') /\
		similar g s1' s2' /\
	     (~access_violation s1')/\
             (~access_violation s2')) ∨
	     ∃e. (comp s1 = Error e) ∧ (comp s2 = Error e)``,
	      let val trm1 = ``(s1 with
                      psrs updated_by ((0,CPSR) =+ s2.psrs (0,CPSR) with M := u))``
		  val trm2 = ``(s2 with
                      psrs updated_by ((0,CPSR) =+ s2.psrs (0,CPSR) with M := u))``
	      in
		  RW_TAC (let_ss) [preserve_relation_mmu_def,
				   write_cpsr_def,write__psr_def,
				   writeT_def,similar_def,untouched_def,
				   parT_def,constT_def,seqT_def,errorT_def,
				   tautology_fun_def,
				   priv_mode_similar_def,assert_mode_def,
				   condT_def,ARM_MODE_def,
				   ARM_READ_CPSR_def,have_same_mem_accesses_def]
			 THEN FULL_SIMP_TAC (srw_ss()) []
			 THEN RW_TAC (srw_ss()) []
			 THEN
			 FIRST_PROVE[
			 (TRY (UNDISCH_TAC ``psr ≠ CPSR``))
			     THEN (TRY (UNDISCH_TAC
					    ``s1.psrs (0,CPSR) = s2.psrs (0,CPSR)``))
			     THEN EVAL_TAC
			     THEN RW_TAC (srw_ss()) []
			     THEN FULL_SIMP_TAC (let_ss) [],
			 UNDISCH_TAC ``equal_user_register s1 s2``
				     THEN EVAL_TAC
				     THEN RW_TAC (srw_ss()) []
		       ,
		       ASSUME_TAC (SPECL [``s1:arm_state``,
					  trm1, ``g:bool[32]``]
					 trivially_untouched_av_lem2)
				  THEN ASSUME_TAC (
		       SPECL [``s2:arm_state``,
			      trm2, ``g:bool[32]``]
			     trivially_untouched_av_lem2)
				  THEN RES_TAC
				  THEN FULL_SIMP_TAC (srw_ss()) []
				  THEN METIS_TAC []
		       ,
		       TRY(UNDISCH_TAC
			       `` (((0,CPSR) =+ cpsr with M := u) s1.psrs (0,CPSR)).M = 16w``)
			  THEN (TRY(UNDISCH_TAC
					`` (((0,CPSR) =+ cpsr with M := u) s2.psrs (0,CPSR)).M = 16w``))
			  THEN EVAL_TAC
			  THEN RW_TAC (srw_ss()) []]
	      end
	     );


(* ================================================+++++========================== *)
(*           proof of preserve relation of write_spsr in no access violation case  *)
(* =====================================================+++++===================== *)


val prove_write__psr_thm =
fn mode => fn spsr =>
    let
	val trm1 = `` (s1 with psrs updated_by ((0,^spsr) =+ cpsr with M := 16w))``
	val trm2 = `` (s2 with psrs updated_by ((0,^spsr) =+ cpsr with M := 16w))``
    in
	RW_TAC (srw_ss()) [preserve_relation_mmu_def,
			   read_cpsr_def,read__psr_def,readT_def,
			   write_cpsr_def,write__psr_def,writeT_def,
			   similar_def,untouched_def,
			   seqT_def,errorT_def,tautology_fun_def,
			   priv_mode_similar_def,
			   assert_mode_def,have_same_mem_accesses_def]
	       THEN RW_TAC (srw_ss()) []
	       THEN FULL_SIMP_TAC (let_ss) []
	       THEN NTAC 9 (FIRST_PROVE [
			    UNDISCH_TAC ``s1.psrs (0,CPSR) = s2.psrs (0,CPSR)``
					THEN EVAL_TAC
					THEN RW_TAC (srw_ss()) []
					THEN RW_TAC (srw_ss()) [],
			    UNDISCH_TAC ``psr ≠ CPSR``
					THEN TRY (UNDISCH_TAC ``psr ≠ ^spsr``)
					THEN EVAL_TAC
					THEN RW_TAC (srw_ss()) []
					THEN RW_TAC (srw_ss()) [],
			    UNDISCH_TAC ``ARM_MODE s1 = ^mode`` THEN
					UNDISCH_TAC ``ARM_MODE s2 = ^mode`` THEN
					UNDISCH_TAC ``s1.psrs (0,CPSR) = s2.psrs (0,CPSR)``
					THEN EVAL_TAC
					THEN RW_TAC (srw_ss()) []
					THEN RW_TAC (srw_ss()) [],
			    UNDISCH_TAC ``equal_user_register s1 s2``
					THEN EVAL_TAC
					THEN RW_TAC (srw_ss()) [],
 			    ASSUME_TAC (SPECL [``s1:arm_state``,
					       trm1, ``g:bool[32]``]
					      trivially_untouched_av_lem2)
				       THEN ASSUME_TAC (
			    SPECL [``s2:arm_state``,
				   trm2, ``g:bool[32]``]
				  trivially_untouched_av_lem2)
				       THEN RES_TAC
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN METIS_TAC [] ])
    end;


val write__psr_und_thm =
    store_thm("write__psr_und_thm",
	      `` preserve_relation_mmu (write__psr <|proc := 0|>
		       (SPSR_und) (cpsr with M := 16w))
	     (assert_mode 27w) (assert_mode 27w) ^uf1 ^uy1 ``,
	      prove_write__psr_thm ``27w:bool[5]`` ``SPSR_und``);

val write__psr_svc_thm =
    store_thm("write__psr_undef_thm",
	      `` preserve_relation_mmu (write__psr <|proc := 0|>
		       (SPSR_svc) (cpsr with M := 16w))
	     (assert_mode 19w) (assert_mode 19w) ^uf1 ^uy1 ``,
	      prove_write__psr_thm ``19w:bool[5]`` ``SPSR_svc``);

val write__psr_irq_thm =
    store_thm("write__psr_irq_thm",
	      `` preserve_relation_mmu (write__psr <|proc := 0|>
		       (SPSR_irq) (cpsr with M := 16w))
	     (assert_mode 18w) (assert_mode 18w) ^uf1 ^uy1 ``,
	      prove_write__psr_thm ``18w:bool[5]`` ``SPSR_irq``);

val write__psr_fiq_thm =
    store_thm("write__psr_fiq_thm",
	      `` preserve_relation_mmu (write__psr <|proc := 0|>
		       (SPSR_fiq) (cpsr with M := 16w))
	     (assert_mode 17w) (assert_mode 17w) ^uf1 ^uy1 ``,
	      prove_write__psr_thm ``17w:bool[5]`` ``SPSR_fiq``);

val write__psr_abt_thm =
    store_thm("write__svc_abt_thm",
	      `` preserve_relation_mmu (write__psr <|proc := 0|>
		       (SPSR_abt) (cpsr with M := 16w))
	     (assert_mode 23w) (assert_mode 23w) ^uf1 ^uy1 ``,
	      prove_write__psr_thm ``23w:bool[5]`` ``SPSR_abt``);



val prove_write_spsr_thm =
fn mode => fn spsr =>
   let
       val (l,r,rb) =
	   decompose_term (rhs (concl (
				SIMP_CONV (srw_ss()) [write_spsr_def]
					  ``(write_spsr <|proc := 0|> (cpsr with M := 16w))``)));
   in
       RW_TAC (srw_ss()) [write_spsr_def]
	      THEN  ASSUME_TAC (SIMP_RULE (bool_ss) []
					  (SPECL [r,
						  ``(assert_mode ^mode)``, uf1,uy1, mode]
						 (INST_TYPE [alpha |-> ``:unit``]
							    switching_lemma_helperTheory.cpsr_simp_rel_lem)))
	      THEN FULL_SIMP_TAC (srw_ss()) []
	      THEN (WEAKEN_TAC is_eq)
	      THEN
	      (let val a =
		       ``(read_cpsr <|proc := 0|> >>=
                              (λcpsr'.
                                 bad_mode <|proc := 0|> ^mode >>=
                                 (λbad_mode.
                                    if bad_mode then
                                      errorT "write_spsr: unpredictable"
                                    else
                                      write__psr <|proc := 0|> ^spsr (cpsr with M := 16w))))``
		   val () = global_mode := mode ;
		   val pthms = pthms @ [write__psr_und_thm,write__psr_svc_thm,
					write__psr_abt_thm,write__psr_irq_thm,
					write__psr_fiq_thm];
		   val (thm,_) = prove a ``(assert_mode ^mode)``
				       ``(assert_mode ^mode)``
				       uargs pthms;
	       in
		   FULL_SIMP_TAC (srw_ss()) [thm]
	       end)
   end

val write_spsr_und_thm =
    store_thm("write_spsr_und_thm",
	      ``preserve_relation_mmu (write_spsr <|proc := 0|> (cpsr with M := 16w))
	     (assert_mode 27w) (assert_mode 27w) ^uf1 ^uy1 ``,
	prove_write_spsr_thm ``27w:bool[5]`` ``SPSR_und ``);

val write_spsr_svc_thm =
    store_thm("write_spsr_svc_thm",
	      ``preserve_relation_mmu (write_spsr <|proc := 0|> (cpsr with M := 16w))
	     (assert_mode 19w) (assert_mode 19w) ^uf1 ^uy1 ``,
	prove_write_spsr_thm ``19w:bool[5]`` ``SPSR_svc ``);

val write_spsr_abt_thm =
    store_thm("write_spsr_abt_thm",
	      ``preserve_relation_mmu (write_spsr <|proc := 0|> (cpsr with M := 16w))
	     (assert_mode 23w) (assert_mode 23w) ^uf1 ^uy1 ``,
	prove_write_spsr_thm ``23w:bool[5]`` ``SPSR_abt ``);

val write_spsr_irq_thm =
    store_thm("write_spsr_irq_thm",
	      ``preserve_relation_mmu (write_spsr <|proc := 0|> (cpsr with M := 16w))
	     (assert_mode 18w) (assert_mode 18w) ^uf1 ^uy1 ``,
	prove_write_spsr_thm ``18w:bool[5]`` ``SPSR_irq ``);

val write_spsr_fiq_thm =
    store_thm("write_spsr_fiq_thm",
	      ``preserve_relation_mmu (write_spsr <|proc := 0|> (cpsr with M := 16w))
	     (assert_mode 17w) (assert_mode 17w) ^uf1 ^uy1 ``,
	prove_write_spsr_thm ``17w:bool[5]`` ``SPSR_fiq ``);

val prove_write__reg_thm =
fn mode => fn reg =>  fn reg_set =>
    let
	val trm1 = ``(s1 with registers updated_by ((0,^reg) =+ value))``
	val trm2 = ``(s2 with registers updated_by ((0,^reg) =+ value))``
    in
	RW_TAC (srw_ss()) [preserve_relation_mmu_def,
			   write__reg_def,writeT_def,
			   similar_def,untouched_def,
			   seqT_def,errorT_def,tautology_fun_def,
			   priv_mode_similar_def,
			   assert_mode_def,have_same_mem_accesses_def]
	       THEN RW_TAC (srw_ss()) []
	       THEN FULL_SIMP_TAC (let_ss) []
	       THEN FIRST_PROVE [
	Q.UNABBREV_TAC ([QUOTE reg_set])
		       THEN FULL_SIMP_TAC (srw_ss()) []
		       THEN UNDISCH_TAC ``reg ≠ ^reg``
		       THEN EVAL_TAC
		       THEN FULL_SIMP_TAC (srw_ss()) [],

	UNDISCH_TAC ``ARM_MODE s1 = ^mode`` THEN
		    UNDISCH_TAC ``ARM_MODE s2 = ^mode``
		    THEN EVAL_TAC
		    THEN RW_TAC (srw_ss()) [],

	UNDISCH_TAC ``equal_user_register s1 s2``
		    THEN EVAL_TAC
		    THEN RW_TAC (srw_ss()) []
		    THEN METIS_TAC [],
 	ASSUME_TAC (SPECL [``s1:arm_state``,
			   trm1, ``g:bool[32]``]
			  trivially_untouched_av_lem2)
		   THEN ASSUME_TAC (
	SPECL [``s2:arm_state``,
	       trm2, ``g:bool[32]``]
	      trivially_untouched_av_lem2)
		   THEN RES_TAC
		   THEN FULL_SIMP_TAC (srw_ss()) []
	]
    end;


val write__reg_und_thm =
    store_thm("write__reg_und_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_LRund value)
		     (assert_mode 27w) (assert_mode 27w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``27w:bool[5]`` ``RName_LRund`` "und_regs"
	     );

val write__reg_abt_thm =
    store_thm("write__reg_abt_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_LRabt value)
		     (assert_mode 23w) (assert_mode 23w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``23w:bool[5]`` ``RName_LRabt`` "abort_regs"
	     );

val write__reg_irq_thm =
    store_thm("write__reg_irq_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_LRirq value)
		     (assert_mode  18w) (assert_mode 18w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``18w:bool[5]`` ``RName_LRirq`` "irq_regs"
	     );

val write__reg_fiq_thm =
    store_thm("write__reg_fiq_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_LRfiq value)
		     (assert_mode  17w) (assert_mode 17w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``17w:bool[5]`` ``RName_LRfiq`` "fiq_regs"
	     );

val write__reg_svc_thm =
    store_thm("write__reg_svc_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_LRsvc value)
		     (assert_mode  19w) (assert_mode 19w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``19w:bool[5]`` ``RName_LRsvc`` "svc_regs"
	     );

val write__pc_und_thm =
    store_thm("write__pc_und_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_PC value)
		     (assert_mode 27w) (assert_mode 27w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``27w:bool[5]`` ``RName_PC:RName`` "user_regs"
	   );
val write__pc_abt_thm =
    store_thm("write__pc_abt_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_PC value)
		     (assert_mode 23w) (assert_mode 23w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``23w:bool[5]`` ``RName_PC:RName`` "user_regs"
	   );
val write__pc_irq_thm =
    store_thm("write__pc_irq_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_PC value)
		     (assert_mode 18w) (assert_mode 18w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``18w:bool[5]`` ``RName_PC:RName`` "user_regs"
	   );
val write__pc_svc_thm =
    store_thm("write__pc_svc_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_PC value)
		     (assert_mode 19w) (assert_mode 19w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``19w:bool[5]`` ``RName_PC:RName`` "user_regs"
	   );
val write__pc_fiq_thm =
    store_thm("write__pc_fiq_thm",
	      ``(preserve_relation_mmu
		     (write__reg <|proc := 0|> RName_PC value)
		     (assert_mode 17w) (assert_mode 17w) ^uf1 ^uy1)``,
	      prove_write__reg_thm ``17w:bool[5]`` ``RName_PC:RName`` "user_regs"
	   );

val prove_write_link_reg_thm =
 fn mode => fn lr =>
 `LookUpRName <|proc := 0|> (14w,^mode) >>=
	(λrname. write__reg <|proc := 0|> rname value) =
	LookUpRName <|proc := 0|> (14w,^mode) >>=
	(λrname. write__reg <|proc := 0|> ^lr value)`
     by  (RW_TAC (srw_ss()) [LookUpRName_def,write__reg_def,
			     writeT_def,RBankSelect_def,bad_mode_def,
			     constT_def,seqT_def] THEN ABS_TAC
		 THEN RW_TAC (srw_ss()) [])
     THEN RW_TAC (srw_ss()) [write_reg_def,
			     write_reg_mode_def]
     (* THEN FULL_SIMP_TAC (srw_ss()) [] *)
     THEN
     let val l = ``(λcpsr.
                         (is_secure <|proc := 0|> ||| read_nsacr <|proc := 0|>
                             ||| current_instr_set <|proc := 0|>) >>=
                          (λ(is_secure,nsacr,current_instr_set).
                             if
                               ¬is_secure ∧ ((cpsr.M = 22w) ∨ (cpsr.M = 17w) ∧ nsacr.RFR)
                             then
                               errorT "write_reg_mode: unpredictable"
                             else
                               LookUpRName <|proc := 0|> (14w,cpsr.M) >>=
                               (λrname. write__reg <|proc := 0|> rname value)))``
			   val a = ``(read_cpsr <|proc := 0|> >>=
                            (λcpsr.
                               (is_secure <|proc := 0|> ||| read_nsacr <|proc := 0|>
                                  ||| current_instr_set <|proc := 0|>) >>=
                               (λ(is_secure,nsacr,current_instr_set).
                                  LookUpRName <|proc := 0|> (14w,^mode) >>=
                                  (λrname. write__reg <|proc := 0|> ^lr value))))``
      in
	  ASSUME_TAC (SIMP_RULE (bool_ss) []
				(SPECL [l, ``(assert_mode ^mode)``,
					uf1,uy1,mode]
				       (INST_TYPE [alpha |-> ``:unit``]
						  switching_lemma_helperTheory.cpsr_simp_rel_lem)))
		     THEN FULL_SIMP_TAC (srw_ss()) []
		     THEN REPEAT (WEAKEN_TAC is_eq)
		     THEN
		     (let
			  val pthms = pthms @
				      [write__reg_und_thm,
				       write__reg_irq_thm,
				       write__reg_fiq_thm,
				       write__reg_svc_thm,
				       write__reg_abt_thm];
			  val () = global_mode := mode;
			  val (thm,_) = prove a ``(assert_mode ^mode)``
					      ``(assert_mode ^mode)``
					      uargs pthms;
		      in
			  FULL_SIMP_TAC (srw_ss()) [thm]
		      end)
      end;

val write_reg_und_thm =
    store_thm("write_reg_und_thm",
	     ``preserve_relation_mmu
	      (write_reg <|proc := 0|> 14w value)
	      (assert_mode 27w) (assert_mode 27w) ^uf1 ^uy1``,
	      prove_write_link_reg_thm ``27w:bool[5]`` ``RName_LRund``
	     );

val write_reg_svc_thm =
    store_thm("write_reg_svc_thm",
	     ``preserve_relation_mmu
	      (write_reg <|proc := 0|> 14w value)
	      (assert_mode 19w) (assert_mode 19w) ^uf1 ^uy1``,
	      prove_write_link_reg_thm ``19w:bool[5]`` ``RName_LRsvc``
	     );

val write_reg_abt_thm =
    store_thm("write_reg_abt_thm",
	     ``preserve_relation_mmu
	      (write_reg <|proc := 0|> 14w value)
	      (assert_mode 23w) (assert_mode 23w) ^uf1 ^uy1``,
	      prove_write_link_reg_thm ``23w:bool[5]`` ``RName_LRabt``
	     );

val write_reg_irq_thm =
    store_thm("write_reg_irq_thm",
	     ``preserve_relation_mmu
	      (write_reg <|proc := 0|> 14w value)
	      (assert_mode 18w) (assert_mode 18w) ^uf1 ^uy1``,
	      prove_write_link_reg_thm ``18w:bool[5]`` ``RName_LRirq``
	     );

(* the body of write is different from the rest *)

(* val write_reg_fiq_thm = *)
(*     store_thm("write_reg_fiq_thm", *)
(* 	     ``preserve_relation_mmu *)
(* 	      (write_reg <|proc := 0|> 14w value) *)
(* 	      (assert_mode 17w) (assert_mode 17w) ^uf1 ^uy1``, *)
(* 	      prove_write_link_reg_thm ``17w:bool[5]`` ``RName_LRfiq`` *)
(* 	     ); *)

(* ================================================+++++========================== *)
(*                   proof of preserve relation of writing part
                    of take exception in no access violation case                  *)
(* =====================================================+++++===================== *)

val write_scr_cpsr_preconds_def =
    Define `write_scr_cpsr_preconds g s1 s2 =
	   (~access_violation s1)
	   /\  (mmu_requirements s1 g)
	   /\ (mmu_requirements s2 g)
	   /\ (similar g s1 s2)
	   /\ (tautology_fun g s1 s2)
	   /\ (¬access_violation s1)
	   /\ ((s1.psrs (0,CPSR)).M = 16w)
	   /\ (¬access_violation s2)
	   /\ ((s2.psrs (0,CPSR)).M = 16w )`;


val TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC =
fn mode =>
   let
	val comp2 = ``(condT F (write_scr <|proc := 0|> (scr with NS := F))
			     ||| write_cpsr <|proc := 0|>
						       (s2.psrs (0,CPSR) with M := ^mode))``;
    in
	RW_TAC (srw_ss())  []
	       THEN ASSUME_TAC (SIMP_RULE (srw_ss())
 					  [assert_mode_def,ARM_MODE_def,
					   ARM_READ_CPSR_def,condT_def]
					  (SPECL [``g:bool[32]``,``s1:arm_state``,
						  ``s2:arm_state``, comp2,
						  ``scr:CP15scr``,mode] write_scr_cpsr_thm))
	       THEN RES_TAC
	       THEN FULL_SIMP_TAC (srw_ss())  [seqT_def,write_scr_cpsr_preconds_def]
	       THEN RW_TAC (srw_ss())  []
	       THEN FULL_SIMP_TAC (srw_ss())  []
    end;

val TAKE_EXCEPTION_MODE_CHANGING_VALUESTATE_TAC =
 fn (si ,si' , a , b, mode) =>
    let
	val l2 = ``(constT ()
			   ||| write_cpsr <|proc := 0|>
						     (s2.psrs (0,CPSR) with M := ^mode))``
	val comp2 = ``(condT F (write_scr <|proc := 0|> (scr with NS := F))
			     ||| write_cpsr <|proc := 0|>
						       (s2.psrs (0,CPSR) with M := ^mode))``;
    in
	ASSUME_TAC (REWRITE_RULE
 			[assert_mode_def,ARM_MODE_def,
			 ARM_READ_CPSR_def,condT_def]
			(SPECL [``g:bool[32]``,``s1:arm_state``,
				``s2:arm_state``, comp2,
				``scr:CP15scr``,mode] write_scr_cpsr_thm))
		   THEN RES_TAC
		   THEN REPEAT (WEAKEN_TAC is_imp)
		   THEN PAT_ASSUM ``X c s1= ValueState a b``
		   (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		   THEN PAT_ASSUM ``X c' s2= ValueState a' b'``
		   (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		   THEN PAT_ASSUM ``X c s1= ValueState a b``
		   (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		   THEN FULL_SIMP_TAC (srw_ss()) []
		   THEN IMP_RES_TAC untouched_mmu_setup_lem
		   THEN PAT_ASSUM ``∀c g s1 s2. X ``
		   (fn thm => ASSUME_TAC
				  (SPECL [``a:unit#unit``,``g:bool[32]``,
					  ``s1':arm_state``,
					  ``s2':arm_state``] thm))
		   THEN RES_TAC
		   THEN IMP_RES_TAC
		   (SPECL [l2, ``H2:unit#unit->unit M``, si, a,
			   b, ``a'':unit#unit``,
			   si', ``e:string``]
			  (INST_TYPE [alpha |-> ``:unit#unit``,
				      beta |-> ``:unit``] hlp_seqT2_thm))
		   THEN IMP_RES_TAC (SIMP_RULE (srw_ss())
					       [ARM_MODE_def,ARM_READ_CPSR_def]
					       untouched_trans)
		   THEN FULL_SIMP_TAC (srw_ss()) []
		   THEN RW_TAC (srw_ss()) []
    end;

val take_exp_mode_changing_ut_thm =
    store_thm ("take_exp_mode_changing_ut_thm",
	       ``! H2 s1 s2 g u.
    let f2 = (((if (s2.psrs (0,CPSR)).M = 22w then
		 write_scr <|proc := 0|>  (s2.coprocessors.state.cp15.SCR with NS := F)
		else
	         constT ()) ||| write_cpsr <|proc := 0|>
		 (s2.psrs (0,CPSR) with M := u)) >>= (H2:unit#unit->unit M))
    in
        (write_scr_cpsr_preconds g s1 s2)
	    ==>
	    (preserve_relation_mmu_abs H2 (assert_mode u) (assert_mode u)
				       have_same_mem_accesses tautology_fun) ==>
	    ((? a b a' b'. (f2  s1 = ValueState a b) /\ (f2  s2 = ValueState a' b')
	      /\ (untouched g s1 b ∧ untouched g s2 b' ∧
		  tautology_fun g b b'))
             \/
	     (?e. (f2 s1 =Error e) /\ (f2 s2 = Error e)))
	    ``,
	      FULL_SIMP_TAC (let_ss) [preserve_relation_mmu_abs_def,
			  condT_def,tautology_fun_def,
			  assert_mode_def,ARM_MODE_def,
			  ARM_READ_CPSR_def,write_scr_cpsr_preconds_def]
		THEN RW_TAC (srw_ss()) []
		THEN Cases_on
		`(constT ()
			 ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s1`
		THEN  Cases_on
		`(constT ()
			 ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s2`
		THEN FIRST_PROVE
		[ TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]`` ,
		  RW_TAC (srw_ss()) [seqT_def]
			 THEN FIRST_PROVE
			 [
			  TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]``,
			  TAKE_EXCEPTION_MODE_CHANGING_VALUESTATE_TAC (
			  ``s1:arm_state`` ,``s1':arm_state``,
			  ``a:unit`` , ``b:arm_state``,``u:bool[5]``)]
		]
	      );


val take_exp_mode_changing_same_access_thm =
    store_thm ("take_exp_mode_changing_same_access_thm",
	       ``! H2 s1 s2 g u .
    let f2 = (((if (s2.psrs (0,CPSR)).M = 22w then
		    write_scr <|proc := 0|>
		 (s2.coprocessors.state.cp15.SCR with NS := F)
		else
		    constT ())  ||| write_cpsr <|proc := 0|>
		(s2.psrs (0,CPSR) with M := u)) >>= (H2:unit#unit->unit M))
    in
        (write_scr_cpsr_preconds g s1 s2)
	    ==>
	    (preserve_relation_mmu_abs H2 (assert_mode u) (assert_mode u)
				       have_same_mem_accesses tautology_fun) ==>
	    ((? a b a' b'. (f2  s1 = ValueState a b) /\ (f2  s2 = ValueState a' b')
	      /\  (have_same_mem_accesses g s1 b ∧ have_same_mem_accesses g s2 b'))
	\/
	(?e. (f2  s1 = Error e) /\  (f2  s2 = Error e) ))
	  ``,
	       FULL_SIMP_TAC (let_ss) [preserve_relation_mmu_abs_def,
				       condT_def,tautology_fun_def,
				       assert_mode_def,ARM_MODE_def,
				       ARM_READ_CPSR_def,write_scr_cpsr_preconds_def]
			     THEN RW_TAC (srw_ss()) []
			     THEN Cases_on `(constT () ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s1`
			     THEN  Cases_on `(constT () ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s2`
			     (*THEN FULL_SIMP_TAC (srw_ss())  []*)
			     THEN FIRST_PROVE
			     [ TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]``,
			       RW_TAC (srw_ss()) [seqT_def]
				      THEN FIRST_PROVE
				      [
				       TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]``,
				       TAKE_EXCEPTION_MODE_CHANGING_VALUESTATE_TAC
					   (
					    ``s1:arm_state`` ,``s1':arm_state``,
					    ``a:unit`` , ``b:arm_state``,``u:bool[5]``)
					   THEN IMP_RES_TAC (SIMP_RULE (srw_ss())
								       [trans_fun_def]
								       trans_have_same_mem_accesses_thm)
					   THEN FULL_SIMP_TAC (srw_ss()) []
			     ]]
	      );


val take_exp_mode_changing_misc_thm =
    store_thm ("take_exp_mode_changing_misc_thm",
	       ``! H2  s1 s2 g u.
    let f2 = (((if (s2.psrs (0,CPSR)).M = 22w then
		    write_scr <|proc := 0|>
		(s2.coprocessors.state.cp15.SCR with NS := F)
		else
		    constT ()) ||| write_cpsr <|proc := 0|>
		(s2.psrs (0,CPSR) with M := u)) >>= (H2:unit#unit->unit M))
    in
	(preserve_relation_mmu_abs H2 (assert_mode u) (assert_mode u)
				   have_same_mem_accesses tautology_fun)
	    ==>
	    (write_scr_cpsr_preconds g s1 s2)
	    ==>
	    ((? a a' b b'. (f2  s1 = ValueState a b)  /\ (f2  s2 = ValueState a' b')
	      /\ ((a' = a) ∧ ((b.psrs (0,CPSR)).M = u) ∧
			   ((b'.psrs (0,CPSR)).M = u) ∧ similar g b b'))
		\/
		(?e. (f2  s1 = Error e)  /\ (f2  s2 = Error e) ))``,
	       FULL_SIMP_TAC (let_ss) [preserve_relation_mmu_abs_def,
				       condT_def,tautology_fun_def,
				       assert_mode_def,ARM_MODE_def,
				       ARM_READ_CPSR_def,write_scr_cpsr_preconds_def]
			     THEN RW_TAC (srw_ss()) []
			     THEN Cases_on `(constT ()  ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s1`
			     THEN  Cases_on `(constT () ||| write_cpsr <|proc := 0|> (s2.psrs (0,CPSR) with M := u)) s2`
			     (*THEN FULL_SIMP_TAC (srw_ss())  []*)
			     THEN FIRST_PROVE
			     [ TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]``,
			       RW_TAC (srw_ss()) [seqT_def]
				      THEN FIRST_PROVE
				      [
				       TAKE_EXCEPTION_MODE_CHANGING_ERROR_TAC ``u:bool[5]``,
				       TAKE_EXCEPTION_MODE_CHANGING_VALUESTATE_TAC
					   (
					    ``s1:arm_state`` ,``s1':arm_state``,
					    ``a:unit`` , ``b:arm_state``,``u:bool[5]``)
					   THEN FULL_SIMP_TAC (srw_ss()) [] ]] );

val take_exp_mode_changing_thm =
    store_thm ("take_exp_mode_changing_thm",
	       ``!  H s1 s2 (* a a'  b b' *) g u .
    let f = (((if (s2.psrs (0,CPSR)).M = 22w then
		   write_scr <|proc := 0|>
			(s2.coprocessors.state.cp15.SCR with NS := F)
               else
		   constT ()) ||| write_cpsr <|proc := 0|>
			 (s2.psrs (0,CPSR) with M := u)) >>= (H:unit#unit->unit M))
    in
	(write_scr_cpsr_preconds g s1 s2)
	    ==>
	    (preserve_relation_mmu_abs H (assert_mode u) (assert_mode u)
				       have_same_mem_accesses tautology_fun) ==>
	    ((? a b a' b'.  (f   s1 = ValueState a b) /\ (f  s2 = ValueState a' b')
	      /\((a' = a) ∧ ((b.psrs (0,CPSR)).M = u) ∧
		((b'.psrs (0,CPSR)).M = u) ∧ similar g b b' /\
                (have_same_mem_accesses g s1 b ∧ have_same_mem_accesses g s2 b')/\
                (untouched g s1 b ∧ untouched g s2 b' /\ tautology_fun g b b')))
	\/
	(? e. (f s1=Error e) /\ (f s2 = Error e)))
	    ``,
	       let
		   val vars = [``H:unit#unit->unit M``, ``s1:arm_state``,
			       ``s2:arm_state``,``g:bool[32]``,``u:bool[5]``];
		   val comp2 = ``(condT F (write_scr <|proc := 0|> (scr with NS := F))
					||| write_cpsr <|proc := 0|>
								  (s2.psrs (0,CPSR) with M := u))``;
	       in
		   FULL_SIMP_TAC (let_ss)  []
       				 THEN RW_TAC (srw_ss())  []
				 THEN MP_TAC (SPECL vars take_exp_mode_changing_ut_thm)
				 THEN MP_TAC (SPECL vars take_exp_mode_changing_same_access_thm)
				 THEN MP_TAC (SPECL vars take_exp_mode_changing_misc_thm)
				 THEN FULL_SIMP_TAC (let_ss)  []
				 THEN UNDISCH_ALL_TAC
				 THEN RW_TAC (srw_ss())  []
				 THEN FULL_SIMP_TAC (srw_ss())  []
				 THEN RW_TAC (srw_ss())  []
	       end
	      );

(****SHOULD BE REPLACED *************)

(* val H'= ``(λ(u1:unit,u2:unit).(write_spsr <|proc := 0|> (s2.psrs (0,CPSR) with M := 16w) *)
(*                ||| write_reg <|proc := 0|> 14w *)
(*                      (if (s2.psrs (0,CPSR) with M := 16w).T then *)
(*                         get_pc_value s2 − 2w *)
(*                       else *)
(*                         get_pc_value s2 − 4w) *)
(*                ||| read_cpsr <|proc := 0|> >>= *)
(*                    (λcpsr. *)
(*                       write_cpsr <|proc := 0|> *)
(*                         (cpsr with *)
(*                          <|I := T; IT := 0w; J := F; *)
(*                            T := s2.coprocessors.state.cp15.SCTLR.TE; *)
(*                            E := s2.coprocessors.state.cp15.SCTLR.EE|>)) *)
(*                ||| branch_to <|proc := 0|> *)
(*                      (get_base_vector_table s2 + 4w)) *)
(* 	    >>= *)
(*             (λ(u1,u2,u3,u4). constT ()))``; *)


fun prove_take_exception_nav_thm
	te_body te_def mode
	fixed_rp_thm  const_comp_rp_thm
	read_part_thm write_part_thm wp_specl simpr
  =
  let  val (lp,rp,_)= decompose_term te_body;
       val al_type = get_monad_type (type_of (lp));
  in
    RW_TAC (bool_ss) [te_def,
		      preserve_relation_mmu_def,
		      assert_mode_no_access_violation_def]
	   THEN  Cases_on [QUOTE ("("^(term_to_string lp) ^ ") s1")]
	   THEN Cases_on [QUOTE ("("^(term_to_string lp) ^ ") s2")]
	   THEN FIRST_PROVE
	   [
	    ASSUME_SPECL_SIMP_TAC
		[``g:bool[32]``,
		 ``s1:arm_state``,
		 ``s2:arm_state``]
		[preserve_relation_mmu_def,assert_mode_def,
		 ARM_MODE_def,ARM_READ_CPSR_def] read_part_thm
		THEN RES_TAC
		THEN IMP_RES_SPEC_TAC rp
		(INST_TYPE [alpha |-> al_type,
			    beta|-> ``:unit``]
			   hlp_seqT3_thm)
		THEN FULL_SIMP_TAC (srw_ss()) []
		THEN RW_TAC (srw_ss()) []
	  ,
	  Cases_on [QUOTE ("("^(term_to_string te_body) ^ ") s1")]
		   THEN Cases_on [QUOTE ("("^(term_to_string te_body) ^ ") s2")]
		   THEN IMP_RES_SPECL_TAC [``s:arm_state``, rp]
		   fixed_rp_thm
		   THEN FULL_SIMP_TAC (srw_ss()) []
		   THEN ASSUME_TAC const_comp_rp_thm
		   THEN IMP_RES_SPECL_TAC [lp] (INST_TYPE [alpha |-> al_type,
							   beta |-> ``:unit``]
							  const_comp_hlp_thm)
		   THEN FULL_SIMP_TAC (srw_ss()) [condT_def]
		   THEN (VALID (NTAC 2 (WEAKEN_TAC is_forall)))
		   THEN (VALID (PAT_ASSUM ``g a s = g' a s``
		   			  (fn thm => THROW_AWAY_TAC (concl thm))))
		       (*reduced to the right part *)
		   THEN EVERY_ASSUM (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		   THEN IMP_RES_TAC similar_states_have_same_vec_tab_thm
		   THEN IMP_RES_TAC similar_states_have_same_read_pc_thm
		   THEN IMP_RES_TAC similar_states_have_same_security_ext_thm
		   THEN PAT_ASSUM ``similar g s1 s2``
		   (fn thm => FULL_SIMP_TAC (srw_ss())
					    [REWRITE_RULE [similar_def,
							   equal_user_register_def
							  ]
							  thm]
					    THEN ASSUME_TAC thm )
		   THEN FULL_SIMP_TAC (srw_ss()) []
		   (* verything is based on s2 state and without lambda abs*)
		   THEN ASSUME_SPECL_TAC wp_specl
		   (GEN_ALL write_part_thm)
		   THEN ASSUME_SPECL_SIMP_TAC
		   [simpr,``s1:arm_state``,``s2:arm_state``, ``g:bool[32]``,mode]
		   [write_scr_cpsr_preconds_def]
		   (SIMP_RULE (let_ss) []
			      take_exp_mode_changing_thm)
		   THEN FULL_SIMP_TAC (let_ss) [assert_mode_def,ARM_MODE_def,
						ARM_READ_CPSR_def]
		   THEN IMP_RES_TAC similar_states_have_same_av_thm1
		   THEN IMP_RES_TAC similar_states_have_same_mode_thm

		   THEN UNDISCH_ALL_TAC
		   THEN FULL_SIMP_TAC (srw_ss()) []
		   THEN RW_TAC (srw_ss()) []
		   THEN METIS_TAC [hlp_seqT3_thm]
	   ]
  end;


val get_take_abt_irq_simp_pars =
 fn x => (
 ``λ(u1:unit,u2:unit).
  (write_spsr <|proc := 0|> (cpsr with M := 16w)
     ||| write_reg <|proc := 0|> 14w
	   (if (cpsr with M := 16w).T then pc else pc − 4w)
     ||| read_cpsr <|proc := 0|> >>=
	 (λcpsr.
	    write_cpsr <|proc := 0|>
	      (cpsr with
	       <|I := T;
		 A :=
		   ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
		    cpsr.A); IT := 0w; J := F; T := sctlr.TE;
		 E := sctlr.EE|>))
     ||| branch_to <|proc := 0|> (ExcVectorBase + ^x)) >>=
   (λ(u1,u2,u3,u4). constT ())``
 ,
``(λ(u1:unit,u2:unit).
   (write_spsr <|proc := 0|> (s2.psrs (0,CPSR) with M := 16w)
      ||| write_reg <|proc := 0|> 14w
	    (if (s2.psrs (0,CPSR) with M := 16w).T then
	       get_pc_value s2
	     else
	       get_pc_value s2 − 4w)
      ||| read_cpsr <|proc := 0|> >>=
	  (λcpsr.
	     write_cpsr <|proc := 0|>
	       (cpsr with
		<|I := T;
		  A :=
		    ((¬get_security_ext s2 ∨
		      ¬s2.coprocessors.state.cp15.SCR.NS ∨
		      s2.coprocessors.state.cp15.SCR.AW) ∨
		     cpsr.A); IT := 0w; J := F;
		  T := s2.coprocessors.state.cp15.SCTLR.TE;
		  E := s2.coprocessors.state.cp15.SCTLR.EE|>))
      ||| branch_to <|proc := 0|>
	    (get_base_vector_table s2 + ^x)) >>=
   (λ(u1,u2,u3,u4). constT ()))``);

val get_take_undef_svc_simp_pars =
 fn x => ( ``λ(u1:unit,u2:unit).
      (write_spsr <|proc := 0|> (cpsr with M := 16w)
	 ||| write_reg <|proc := 0|> 14w
	       (if (cpsr with M := 16w).T then pc − 2w else pc − 4w)
	 ||| read_cpsr <|proc := 0|> >>=
	     (λcpsr.
		write_cpsr <|proc := 0|>
		  (cpsr with
		   <|I := T; IT := 0w; J := F; T := sctlr.TE;
		     E := sctlr.EE|>))
	 ||| branch_to <|proc := 0|> (ExcVectorBase + ^x)) >>=
      (λ(u1,u2,u3,u4). constT ())``,
	   ``(λ(u1:unit,u2:unit).
      (write_spsr <|proc := 0|> (s2.psrs (0,CPSR) with M := 16w)
	 ||| write_reg <|proc := 0|> 14w
	       (if (s2.psrs (0,CPSR) with M := 16w).T then
		  get_pc_value s2 -2w
		else
		  get_pc_value s2 − 4w)
	 ||| read_cpsr <|proc := 0|> >>=
	     (λcpsr.
		write_cpsr <|proc := 0|>
		  (cpsr with
		   <|I := T;
		     IT := 0w; J := F;
		     T := s2.coprocessors.state.cp15.SCTLR.TE;
		     E := s2.coprocessors.state.cp15.SCTLR.EE|>))
	 ||| branch_to <|proc := 0|>
	       (get_base_vector_table s2 + ^x)) >>=
      (λ(u1,u2,u3,u4). constT ()))``);


val take_data_abort_exception_nav_thm =
    store_thm ("take_data_abort_exception_nav_thm",
	       ``preserve_relation_mmu
	      (take_data_abort_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 23w) ^uf1 ^uy1``,
	       let
		   val (_,te_body) =
		       (dest_eq o concl) (REWRITE_CONV [take_data_abort_exception_def]
						       ``take_data_abort_exception <|proc:=0|> ``);
		   val (lp,rp,_)= decompose_term te_body;
		   (*proof of reading part *)
		   val () = global_mode := ``16w:bool[5]``;
		   val (read_part_thm,_) =
		       prove lp ``(assert_mode 16w)`` ``(assert_mode 16w)`` uargs pthms;
		   val (writing_part , simpr) = get_take_abt_irq_simp_pars
						    ``16w:bool[32]``

		   val () = global_mode := ``23w:bool[5]``;
		   val pthms = [trans_have_same_mem_accesses_thm,
				reflex_have_same_mem_accesses_thm,
				tautology_fun_def,
				have_same_mem_accesses_def,
				errorT_thm,
				SIMP_RULE (srw_ss()) []
					  (SPEC ``23w:bool[5]`` read_write_cpsr_abt_irq_thm),
				write_spsr_abt_thm,
				write_reg_abt_thm,
				write__pc_abt_thm
			       ];
		   val (write_part_thm,_) = prove writing_part
						  ``(assert_mode 23w)`` ``(assert_mode 23w)``
						  uargs pthms;
		   val wp_specl = [``(s2.coprocessors.state.cp15.SCTLR):CP15sctlr``,
				   ``s2.coprocessors.state.cp15.SCR:CP15scr``,
				   ``get_pc_value s2``,
				   ``get_security_ext s2``,
				   ``(s2.psrs (0,CPSR)):ARMpsr``,
				   ``get_base_vector_table s2``];
		   val fixed_rp_thm = fixed_abt_irq_exception_rp_thm3;
		   val const_comp_rp_thm =  const_comp_take_abort_irq_exception_rp_thm;

	       in
		   prove_take_exception_nav_thm
			   te_body take_data_abort_exception_def ``23w:bool[5]``
			   fixed_rp_thm  const_comp_rp_thm
			   read_part_thm write_part_thm wp_specl simpr
	       end);


val take_prefetch_abort_exception_nav_thm =
    store_thm ("take_prefetch_exception_nav_thm",
	       ``preserve_relation_mmu
	      (take_prefetch_abort_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 23w) ^uf1 ^uy1``,
	       let
		   val (_,te_body) =
		       (dest_eq o concl) (REWRITE_CONV [take_prefetch_abort_exception_def]
						       ``take_prefetch_abort_exception <|proc:=0|> ``);
		   val (lp,rp,_)= decompose_term te_body;
		   (*proof of reading part *)
		   val () = global_mode := ``16w:bool[5]``;
		   val (read_part_thm,_) =
		       prove lp ``(assert_mode 16w)`` ``(assert_mode 16w)`` uargs pthms;

		   val (writing_part , simpr) = get_take_abt_irq_simp_pars
						    ``12w:bool[32]``

		   val () = global_mode := ``23w:bool[5]``;
		   val pthms = [trans_have_same_mem_accesses_thm,
				reflex_have_same_mem_accesses_thm,
				tautology_fun_def,
				have_same_mem_accesses_def,
				errorT_thm,
				SIMP_RULE (srw_ss()) []
					  (SPEC ``23w:bool[5]`` read_write_cpsr_abt_irq_thm),
				write_spsr_abt_thm,
				write_reg_abt_thm,
				write__pc_abt_thm
			       ];
		   val (write_part_thm,_) = prove writing_part
						  ``(assert_mode 23w)`` ``(assert_mode 23w)``
						  uargs pthms;
		   val wp_specl = [``(s2.coprocessors.state.cp15.SCTLR):CP15sctlr``,
				   ``s2.coprocessors.state.cp15.SCR:CP15scr``,
				   ``get_pc_value s2``,
				   ``get_security_ext s2``,
				   ``(s2.psrs (0,CPSR)):ARMpsr``,
				   ``get_base_vector_table s2``];
		   val fixed_rp_thm = fixed_abt_irq_exception_rp_thm3;
		   val const_comp_rp_thm =  const_comp_take_abort_irq_exception_rp_thm;

	       in
		   prove_take_exception_nav_thm
			   te_body take_prefetch_abort_exception_def ``23w:bool[5]``
			   fixed_rp_thm  const_comp_rp_thm
			   read_part_thm write_part_thm wp_specl simpr
	       end);


val take_irq_exception_nav_thm =
    store_thm ("take_irq_exception_nav_thm",
	       ``preserve_relation_mmu
	      (take_irq_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 18w) ^uf1 ^uy1``,
	       let
		   val (_,te_body) =
		       (dest_eq o concl) (REWRITE_CONV [take_irq_exception_def]
						       ``take_irq_exception <|proc:=0|> ``);
		   val (lp,rp,_)= decompose_term te_body;
		   (*proof of reading part *)
		   val () = global_mode := ``16w:bool[5]``;
		   val (read_part_thm,_) =
		       prove lp ``(assert_mode 16w)`` ``(assert_mode 16w)`` uargs pthms;

		   val (writing_part , simpr) = get_take_abt_irq_simp_pars
						    ``24w:bool[32]`` ;

		   val () = global_mode := ``18w:bool[5]``;
		   val pthms = [trans_have_same_mem_accesses_thm,
				reflex_have_same_mem_accesses_thm,
				tautology_fun_def,
				have_same_mem_accesses_def,
				errorT_thm,
				SIMP_RULE bool_ss []
					  (SPEC ``18w:bool[5]`` read_write_cpsr_abt_irq_thm),
				write_spsr_irq_thm,
				write_reg_irq_thm,
				write__pc_irq_thm
			       ];
		   val (write_part_thm,_) = prove writing_part
						  ``(assert_mode 18w)`` ``(assert_mode 18w)``
						  uargs pthms;
		   val wp_specl = [``(s2.coprocessors.state.cp15.SCTLR):CP15sctlr``,
				   ``s2.coprocessors.state.cp15.SCR:CP15scr``,
				   ``get_pc_value s2``,
				   ``get_security_ext s2``,
				   ``(s2.psrs (0,CPSR)):ARMpsr``,
				   ``get_base_vector_table s2``];
		   val fixed_rp_thm = fixed_abt_irq_exception_rp_thm3;
		   val const_comp_rp_thm =  const_comp_take_abort_irq_exception_rp_thm;

	       in
		   prove_take_exception_nav_thm
			   te_body take_irq_exception_def ``18w:bool[5]``
			   fixed_rp_thm  const_comp_rp_thm
			   read_part_thm write_part_thm wp_specl simpr
	       end);


val take_undef_instr_exception_nav_thm =
    store_thm ("take_undef_instr_exception_nav_thm",
	       ``preserve_relation_mmu
	      (take_undef_instr_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 27w) ^uf1 ^uy1``,
	       let
		   val (_,te_body) =
		       (dest_eq o concl) (REWRITE_CONV [take_undef_instr_exception_def]
						       ``take_undef_instr_exception <|proc:=0|> ``);
		   val (lp,rp,_)= decompose_term te_body;
		   (*proof of reading part *)
		   val () = global_mode := ``16w:bool[5]``;
		   val (read_part_thm,_) =
		       prove lp ``(assert_mode 16w)`` ``(assert_mode 16w)`` uargs pthms;

		   (*proof of writing part *)
		    val (writing_part , simpr) = get_take_undef_svc_simp_pars ``4w:bool[32]``

		    val () = global_mode := ``27w:bool[5]``;
		    val pthms = [trans_have_same_mem_accesses_thm,
				reflex_have_same_mem_accesses_thm,
				tautology_fun_def,
				have_same_mem_accesses_def,
				errorT_thm,
				SIMP_RULE (srw_ss()) []
					  (SPEC ``27w:bool[5]`` read_write_cpsr_undef_svc_thm),
				write_spsr_und_thm,
				write_reg_und_thm,
				write__pc_und_thm
			       ];
		   val (write_part_thm,_) = prove writing_part
						  ``(assert_mode 27w)`` ``(assert_mode 27w)``
						  uargs pthms;
		   val wp_specl = [``(s2.coprocessors.state.cp15.SCTLR):CP15sctlr``,
				   ``get_pc_value s2``,
				   ``(s2.psrs (0,CPSR)):ARMpsr``,
				   ``get_base_vector_table s2``];
		   val fixed_rp_thm = fixed_undef_svc_exception_rp_thm3
		   val const_comp_rp_thm =  const_comp_take_undef_svc_exception_rp_thm;

	       in
		   prove_take_exception_nav_thm
			   te_body take_undef_instr_exception_def ``27w:bool[5]``
			   fixed_rp_thm  const_comp_rp_thm
			   read_part_thm write_part_thm wp_specl simpr
	       end);


val take_svc_exception_nav_thm =
    store_thm ("take_svc_exception_nav_thm",
	       let
		   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
					``take_svc_exception <|proc:=0|> ``;
		   val (_, a) =  (dest_eq (concl athm))
		   val (_,_,rb)= decompose_term a;
	       in
		   ``preserve_relation_mmu
	               ^rb
	               (assert_mode_no_access_violation 16w )
	               (assert_mode 19w) ^uf1 ^uy1``
	       end
	     ,
	       let
		   val (_,a) =
		       (dest_eq o concl) (REWRITE_CONV [take_svc_exception_def]
						       ``take_svc_exception <|proc:=0|> ``);
		   val (_,_,te_body)= decompose_term a
		   val (lp,rp,_)= decompose_term te_body
		   (*proof of reading part *)
		   val () = global_mode := ``16w:bool[5]``
		   val (read_part_thm,_) =
		       prove lp ``(assert_mode 16w)`` ``(assert_mode 16w)`` uargs pthms;

		   (*proof of writing part *)
		   val (writing_part , simpr) = get_take_undef_svc_simp_pars ``8w:bool[32]``
		   val () = global_mode := ``19w:bool[5]``;
		   val pthms = [trans_have_same_mem_accesses_thm,
				reflex_have_same_mem_accesses_thm,
				tautology_fun_def,
				have_same_mem_accesses_def,
				errorT_thm,
				SIMP_RULE (srw_ss()) []
					  (SPEC ``19w:bool[5]`` read_write_cpsr_undef_svc_thm),
				write_spsr_svc_thm,
				write_reg_svc_thm,
				write__pc_svc_thm
			       ];
		   val (write_part_thm,_) = prove writing_part
						  ``(assert_mode 19w)`` ``(assert_mode 19w)``
						  uargs pthms;
		   val wp_specl = [``(s2.coprocessors.state.cp15.SCTLR):CP15sctlr``,
				   ``get_pc_value s2``,
				   ``(s2.psrs (0,CPSR)):ARMpsr``,
				   ``get_base_vector_table s2``];
		   val fixed_rp_thm = fixed_undef_svc_exception_rp_thm3
		   val const_comp_rp_thm =  const_comp_take_undef_svc_exception_rp_thm;

	       in
		   prove_take_exception_nav_thm
			   te_body take_svc_exception_def ``19w:bool[5]``
			   fixed_rp_thm  const_comp_rp_thm
			   read_part_thm write_part_thm wp_specl simpr
	       end);


(**************************************)
(******** privilaged constranits ******)

fun prove_take_exception_ut_EE_F_flags_thm mode thm te =

    RW_TAC (srw_ss()) []
	   THEN ASSUME_TAC
       (LIST_MP [thm,
		 refl_rel_tautology_fun_thm]
		(SPECL [te,
			``(assert_mode_no_access_violation 16w) ``,
			``(assert_mode ^mode)``,
			uf1, uy1]
		       (INST_TYPE [alpha |-> ``:unit``]
				  downgrade_thm )))
       THEN FULL_SIMP_TAC (bool_ss) [keep_untouched_relation_def]
       THEN PAT_ASSUM ``∀g s s' a.X``
       (fn thm =>
	   ASSUME_SPECL_TAC [``g:bool[32]``,
			     ``s1:arm_state``,
			     ``s1':arm_state``,
			     ``a:unit``]
			    thm)
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def];

val take_undef_instr_exception_ut_EE_F_flags_thm =
store_thm ("take_undef_instr_exception_ut_EE_F_flags_thm",
``! s1 a s1' g  .
    mmu_requirements s1 g ⇒
    assert_mode_no_access_violation 16w  s1 ⇒
    (take_undef_instr_exception <|proc := 0|> s1 = ValueState a s1') ==>
    (((s1'.psrs (0,CPSR)).F = (s1.psrs (0,CPSR)).F) /\
     (s1'.coprocessors.state.cp15=
      s1.coprocessors.state.cp15)
     /\ (s1.information  = s1'.information )
     /\ ((s1.psrs (0,CPSR)).F = (s1'.psrs (0,CPSR)).F))``
,
prove_take_exception_ut_EE_F_flags_thm ``27w:bool[5]``
				       take_undef_instr_exception_nav_thm
				       ``take_undef_instr_exception <|proc:=0|>``
);


val take_svc_exception_ut_EE_F_flags_thm =
store_thm ("take_svc_exception_ut_EE_F_flags_thm",
	   let
	       val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
				    ``take_svc_exception <|proc:=0|> ``;
	       val (_, a) =  (dest_eq (concl athm))
	       val (_,_,rb)= decompose_term a;
	   in
             ``! s1 a s1' g  .
                 mmu_requirements s1 g ⇒
                 assert_mode_no_access_violation 16w  s1 ⇒
                 (^rb s1 = ValueState a s1') ==>
                 (((s1'.psrs (0,CPSR)).F = (s1.psrs (0,CPSR)).F) /\
                  (s1'.coprocessors.state.cp15=
                   s1.coprocessors.state.cp15)
                  /\ (s1.information  = s1'.information )
                  /\ ((s1.psrs (0,CPSR)).F = (s1'.psrs (0,CPSR)).F))``
	   end
,
let val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
			 ``take_svc_exception <|proc:=0|> ``;
    val (_, a) =  (dest_eq (concl athm))
    val (_,_,rb)= decompose_term a
in
    prove_take_exception_ut_EE_F_flags_thm ``19w:bool[5]``
				           take_svc_exception_nav_thm
					   rb
end
	  );



val take_data_abort_exception_ut_EE_F_flags_thm =
store_thm ("take_data_abort_exception_ut_EE_F_flags_thm",
``! s1 a s1' g  .
    mmu_requirements s1 g ⇒
    assert_mode_no_access_violation 16w  s1 ⇒
    (take_data_abort_exception <|proc := 0|> s1 = ValueState a s1') ==>
    (((s1'.psrs (0,CPSR)).F = (s1.psrs (0,CPSR)).F) /\
     (s1'.coprocessors.state.cp15=
      s1.coprocessors.state.cp15)
     /\ (s1.information  = s1'.information )
     /\ ((s1.psrs (0,CPSR)).F = (s1'.psrs (0,CPSR)).F))``
,
prove_take_exception_ut_EE_F_flags_thm ``23w:bool[5]``
				       take_data_abort_exception_nav_thm
				       ``take_data_abort_exception <|proc:=0|>``
);

val take_prefetch_abort_exception_ut_EE_F_flags_thm =
store_thm ("take_prefetch_abort_exception_ut_EE_F_flags_thm",
``! s1 a s1' g  .
    mmu_requirements s1 g ⇒
    assert_mode_no_access_violation 16w  s1 ⇒
    (take_prefetch_abort_exception <|proc := 0|> s1 = ValueState a s1') ==>
    (((s1'.psrs (0,CPSR)).F = (s1.psrs (0,CPSR)).F) /\
     (s1'.coprocessors.state.cp15=
      s1.coprocessors.state.cp15)
     /\ (s1.information  = s1'.information )
     /\ ((s1.psrs (0,CPSR)).F = (s1'.psrs (0,CPSR)).F))``
,
prove_take_exception_ut_EE_F_flags_thm ``23w:bool[5]``
				       take_prefetch_abort_exception_nav_thm
				       ``take_prefetch_abort_exception <|proc:=0|>``
);

val take_irq_exception_ut_EE_F_flags_thm =
store_thm ("take_irq_exception_ut_EE_F_flags_thm",
``! s1 a s1' g  .
    mmu_requirements s1 g ⇒
    assert_mode_no_access_violation 16w  s1 ⇒
    (take_irq_exception <|proc := 0|> s1 = ValueState a s1') ==>
    (((s1'.psrs (0,CPSR)).F = (s1.psrs (0,CPSR)).F) /\
     (s1'.coprocessors.state.cp15=
      s1.coprocessors.state.cp15)
     /\ (s1.information  = s1'.information )
     /\ ((s1.psrs (0,CPSR)).F = (s1'.psrs (0,CPSR)).F))``
,
prove_take_exception_ut_EE_F_flags_thm ``18w:bool[5]``
				       take_irq_exception_nav_thm
				       ``take_irq_exception <|proc:=0|>``
);

fun prove_take_exception_priv_constraints_thm
	cfc_thm
	spc_thm
	ut_EE_F_flags_thm
	spsr_thm
	lr_thm
  =
  let
      val sl = [``s1:arm_state``,``a:unit``,``s1':arm_state``]
  in
      RW_TAC (bool_ss) [priv_mode_constraints_v3_def,priv_mode_constraints_v2a_def,
		        priv_mode_constraints_v2_def,satisfy_priv_constraints_v2_def,
			priv_mode_constraints_v1_def,satisfy_priv_constraints_v2a_def,
			satisfy_priv_constraints_v3_def]
	     THEN FIRST_PROVE
	     [
	      FULL_SIMP_TAC (srw_ss()) [],
	      MP_TAC
		  (SIMP_RULE (srw_ss()) [] (SPECL (sl @ [``g:bool[32]``])
			 ut_EE_F_flags_thm))
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN METIS_TAC [ARM_MODE_def, ARM_READ_CPSR_def,
				  assert_mode_no_access_violation_def]
	    ,
	    MP_TAC (SPECL sl
			  cfc_thm)
		   THEN FULL_SIMP_TAC (srw_ss()) []
	    ,
	    MP_SPECL_TAC sl
			 spc_thm
			 THEN FULL_SIMP_TAC (srw_ss())
			 [ARM_MODE_def,ARM_READ_CPSR_def]
	    ,
	    MP_SPECL_TAC [``s1:arm_state``,``s1':arm_state``,``a:unit``]
			 (SIMP_RULE (bool_ss) [satisfy_SPSR_constraints_def] spsr_thm)
			 THEN  (TRY (Q.UNABBREV_TAC `spsr`))
			 THEN FULL_SIMP_TAC (srw_ss()) [get_spsr_by_mode_def,
							ARM_MODE_def,ARM_READ_CPSR_def]
	    ,
	    MP_SPECL_TAC [``s1:arm_state``,``s1':arm_state``,``a:unit``]
			 (SIMP_RULE (bool_ss) [satisfy_LR_constraints_def] lr_thm)
			 THEN FULL_SIMP_TAC (srw_ss()) [get_lr_by_mode_def,
							ARM_MODE_def,ARM_READ_CPSR_def]
	     ]
  end;

val take_undef_instr_exception_priv_constraints_thm =
store_thm ("take_undef_instr_exception_priv_constraints_thm",
`` satisfy_priv_constraints_v3 (take_undef_instr_exception <|proc := 0|>)
	  16w 27w ``,
	   prove_take_exception_priv_constraints_thm
	       take_undef_instr_exception_cfc_thm
	       take_undef_instr_exception_spc_thm
	       take_undef_instr_exception_ut_EE_F_flags_thm
	       take_undef_instr_exception_spsr_thm
	       take_undef_instr_exception_LR_thm
	  );


val take_data_abort_exception_priv_constraints_thm =
store_thm ("take_data_abort_exception_priv_constraints_thm",
`` satisfy_priv_constraints_v3 (take_data_abort_exception <|proc := 0|>)
	  16w 23w ``,
	   prove_take_exception_priv_constraints_thm
	       take_data_abort_exception_cfc_thm
	       take_data_abort_exception_spc_thm
	       take_data_abort_exception_ut_EE_F_flags_thm
	       take_data_abort_exception_spsr_thm
	       take_data_abort_exception_LR_thm
	  );

val take_prefetch_abort_exception_priv_constraints_thm =
store_thm ("take_prefetch_abort_exception_priv_constraints_thm",
`` satisfy_priv_constraints_v3 (take_prefetch_abort_exception <|proc := 0|>)
	  16w 23w ``,
	   prove_take_exception_priv_constraints_thm
	       take_prefetch_abort_exception_cfc_thm
	       take_prefetch_abort_exception_spc_thm
	       take_prefetch_abort_exception_ut_EE_F_flags_thm
	       take_prefetch_abort_exception_spsr_thm
	       take_prefetch_abort_exception_LR_thm
	  );

val take_irq_exception_priv_constraints_thm =
store_thm ("take_irq_exception_priv_constraints_thm",
`` satisfy_priv_constraints_v3 (take_irq_exception <|proc := 0|>)
	  16w 18w ``,
	   prove_take_exception_priv_constraints_thm
	       take_irq_exception_cfc_thm
	       take_irq_exception_spc_thm
	       take_irq_exception_ut_EE_F_flags_thm
	       take_irq_exception_spsr_thm
	       take_irq_exception_LR_thm
	  );

val take_svc_exception_priv_constraints_thm =
store_thm ("take_svc_exception_priv_constraints_thm",
	   let
	       val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
				    ``take_svc_exception <|proc:=0|> ``
	       val (_, a) =  (dest_eq (concl athm))
	       val (_,_,rb)= decompose_term a
	   in
	       `` satisfy_priv_constraints_v2 ^rb 16w 19w ``
	   end
	 ,
	 prove_take_exception_priv_constraints_thm
	     take_svc_exception_cfc_thm
	     take_svc_exception_spc_thm
	     take_svc_exception_ut_EE_F_flags_thm
	     take_svc_exception_spsr_thm
	     take_svc_exception_LR_thm
	  );


(*******************************************************)

val take_undef_instr_exception_priv_nav_thm =
    store_thm ("take_undef_instr_exception_priv_nav_thm",
 `` preserve_relation_mmu
	      (take_undef_instr_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 27w) priv_mode_constraints_v3 priv_mode_similar``
,
MP_TAC take_undef_instr_exception_priv_mode_similar_thm
THEN MP_TAC take_undef_instr_exception_priv_constraints_thm
THEN MP_TAC ( take_undef_instr_exception_nav_thm)
THEN METIS_TAC [preserve_relation_in_priv_mode_v3_thm]);


val take_data_abort_exception_priv_nav_thm =
    store_thm ("take_data_abort_exception_priv_nav_thm"
, `` preserve_relation_mmu
	      (take_data_abort_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 23w) priv_mode_constraints_v3 priv_mode_similar``
,
     MP_TAC take_data_abort_exception_priv_mode_similar_thm
THEN MP_TAC take_data_abort_exception_priv_constraints_thm
THEN MP_TAC ( take_data_abort_exception_nav_thm)
THEN METIS_TAC [preserve_relation_in_priv_mode_v3_thm]);

val take_prefetch_abort_exception_priv_nav_thm =
    store_thm ("take_prefetch_abort_exception_priv_nav_thm"
, `` preserve_relation_mmu
	      (take_prefetch_abort_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 23w) priv_mode_constraints_v3 priv_mode_similar``
,
     MP_TAC take_prefetch_abort_exception_priv_mode_similar_thm
THEN MP_TAC take_prefetch_abort_exception_priv_constraints_thm
THEN MP_TAC take_prefetch_abort_exception_nav_thm
THEN METIS_TAC [preserve_relation_in_priv_mode_v3_thm]);

val take_irq_exception_priv_nav_thm =
    store_thm ("take_irq_exception_priv_nav_thm"
, `` preserve_relation_mmu
	      (take_irq_exception <|proc := 0|> )
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 18w) priv_mode_constraints_v3 priv_mode_similar``
,
     MP_TAC take_irq_exception_priv_mode_similar_thm
THEN MP_TAC take_irq_exception_priv_constraints_thm
THEN MP_TAC ( take_irq_exception_nav_thm)
THEN METIS_TAC [preserve_relation_in_priv_mode_v3_thm]);


val take_svc_exception_priv_nav_thm =
    store_thm ("take_svc_exception_priv_nav_thm"
,
 let
     val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
			  ``take_svc_exception <|proc:=0|> ``;
     val (_, a) =  (dest_eq (concl athm))
     val (_,_,rb)= decompose_term a;
 in
 `` preserve_relation_mmu
	      ^rb
	      (assert_mode_no_access_violation 16w )
	      (assert_mode 19w) priv_mode_constraints_v2 priv_mode_similar``
 end
,
     MP_TAC take_svc_exception_priv_mode_similar_thm
	    THEN MP_TAC take_svc_exception_priv_constraints_thm
	    THEN MP_TAC take_svc_exception_nav_thm
	    THEN METIS_TAC [preserve_relation_in_priv_mode_v2_thm]);


val take_undef_instr_exception_av_thm =
    store_thm ("take_undef_instr_exception_av_thm",
``preserve_relation_mmu
	      (take_undef_instr_exception <|proc := 0|>)
	      (assert_mode_access_violation 16w)
	      (assert_mode_access_violation 16w)
	      priv_mode_constraints_v3 priv_mode_similar``
	     ,
	     let val (_,take_undef_exception_body) =
		     (dest_eq o concl) (REWRITE_CONV [take_undef_instr_exception_def]
						     ``take_undef_instr_exception <|proc:=0|> ``);
		 val (al,ar,arb)= decompose_term take_undef_exception_body;
		 val al_type = get_monad_type (type_of (al));
		 val () = global_mode := ``16w:bool[5]``;
		 val pthms1 = [trans_tautology_fun_thm,
			       reflex_tautology_fun_thm,
			       tautology_fun_def,
			       tautology_fun_def,
			       errorT_thm
			      ];
		 val uargs = [``tautology_fun``,``tautology_fun``,
			      ``27w:bool[5]``,``_thm1``];
		 val (read_part_thm,_) = prove al ``(assert_mode 16w)``
					       ``(assert_mode 16w)`` uargs pthms1;
	     in
		 RW_TAC (srw_ss()) [take_undef_instr_exception_def]
			THEN MP_TAC const_comp_take_undef_svc_exception_rp_thm
			THEN MP_TAC (MP (SPEC al (INST_TYPE
						      [alpha |-> al_type]
						      user_pr_taut_imp_priv_pr_thm))
					read_part_thm )
			THEN METIS_TAC [access_violation_implies_no_mode_changing_thm]
	     end);

val take_svc_exception_av_thm =
    store_thm ("take_svc_exception_av_thm",
	       let
		   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
					``take_svc_exception <|proc:=0|> ``
		   val (_, a) =  (dest_eq (concl athm))
		   val (_,_,rb)= decompose_term a;
	       in
           ``preserve_relation_mmu
	        ^rb
              (assert_mode_access_violation 16w)
	      (assert_mode_access_violation 16w)
	      priv_mode_constraints_v2 priv_mode_similar``
	       end
	     ,
	     let
		 val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
			  ``take_svc_exception <|proc:=0|> ``
		 val (_, a) =  (dest_eq (concl athm))
		 val (_,_,body)= decompose_term a
		 val (al,_,body)= decompose_term body;

		 val al_type = get_monad_type (type_of (al));
		 val () = global_mode := ``16w:bool[5]``;
		 val pthms1 = [trans_tautology_fun_thm,
			       reflex_tautology_fun_thm,
			       tautology_fun_def,
			       tautology_fun_def,
			       errorT_thm
			      ];
		 val uargs = [``tautology_fun``,``tautology_fun``,
			      ``19w:bool[5]``,``_thm1``];
		 val (read_part_thm,_) = prove al ``(assert_mode 16w)``
					       ``(assert_mode 16w)`` uargs pthms1;
	     in
		 RW_TAC (srw_ss()) [take_svc_exception_def]
			THEN MP_TAC const_comp_take_undef_svc_exception_rp_thm
			THEN MP_TAC (MP (SPEC al (INST_TYPE
						      [alpha |-> al_type]
						      user_pr_taut_imp_priv_pr_thm))
					read_part_thm )
			THEN METIS_TAC [access_violation_implies_no_mode_changing_v1_thm]
	     end);


val take_data_abort_exception_av_thm =
    store_thm ("take_data_abort_exception_av_thm",
``preserve_relation_mmu
	      (take_data_abort_exception <|proc := 0|>)
	      (assert_mode_access_violation 16w)
	      (assert_mode_access_violation 16w)
	      priv_mode_constraints_v3 priv_mode_similar``
	     ,
	     let val (_,te_body) =
		     (dest_eq o concl) (REWRITE_CONV [take_data_abort_exception_def]
						     ``take_data_abort_exception <|proc:=0|> ``);
		 val (al,ar,arb)= decompose_term te_body;
		 val al_type = get_monad_type (type_of (al));
		 val () = global_mode := ``16w:bool[5]``;
		 val pthms1 = [trans_tautology_fun_thm,
			       reflex_tautology_fun_thm,
			       tautology_fun_def,
			       tautology_fun_def,
			       errorT_thm
			      ];
		 val uargs = [``tautology_fun``,``tautology_fun``,
			      ``27w:bool[5]``,``_thm1``];
		 val (read_part_thm,_) = prove al ``(assert_mode 16w)``
					       ``(assert_mode 16w)`` uargs pthms1;
	     in
		 RW_TAC (srw_ss()) [take_data_abort_exception_def]
			THEN MP_TAC const_comp_take_abort_irq_exception_rp_thm
			THEN MP_TAC (MP (SPEC al (INST_TYPE
						      [alpha |-> al_type]
						      user_pr_taut_imp_priv_pr_thm))
					read_part_thm )
			THEN METIS_TAC [access_violation_implies_no_mode_changing_thm]
	     end);

val take_prefetch_abort_exception_av_thm =
    store_thm ("take_prefetch_abort_exception_av_thm",
``preserve_relation_mmu
	      (take_prefetch_abort_exception <|proc := 0|>)
	      (assert_mode_access_violation 16w)
	      (assert_mode_access_violation 16w)
	      priv_mode_constraints_v3 priv_mode_similar``
	     ,
	     let val (_,te_body) =
		     (dest_eq o concl) (REWRITE_CONV [take_prefetch_abort_exception_def]
						     ``take_prefetch_abort_exception <|proc:=0|> ``);
		 val (al,ar,arb)= decompose_term te_body;
		 val al_type = get_monad_type (type_of (al));
		 val () = global_mode := ``16w:bool[5]``;
		 val pthms1 = [trans_tautology_fun_thm,
			       reflex_tautology_fun_thm,
			       tautology_fun_def,
			       tautology_fun_def,
			       errorT_thm
			      ];
		 val uargs = [``tautology_fun``,``tautology_fun``,
			      ``27w:bool[5]``,``_thm1``];
		 val (read_part_thm,_) = prove al ``(assert_mode 16w)``
					       ``(assert_mode 16w)`` uargs pthms1;
	     in
		 RW_TAC (srw_ss()) [take_prefetch_abort_exception_def]
			THEN MP_TAC const_comp_take_abort_irq_exception_rp_thm
			THEN MP_TAC (MP (SPEC al (INST_TYPE
						      [alpha |-> al_type]
						      user_pr_taut_imp_priv_pr_thm))
					read_part_thm )
			THEN METIS_TAC [access_violation_implies_no_mode_changing_thm]
	     end);


val take_irq_exception_av_thm =
    store_thm ("take_irq_exception_av_thm",
``preserve_relation_mmu
	      (take_irq_exception <|proc := 0|>)
	      (assert_mode_access_violation 16w)
	      (assert_mode_access_violation 16w)
	      priv_mode_constraints_v3 priv_mode_similar``
	     ,
	     let val (_,te_body) =
		     (dest_eq o concl) (REWRITE_CONV [take_irq_exception_def]
						     ``take_irq_exception <|proc:=0|> ``);
		 val (al,ar,arb)= decompose_term te_body;
		 val al_type = get_monad_type (type_of (al));
		 val () = global_mode := ``16w:bool[5]``;
		 val pthms1 = [trans_tautology_fun_thm,
			       reflex_tautology_fun_thm,
			       tautology_fun_def,
			       tautology_fun_def,
			       errorT_thm
			      ];
		 val uargs = [``tautology_fun``,``tautology_fun``,
			      ``27w:bool[5]``,``_thm1``];
		 val (read_part_thm,_) = prove al ``(assert_mode 16w)``
					       ``(assert_mode 16w)`` uargs pthms1;
	     in
		 RW_TAC (srw_ss()) [take_irq_exception_def]
			THEN MP_TAC const_comp_take_abort_irq_exception_rp_thm
			THEN MP_TAC (MP (SPEC al (INST_TYPE
						      [alpha |-> al_type]
						      user_pr_taut_imp_priv_pr_thm))
					read_part_thm )
			THEN METIS_TAC [access_violation_implies_no_mode_changing_thm]
	     end);


val take_undef_instr_exception_thm =
store_thm ("take_undef_instr_exception_thm",
``preserve_relation_mmu
	      (take_undef_instr_exception <|proc := 0|> )
	      (assert_mode 16w )
	      (comb_mode 16w 27w )
	      priv_mode_constraints_v3 priv_mode_similar``
,
ASSUME_TAC  take_undef_instr_exception_av_thm
THEN ASSUME_TAC	 take_undef_instr_exception_priv_nav_thm
THEN RW_TAC (srw_ss()) [deduce_pr_from_pr_av_and_pr_no_av_thm]);



val take_data_abort_exception_thm =
store_thm ("take_data_abort_exception_thm",
``preserve_relation_mmu
	      (take_data_abort_exception <|proc := 0|> )
	      (assert_mode 16w )
	      (comb_mode 16w 23w )
	      priv_mode_constraints_v3 priv_mode_similar``
,
ASSUME_TAC  take_data_abort_exception_av_thm
THEN ASSUME_TAC	 take_data_abort_exception_priv_nav_thm
THEN RW_TAC (srw_ss()) [deduce_pr_from_pr_av_and_pr_no_av_thm]);


val take_prefetch_abort_exception_thm =
store_thm ("take_prefetch_abort_exception_thm",
``preserve_relation_mmu
	      (take_prefetch_abort_exception <|proc := 0|> )
	      (assert_mode 16w )
	      (comb_mode 16w 23w )
	      priv_mode_constraints_v3 priv_mode_similar``
,
ASSUME_TAC  take_prefetch_abort_exception_av_thm
THEN ASSUME_TAC	 take_prefetch_abort_exception_priv_nav_thm
THEN RW_TAC (srw_ss()) [deduce_pr_from_pr_av_and_pr_no_av_thm]);

val take_irq_exception_thm =
store_thm ("take_irq_exception_thm",
``preserve_relation_mmu
	      (take_irq_exception <|proc := 0|> )
	      (assert_mode 16w )
	      (comb_mode 16w 18w )
	      priv_mode_constraints_v3 priv_mode_similar``
,
ASSUME_TAC  take_irq_exception_av_thm
THEN ASSUME_TAC	 take_irq_exception_priv_nav_thm
THEN RW_TAC (srw_ss()) [deduce_pr_from_pr_av_and_pr_no_av_thm]);

val take_svc_exception_part2_def =
Define `take_svc_exception_part2 ii =
(read_reg ii 15w ||| exc_vector_base ii ||| read_cpsr ii
           ||| read_scr ii ||| read_sctlr ii) >>=
        (λ(pc,ExcVectorBase,cpsr,scr,sctlr).
           (condT (cpsr.M = 22w) (write_scr ii (scr with NS := F))
              ||| write_cpsr ii (cpsr with M := 19w)) >>=
           (λ(u1,u2).
              (write_spsr ii cpsr
                 ||| write_reg ii 14w
                       (if cpsr.T then pc − 2w else pc − 4w)
                 ||| read_cpsr ii >>=
                     (λcpsr.
                        write_cpsr ii
                          (cpsr with
                           <|I := T; IT := 0w; J := F; T := sctlr.TE;
                             E := sctlr.EE|>))
                 ||| branch_to ii (ExcVectorBase + 8w)) >>=
              (λ(u1,u2,u3,u4). constT ())))`;

val take_svc_exception_part2_thm =
store_thm ("take_svc_exception_part2_thm",
``preserve_relation_mmu  (take_svc_exception_part2 <|proc:=0|>)  (assert_mode 16w )
	      (comb_mode 16w 19w )
	      priv_mode_constraints_v2 priv_mode_similar``
	 ,
	 FULL_SIMP_TAC (bool_ss) [take_svc_exception_part2_def]
		       THEN ASSUME_TAC  take_svc_exception_av_thm
		       THEN ASSUME_TAC	 take_svc_exception_priv_nav_thm
		       THEN RW_TAC (srw_ss()) [deduce_pr_from_pr_av_and_pr_no_av_thm]
	  )

(** this axiom is proven in user_lemma_primitive_operationsTheory under the name IT_advance_thm*)
val IT_advance_thm1 =
    save_thm("IT_advance_thm1",
	     new_axiom("IT_advance_thmX", ``preserve_relation_mmu (IT_advance <|proc:=0|>)
		      (assert_mode 16w) (assert_mode  16w) priv_mode_constraints priv_mode_similar``));

val priv_mode_constraints_def = priv_mode_constraints_v1_def;

val take_svc_exception_helper_thm = store_thm("take_svc_exception_helper_thm",
``! Z A .
preserve_relation_mmu (A)
     (assert_mode 16w )
	      (comb_mode 16w 19w )
	      priv_mode_constraints_v2 priv_mode_similar ==>
preserve_relation_mmu (Z)
     (assert_mode 16w )
     (assert_mode 16w )
	      priv_mode_constraints_v1 priv_mode_similar ==>
(! state0 state1 a. (Z state0 = ValueState a state1) ==>
   (~access_violation state1) ==>(((get_pc_value state1) = (get_pc_value state0)) /\
 ((state1.psrs(0,CPSR)) =
			     if (((ARMarch2num state0.information.arch = 6) ∨
				  version_number state0.information.arch ≥ 7) /\
				 (((state0.psrs (0,CPSR)).IT = 0w) ∨ (state0.psrs (0,CPSR)).T))
			     then
				 (state0.psrs(0,CPSR) with IT := ITAdvance ((state0.psrs(0,CPSR)).IT))
			     else
				 (state0.psrs(0,CPSR))))) ==>
preserve_relation_mmu (Z >>= (\x.A))
     (assert_mode 16w )
	      (comb_mode 16w 19w )
	      priv_mode_constraints_v2a priv_mode_similar``
,
	      RW_TAC (bool_ss) [preserve_relation_mmu_def,seqT_def]
	      THEN Cases_on ` Z s1`
	      THEN Cases_on ` Z s2`
	      THEN RW_TAC (srw_ss()) [seqT_def]
	      THEN PAT_ASSUM ``∀g:word32 s1 s2.X`` (fn thm =>
						       ASSUME_SPECL_TAC
							   [``g:bool[32]``,``s1:arm_state``,
							    ``s2:arm_state``] thm)

	      THEN UNDISCH_ALL_TAC
	      THEN RW_TAC (bool_ss) []
	      THEN
	      FIRST_PROVE
	      [
	       FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def,priv_mode_constraints_v2_def,assert_mode_def,comb_mode_def]
	     ,
	     (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
		 THEN FULL_SIMP_TAC (srw_ss()) []
	     ,
	     ASSUME_TAC  seqT_access_violation_thm
			 THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
			 THEN PAT_ASSUM ``∀g:word32 s1 s2.X`` (fn thm =>
						 ASSUME_SPECL_TAC
						     [``g:bool[32]``,``b:arm_state``,
						      ``b':arm_state``] thm)
		       THEN IMP_RES_TAC untouched_mmu_setup_lem
		       THEN UNDISCH_ALL_TAC
		       THEN RW_TAC (srw_ss()) []
		       THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def]
		       THEN REPEAT STRIP_TAC
		       THEN FIRST_PROVE
		       [
			IMP_RES_TAC untouched_trans
				    THEN FULL_SIMP_TAC (srw_ss()) []
		      ,
		      FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def,
						priv_mode_constraints_v2_def,
						assert_mode_def,comb_mode_def]
				    THEN REPEAT STRIP_TAC
				    THEN FIRST_PROVE
				    [
				     FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def,priv_mode_constraints_def,
							       priv_mode_constraints_v2_def,assert_mode_def,
							       comb_mode_def,LET_DEF,ARM_MODE_def,
							       ARM_READ_CPSR_def]
				   ,
				   IMP_RES_TAC similar_states_have_same_mode_thm
					       THEN FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def,ARM_READ_CPSR_def]
				   ,

				   PAT_ASSUM ``∀ s1:arm_state s2.X`` (fn thm =>
									 ASSUME_SPECL_TAC
									     [``s1:arm_state``,
									      ``b:arm_state``, ``a:'a``] thm
									     THEN						 ASSUME_SPECL_TAC
									     [``s2:arm_state``,
									      ``b':arm_state``, ``a:'a``] thm)

					     THEN UNDISCH_ALL_TAC
					     THEN RW_TAC (srw_ss()) []
					     THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def]
				   ,

				   IMP_RES_TAC (SIMP_RULE bool_ss [trans_fun_def] trans_priv_mode_constraints_thm)
				    ]
		       ]
	      ]
)


val IT_advance_svc_spsr_thm =
store_thm ("IT_advance_svc_spsr_thm",
``(! state0 state1 a. (IT_advance <|proc := 0|> state0 = ValueState a state1) ==>
				(~access_violation state1) ==>
(((get_pc_value state1) = (get_pc_value state0)) /\
 ((state1.psrs(0,CPSR)) =
			     if (((ARMarch2num state0.information.arch = 6) ∨
				  version_number state0.information.arch ≥ 7) /\
				 (((state0.psrs (0,CPSR)).IT = 0w) ∨ (state0.psrs (0,CPSR)).T))
			     then
				 (state0.psrs(0,CPSR) with IT := ITAdvance ((state0.psrs(0,CPSR)).IT))
			     else
				 (state0.psrs(0,CPSR)))))``
	 ,
	 RW_TAC (srw_ss()) []
		THEN PAT_ASSUM ``IT_advance <|proc := 0|> state0 = ValueState a state1`` (fn thm => ASSUME_TAC (EVAL_RULE thm))
		THEN Cases_on `access_violation state0`
		THEN FIRST_PROVE
		[
		 FULL_SIMP_TAC (srw_ss()) []
	       ,
	       Cases_on `(ARMarch2num state0.information.arch = 6) ∨
		version_number state0.information.arch ≥ 7`
		       THEN
		       Cases_on `((state0.psrs (0,CPSR)).IT = 0w) ∨ (state0.psrs (0,CPSR)).T`
		       THEN NTAC 2 (UNDISCH_ALL_TAC
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN RW_TAC (srw_ss()) []
				       THEN EVAL_TAC
				       THEN FULL_SIMP_TAC (srw_ss()) [])
		]
	  );

val take_svc_exception_thm =
    store_thm ("take_svc_exception_thm",
	       ``preserve_relation_mmu (take_svc_exception <|proc := 0|>)
	      (assert_mode 16w )
	      (comb_mode 16w 19w )
	      priv_mode_constraints_v2a priv_mode_similar ``,

	       FULL_SIMP_TAC (srw_ss()) [take_svc_exception_def]
			     THEN ASSUME_TAC take_svc_exception_part2_thm
			     THEN ASSUME_TAC  IT_advance_thm1
			     THEN ASSUME_TAC  IT_advance_svc_spsr_thm
			     THEN IMP_RES_TAC (INST_TYPE [beta |-> ``:unit`` ] take_svc_exception_helper_thm)
			     THEN FULL_SIMP_TAC (srw_ss()) [take_svc_exception_part2_def]
	      );

val _ = export_theory();
