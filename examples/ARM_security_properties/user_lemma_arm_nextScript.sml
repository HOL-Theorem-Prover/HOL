(*  properties of the next function *)
(*  Author: Oliver Schwarz          *)

open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory;
open tacticsLib ARM_proverLib ARM_prover_toolsLib;
open user_lemma_basicsTheory user_lemma_primitive_operationsTheory;
open user_lemma_instructionsTheory;
open wordsTheory wordsLib;

val _ =  new_theory("user_lemma_arm_next");

val _ = temp_overload_on ("return", ``constT``);
val _ = diminish_srw_ss ["one"]
val _ = augment_srw_ss [rewrites [oneTheory.FORALL_ONE]]


(************************************************************)
(*******************  A. Fetch Phase   **********************)
(************************************************************)



val no_armv4_axiom = new_axiom("no_armv4_axiom", ``!s. ((ARMinfo_arch o arm_state_information) s) <> ARMv4``);


val fetch_instruction_thm = prove_and_save_s (``fetch_instruction <|proc:=0|>
                                       (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))
                                       (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))``,
                                       "fetch_instruction_thm");


val instr_set_and_T_flag_thm = store_thm(
    "instr_set_and_T_flag_thm",
    ``!s.  (~access_violation s) ==> (((s.psrs(0,CPSR)).T) ==> ((actual_instr_set <|proc:=0|> s = ValueState InstrSet_Thumb s) \/ (actual_instr_set <|proc:=0|> s = ValueState InstrSet_ThumbEE s))) /\ ((~((s.psrs(0,CPSR)).T)) ==> ((actual_instr_set <|proc:=0|> s = ValueState InstrSet_ARM s) \/ (actual_instr_set <|proc:=0|> s = ValueState InstrSet_Jazelle s)))``,
    STRIP_TAC
      THEN MP_TAC (SPEC ``s:arm_state`` no_armv4_axiom)
      THEN EVAL_TAC
      THEN REPEAT STRIP_TAC
      THEN RW_TAC (srw_ss()) []
      THEN (REPEAT (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN EVAL_TAC)));

val align_248 =  numLib.REDUCE_RULE (Drule.LIST_CONJ (List.map (fn t => Q.SPEC t align_slice) [`1`,`2`,`3`]));



val align_lem = store_thm(
    "align_lem",
  ``(!b:word32. align(b,2) + (0 -- 0) b = b) /\
   (!b:word32. align(b,4) + (1 -- 0) b = b) /\
   (!b:word32. align(b,8) + (2 -- 0) b = b)``,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);



val read_memA4_av_lem = store_thm(
    "read_memA4_av_lem",
    ``!pc. (mmu_requirements s g) ==>
       ((read_memA <|proc:=0|> (pc, 4)) s = ValueState x t) ==>
       (    ¬permitted_byte_pure (pc) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(pc,4)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 2w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 3w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory)
       ==> (access_violation t)``,
    RW_TAC (srw_ss()) []
       THENL (map (fn byte => (`!other. access_violation (s with accesses updated_by CONS (MEM_READ (^byte)) o other)` by (METIS_TAC [malicious_read2, access_violation_req, mmu_requirement_accesses_update_lem2]))) [``pc:word32``, ``(align(pc,4)):word32``, ``(align(pc,4) + 1w):word32``, ``(align(pc,4) +2w):word32``, ``(align(pc,4) +3w):word32``])
       THEN UNDISCH_TAC `` read_memA <|proc := 0|> (pc,4) s = ValueState x t``
       THEN EVAL_TAC
       THEN (REPEAT (CHANGED_TAC ((TRY (UNDISCH_MATCH_TAC ``X = ValueState x t``)) THEN RW_TAC (srw_ss()) [])))
       THEN FIRST [MP_TAC (blastLib.BBLAST_PROVE ``(((1 -- 0) (pc:word32)) = 0w) \/ (((1 -- 0) (pc:word32)) = 1w) \/ (((1 -- 0) (pc:word32)) = 2w) \/ (((1 -- 0) (pc:word32)) = 3w)``)
                                THEN RW_TAC (srw_ss()) []
                                THEN CCONTR_TAC
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN ASSUME_TAC (SPEC ``pc:word32`` (CONJUNCT1 (CONJUNCT2 align_lem)))
                                THEN UNDISCH_ALL_TAC
                                THEN RW_TAC (srw_ss()) []
                                THEN CCONTR_TAC
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN UNDISCH_ALL_TAC
                                THEN RW_TAC (srw_ss()) []
                                THEN FULL_SIMP_TAC (srw_ss()) [aligned_def, align_def]
                                THEN NO_TAC,
		    FULL_SIMP_TAC (srw_ss()) [aligned_def]
                                THEN METIS_TAC [malicious_read, access_violation_req, mmu_requirement_accesses_update_lem]]);


val read_memA2_av_lem = store_thm(
    "read_memA2_av_lem",
    ``!pc. (mmu_requirements s g) ==>
       ((read_memA <|proc:=0|> (pc, 2)) s = ValueState x t) ==>
       (    ¬permitted_byte_pure (pc) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(pc,2)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,2) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory)
       ==> (access_violation t)``,
    RW_TAC (srw_ss()) []
       THENL (map (fn byte => (`!other. access_violation (s with accesses updated_by CONS (MEM_READ (^byte)) o other)` by (METIS_TAC [malicious_read2, access_violation_req, mmu_requirement_accesses_update_lem2]))) [``pc:word32``, ``(align(pc,2)):word32``, ``(align(pc,2) + 1w):word32``])
       THEN UNDISCH_TAC `` read_memA <|proc := 0|> (pc,2) s = ValueState x t``
       THEN EVAL_TAC
       THEN (REPEAT (CHANGED_TAC ((TRY (UNDISCH_MATCH_TAC ``X = ValueState x t``)) THEN RW_TAC (srw_ss()) [])))
       THEN FIRST [ MP_TAC (blastLib.BBLAST_PROVE ``(((0 -- 0) (pc:word32)) = 0w) \/ (((0 -- 0) (pc:word32)) = 1w)``)
                       THEN RW_TAC (srw_ss()) []
		       THEN CCONTR_TAC
		       THEN FULL_SIMP_TAC (srw_ss()) []
		       THEN ASSUME_TAC (SPEC ``pc:word32`` (CONJUNCT1 (align_lem)))
		       THEN UNDISCH_ALL_TAC
		       THEN RW_TAC (srw_ss()) []
		       THEN CCONTR_TAC
		       THEN FULL_SIMP_TAC (srw_ss()) []
		       THEN UNDISCH_ALL_TAC
		       THEN RW_TAC (srw_ss()) []
		       THEN FULL_SIMP_TAC (srw_ss()) [aligned_def, align_def]
		       THEN NO_TAC,
                    FULL_SIMP_TAC (srw_ss()) [aligned_def]
                       THEN METIS_TAC [malicious_read, access_violation_req, mmu_requirement_accesses_update_lem]]);


val fetch_arm_av_lem = store_thm(
    "fetch_arm_av_lem",
    `` (mmu_requirements s g) ==>
       (    ¬permitted_byte_pure (s.registers (0,RName_PC)) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(s.registers (0,RName_PC),4)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 2w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 3w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory) ==>
       (((fetch_arm <|proc:=0|> (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))) s) = ValueState x t)
       ==> (access_violation t)``,
    NTAC 2 DISCH_TAC
      THEN PROTECTED_OR_RW_TAC [armTheory.fetch_arm_def, read_pc_def, readT_def, seqT_def, parT_def, arch_version_def, read__reg_def, read_arch_def, constT_def] THEN PROTECTED_OR_RW_TAC []
      THEN Cases_on `read_memA <|proc := 0|> (s.registers (0,RName_PC),4) s` THEN PROTECTED_OR_SIMP_TAC []
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [read_memA4_av_lem] THEN METIS_TAC [read_memA4_av_lem] );


val fetch_thumb_av_lem = store_thm(
    "fetch_thumb_av_lem",
    `` (mmu_requirements s g) ==>
       (    ¬permitted_byte_pure (s.registers (0,RName_PC)) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(s.registers (0,RName_PC),2)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),2) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2
						      s.coprocessors.state.cp15.C3 F s.memory) ==>
       (((fetch_thumb <|proc:=0|> bEE (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))) s) = ValueState x t)
       ==> (access_violation t)``,
      NTAC 2 DISCH_TAC
         THEN PROTECTED_OR_RW_TAC [armTheory.fetch_thumb_def, read_pc_def, readT_def, seqT_def, parT_def, arch_version_def, read__reg_def, read_arch_def, constT_def, read_cpsr_def, read__psr_def] THEN PROTECTED_OR_RW_TAC []
         THEN Cases_on `read_memA <|proc := 0|> (s.registers (0,RName_PC),2) s` THEN PROTECTED_OR_SIMP_TAC []
         THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [read_memA2_av_lem] THEN  METIS_TAC [read_memA2_av_lem]);




val fetch_instr_av_lem = store_thm(
    "fetch_instr_av_lem",
    ``(mmu_requirements s g) ==>
      (~aligned_word_readable s ((s.psrs (0,CPSR)).T) (s.registers (0,RName_PC))) ==>
      ((fetch_instruction <|proc:=0|> (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))
                                       (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d))) s) = ValueState x t)
      ==> (access_violation t)``,
    Q.ABBREV_TAC `readword = (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))`
       THEN Q.ABBREV_TAC `readhalfword = (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))`
       THEN RW_TAC (srw_ss()) [armTheory.fetch_instruction_def, seqT_def, aligned_word_readable_def]
       THENL [(Cases_on `(s.psrs (0,CPSR)).T`), ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC]
       THEN (Cases_on `access_violation s`
              THENL [FULL_SIMP_TAC (srw_ss()) [armTheory.actual_instr_set_def, read_arch_def, seqT_def, readT_def]
                       THEN METIS_TAC [],
                    IMP_RES_TAC instr_set_and_T_flag_thm THEN FULL_SIMP_TAC (srw_ss()) [errorT_def]
                       THEN FIRST [Q.UNABBREV_TAC `readhalfword`
                                      THEN IMP_RES_TAC fetch_thumb_av_lem
                                      THEN NO_TAC,
                                   Q.UNABBREV_TAC `readword`
                                      THEN IMP_RES_TAC fetch_arm_av_lem]]));


(************************************************************)
(******************   B. mmu_arm_next   *********************)
(************************************************************)

(**************************************)
(****    minor state updates     ******)
(**************************************)

(* empty access list *)

val empty_accesses_av_lem = store_thm(
    "empty_accesses_av_lem",
    ``~(access_violation (s with accesses := []))``,
    ASSUME_TAC (SPEC ``(s with accesses := [])`` (GEN_ALL empty_accesses_full_lem))
      THEN ASSUME_TAC (SPECL [``(s with accesses := [])``, ``T``, ``F``, ``ARB:word32``] access_violation_axiom)
      THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_requirements_lem = store_thm(
    "empty_accesses_requirements_lem",
    ``(mmu_requirements (s with accesses := []) g) = (mmu_requirements s g)``,
    RW_TAC (srw_ss()) [mmu_requirements_def]);

val empty_accesses_aligned_word_readable_lem = store_thm(
    "empty_accesses_aligned_word_readable_lem",
    ``(aligned_word_readable (s with accesses := []) ist g) = (aligned_word_readable s ist g)``,
    RW_TAC (srw_ss()) [aligned_word_readable_def]);

val empty_accesses_similar_lem = store_thm(
    "empty_accesses_similar_lem",
    `` (similar g s1 s2) ==> (similar g (s1 with accesses := []) (s2 with accesses := []))``,
    RW_TAC (srw_ss()) [similar_def, equal_user_register_def] THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_full_lem, access_violation_axiom]);

val empty_accesses_priv_mode_similar_lem = store_thm(
    "empty_accesses_priv_mode_similar_lem",
    ``(priv_mode_similar g (s1 with accesses := []) (s2 with accesses := [])) = (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def, LET_DEF, ARM_MODE_def, ARM_READ_CPSR_def]);

val empty_accesses_mode_lem = store_thm(
    "empty_accesses_mode_lem",
    ``(ARM_MODE (s with accesses := [])) = (ARM_MODE s)``,
    RW_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);

val empty_accesses_untouched_lem = store_thm(
    "empty_accesses_untouched_lem",
    ``((untouched g (s with accesses := []) t) = (untouched g s t)) /\ ((untouched g s (t with accesses := [])) = (untouched g s t)) ``,
 STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF, empty_accesses_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_strict_unt_lem = store_thm(
    "empty_accesses_strict_unt_lem",
    ``((strict_unt g (s with accesses := []) t) = (strict_unt g s t)) /\ ((strict_unt g s (t with accesses := [])) = (strict_unt g s t)) ``,
 STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [strict_unt_def, LET_DEF, empty_accesses_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_priv_mode_constraints_v1_lem = store_thm(
    "empty_accesses_priv_mode_constraints_v1_lem",
    ``((priv_mode_constraints_v1 g (s with accesses := []) t) = (priv_mode_constraints_v1 g s t)) /\ ((priv_mode_constraints_v1 g s t) ==> (priv_mode_constraints_v1 g s (t with accesses := [])))``,
 STRIP_TAC THENL [EQ_TAC, ALL_TAC] THEN RW_TAC (srw_ss()) [priv_mode_constraints_v1_def, LET_DEF, empty_accesses_mode_lem, get_base_vector_table_def, empty_accesses_av_lem] THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_av_lem]);

val empty_accesses_priv_mode_constraints_v2_lem = store_thm(
    "empty_accesses_priv_mode_constraints_v2_lem",
    ``((priv_mode_constraints_v2 g (s with accesses := []) t) = (priv_mode_constraints_v2 g s t)) /\ ((priv_mode_constraints_v2 g s t) ==> (priv_mode_constraints_v2 g s (t with accesses := [])))``,
 STRIP_TAC THENL [EQ_TAC, ALL_TAC] THEN RW_TAC (srw_ss()) [priv_mode_constraints_v2_def, LET_DEF, empty_accesses_mode_lem, empty_accesses_priv_mode_constraints_v1_lem, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_priv_mode_constraints_v2a_lem = store_thm(
    "empty_accesses_priv_mode_constraints_v2a_lem",
    ``((priv_mode_constraints_v2a g (s with accesses := []) t) = (priv_mode_constraints_v2a g s t)) /\ ((priv_mode_constraints_v2a g s t) ==> (priv_mode_constraints_v2a g s (t with accesses := [])))``,
 STRIP_TAC THENL [EQ_TAC, ALL_TAC] THEN RW_TAC (srw_ss()) [priv_mode_constraints_v2a_def, LET_DEF, empty_accesses_mode_lem, empty_accesses_priv_mode_constraints_v1_lem, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

(* updated interrupt_wait *)

val updated_int_wait_mode_lem = store_thm(
    "updated_int_wait_mode_lem",
    ``(ARM_MODE (s with interrupt_wait updated_by IWU)) = (ARM_MODE s)``,
    RW_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);

val updated_int_wait_untouched_lem = store_thm(
    "updated_int_wait_untouched_lem",
    ``(untouched g s (t with interrupt_wait updated_by IWU)) = (untouched g s t)``,
    EQ_TAC THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF, updated_int_wait_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val updated_int_wait_priv_mode_constraints_v2_lem = store_thm(
    "updated_int_wait_priv_mode_constraints_v2_lem",
    ``(mmu_requirements t g) ==> ((priv_mode_constraints_v2 g s (t with interrupt_wait updated_by IWU)) = (priv_mode_constraints_v2 g s t))``,
    STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [get_base_vector_table_def, priv_mode_constraints_v2_def, get_pc_value_def, priv_mode_constraints_v1_def, LET_DEF, updated_int_wait_mode_lem, trivially_untouched_av_lem] THEN FULL_SIMP_TAC (srw_ss()) [] THEN MP_TAC (SPECL [``t:arm_state``, ``(t with interrupt_wait updated_by IWU):arm_state``, ``g:word32``] trivially_untouched_av_lem) THEN UNDISCH_MATCH_TAC ``~ access_violation X`` THEN UNDISCH_TAC ``mmu_requirements t g`` THEN RW_TAC (srw_ss()) []);

val updated_int_wait_priv_mode_constraints_v2a_lem = store_thm(
    "updated_int_wait_priv_mode_constraints_v2a_lem",
    ``(mmu_requirements t g) ==> ((priv_mode_constraints_v2a g s (t with interrupt_wait updated_by IWU)) = (priv_mode_constraints_v2a g s t))``,
    STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [get_base_vector_table_def, priv_mode_constraints_v2a_def, get_pc_value_def, priv_mode_constraints_v1_def, LET_DEF, updated_int_wait_mode_lem, trivially_untouched_av_lem] THEN FULL_SIMP_TAC (srw_ss()) [] THEN MP_TAC (SPECL [``t:arm_state``, ``(t with interrupt_wait updated_by IWU):arm_state``, ``g:word32``] trivially_untouched_av_lem) THEN UNDISCH_MATCH_TAC ``~ access_violation X`` THEN UNDISCH_TAC ``mmu_requirements t g`` THEN RW_TAC (srw_ss()) []);

val updated_int_wait_priv_mode_similar_lem = store_thm(
    "updated_int_wait_priv_mode_similar_lem",
    ``(priv_mode_similar g (s1 with interrupt_wait updated_by IWU) (s2 with interrupt_wait updated_by IWU)) = (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def, LET_DEF, ARM_MODE_def, ARM_READ_CPSR_def]);

val updated_int_wait_similar_lem = store_thm(
    "updated_int_wait_similar_lem",
    ``(mmu_requirements s1 g) ==> (mmu_requirements s2 g) ==> (similar g s1 s2) ==> (similar g (s1 with interrupt_wait updated_by (0 =+ A)) (s2 with interrupt_wait updated_by (0 =+ A)))``,
    ASSUME_TAC (SPECL [``s1:arm_state``, ``(s1 with interrupt_wait updated_by (0 =+ A)):arm_state``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``(s2 with interrupt_wait updated_by (0 =+ A)):arm_state``, ``g:word32``] trivially_untouched_av_lem)
      THEN RW_TAC (srw_ss()) [similar_def, equal_user_register_def, updated_int_wait_mode_lem]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN EVAL_TAC);



(**************************************)
(****      contract massaging    ******)
(**************************************)

val take_irq_exception_comb_thm2 = store_thm(
    "take_irq_exception_comb_thm2",
    ``preserve_relation_mmu (take_irq_exception <|proc := 0|>) (assert_mode 16w) mode_mix  priv_mode_constraints_v2a priv_mode_similar``,
    MODE_MIX_TAC ``comb_mode 16w 18w`` THEN FULL_SIMP_TAC (srw_ss()) [take_irq_exception_comb_thm]);

val take_prefetch_abort_exception_comb_thm2 = store_thm(
    "take_prefetch_abort_exception_comb_thm2",
    ``preserve_relation_mmu (take_prefetch_abort_exception <|proc := 0|>) (assert_mode 16w) mode_mix priv_mode_constraints_v2a priv_mode_similar``,
    MODE_MIX_TAC ``comb_mode 16w 23w`` THEN FULL_SIMP_TAC (srw_ss()) [take_prefetch_abort_exception_comb_thm]);


(**************************************)
(****         main proof         ******)
(**************************************)



val _ = g` irpt <> HW_Reset ==>
           irpt <> HW_Fiq   ==>
           preserve_relation_mmu (mmu_arm_next irpt)
             (assert_mode 16w) mode_mix priv_mode_constraints_v2a
              priv_mode_similar`;


val _ = e(Cases_on `irpt` THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, mmu_arm_next_def]);

(* 1. instructions *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [waiting_for_interrupt_def, readT_def]);
val _ = e(`s1.interrupt_wait 0 = s2.interrupt_wait 0` by FULL_SIMP_TAC (srw_ss()) [similar_def]);
val _ = e(Cases_on `s1.interrupt_wait 0` THEN FULL_SIMP_TAC (srw_ss()) []);

(* 1.1. waiting for any interrupt *)
val _ = e(ASSUME_TAC (SPECL [``g:word32``, ``s1:arm_state``] untouched_refl));
val _ = e(ASSUME_TAC (SPECL [``g:word32``, ``s2:arm_state``] untouched_refl));
val _ = e(ASSUME_TAC reflex_priv_mode_constraints_v2a_thm);
val _ = e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, reflexive_comp_def]);
val _ = e(IMP_RES_TAC empty_accesses_similar_lem
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2a_lem, empty_accesses_untouched_lem]
	  THEN RES_TAC);

(* 1.2. not waiting for interrupt *)
val _ = e(ASSUME_TAC (CONJUNCT1 fetch_instruction_thm));
val _ = e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
val _ = e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1 with accesses:= []``, ``s2 with accesses := []``]));
val _ = e(IMP_RES_TAC empty_accesses_similar_lem
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_sim_def]
	  THEN RES_TAC
	  THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = e(Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = e(ASSUME_TAC (SPECL [``g:word32``, ``s1':arm_state``, ``s2':arm_state``] generate_priv_mode_similar_lem));
val _ = e(ASSUME_TAC (SPECL [``g:word32``, ``s1':arm_state``, ``s2':arm_state``]  similarity_implies_equal_av_thm));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = e(RES_TAC);
val _ = e(Cases_on `access_violation s1'` THEN FULL_SIMP_TAC (srw_ss()) []);

(* 1.2.1. prefetch abort *)
val _ = e(IMP_RES_TAC untouched_mmu_setup_lem);
val _ = e(ASSUME_TAC take_prefetch_abort_exception_comb_thm2);
val _ = e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
val _ = e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1' with accesses:= []``, ``s2' with accesses := []``]));
val _ = e(IMP_RES_TAC empty_accesses_similar_lem
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem]
	  THEN RES_TAC
	  THEN IMP_RES_TAC untouched_trans
	  THEN IMP_RES_TAC (GEN_ALL strict_unt_and_priv_mode_constraints_v2a_lem)
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_priv_mode_constraints_v2a_lem]);

(* 1.2.2. no prefetch abort *)
val _ = e(IMP_RES_TAC untouched_mmu_setup_lem);
val _ = e(Cases_on `r` THEN Cases_on `r'`);
val _ = e(ASSUME_TAC (SPECL [``r:ARMinstruction``, ``q':Encoding``, ``q'':word4``] (GEN_ALL arm_instr_comb_thm)));
val _ = e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
val _ = e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1' with accesses:= []``, ``s2' with accesses := []``]));
val _ = e(IMP_RES_TAC empty_accesses_similar_lem
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem]
	  THEN RES_TAC
	  THEN IMP_RES_TAC untouched_trans
	  THEN IMP_RES_TAC (GEN_ALL strict_unt_and_priv_mode_constraints_v2a_lem)
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_priv_mode_constraints_v2a_lem]);
val _ = e(ASSUME_TAC (SPECL [``g:word32``, ``s1'':arm_state``, ``s2'':arm_state``]  similarity_implies_equal_av_thm));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = e(RES_TAC);
val _ = e(Cases_on `access_violation s1''` THEN FULL_SIMP_TAC (srw_ss()) []);

(* data abort *)
val _ = e(`(ARM_MODE s1'' = 16w) /\ (ARM_MODE s2'' = 16w)` by (UNDISCH_TAC ``priv_mode_constraints_v2a g s1' s1''`` THEN UNDISCH_TAC ``priv_mode_constraints_v2a g s2' s2''`` THEN RW_TAC (srw_ss()) [LET_DEF, priv_mode_constraints_v2a_def, priv_mode_constraints_v1_def]));
val _ = e(IMP_RES_TAC untouched_mmu_setup_lem);
val _ = e(ASSUME_TAC take_data_abort_exception_comb_thm);
val _ = e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
val _ = e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1'' with accesses:= []``, ``s2'' with accesses := []``]));
val _ = e(IMP_RES_TAC empty_accesses_similar_lem
	THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem, priv_mode_constraints_v2a_def, comb_mode_def, assert_mode_def, mode_mix_def, empty_accesses_priv_mode_constraints_v1_lem, empty_accesses_priv_mode_constraints_v2a_lem]
	THEN RES_TAC
	THEN IMP_RES_TAC untouched_trans
	THEN IMP_RES_TAC (SIMP_RULE (srw_ss()) [trans_fun_def] trans_priv_mode_constraints_thm)
	THEN RES_TAC
	THEN IMP_RES_TAC untouched_trans
	THEN IMP_RES_TAC (SIMP_RULE (srw_ss()) [trans_fun_def] trans_priv_mode_constraints_thm)
	THEN FULL_SIMP_TAC (srw_ss()) []);

(* 2. irq *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [clear_wait_for_interrupt_def, writeT_def, seqT_def]);
val _ = e(Cases_on `take_irq_exception <|proc := 0|> (s1 with accesses := [])` THEN Cases_on `take_irq_exception <|proc := 0|> (s2 with accesses := [])` THEN ASSUME_TAC take_irq_exception_comb_thm2 THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def] THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``(s1 with accesses := []):arm_state``, ``(s2 with accesses := []):arm_state``])
	  THEN IMP_RES_TAC empty_accesses_similar_lem
	  THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2a_lem, empty_accesses_untouched_lem]
	  THEN RES_TAC
	  THEN `ARB:unit = ()` by (Cases_on `(ARB:unit)` THEN FULL_SIMP_TAC (srw_ss()) [])
	  THEN FULL_SIMP_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2a_lem]
	  THEN IMP_RES_TAC untouched_mmu_setup_lem
	  THEN IMP_RES_TAC updated_int_wait_similar_lem
	  THEN IMP_RES_TAC (GEN_ALL updated_int_wait_priv_mode_similar_lem)
	  THEN IMP_RES_TAC similarity_implies_equal_av_thm
	  THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2a_lem, untouched_mmu_setup_lem, updated_int_wait_similar_lem]);


val mmu_arm_next_thm = save_thm("mmu_arm_next_thm", top_thm());





(************************************************************)
(******************   C. SVC statement   ********************)
(************************************************************)





(* Step 1: modes reachable with bad PC *)

val bad_PC_lem = store_thm(
    "bad_PC_lem",
    ``(mmu_requirements s g) ==>
      ((assert_mode 16w) s)  ==>
      (~aligned_word_readable s  ((s.psrs (0,CPSR)).T) (s.registers (0,RName_PC))) ==>
      (intrpt <> HW_Reset)   ==>
      (intrpt <> HW_Fiq)     ==>
      (mmu_arm_next intrpt s = ValueState () t)
     ==> (little_mode_mix t)``,
     RW_TAC (srw_ss()) [mmu_arm_next_def, waiting_for_interrupt_def, readT_def, clear_wait_for_interrupt_def, writeT_def] THEN1 FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, assert_mode_def, empty_accesses_mode_lem]
     THENL [UNDISCH_ALL_TAC THEN CASE_TAC THEN RW_TAC (srw_ss()) []
               THEN ASSUME_TAC (SPECL [``a:(string # Encoding # word4 # ARMinstruction)``, ``b:arm_state``, ``(s with accesses := [])``, ``g:word32``] (GEN_ALL fetch_instr_av_lem))
               THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_aligned_word_readable_lem]
               THEN RES_TAC
               THEN UNDISCH_ALL_TAC THEN (REPEAT CASE_TAC) THEN RW_TAC(srw_ss()) []
               THEN ASSUME_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 fetch_instruction_thm)))
               THEN ASSUME_TAC take_prefetch_abort_exception_comb_thm
               THEN ASSUME_TAC reflex_priv_mode_similar_thm
               THEN IMP_RES_TAC downgrade_thm
               THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def, keep_untouched_relation_def]
               THEN SPEC_ASSUM_TAC (``!g s s' x. X``, [``g:word32``, ``(s with accesses := [])``, ``b:arm_state``, ``(q,r):(string # Encoding # word4 # ARMinstruction)``])
               THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``(b with accesses := [])``, ``t:arm_state``])
               THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_mode_lem, assert_mode_def, empty_accesses_untouched_lem]
               THEN RES_TAC
               THEN IMP_RES_TAC untouched_mmu_setup_lem
               THEN RES_TAC
               THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, comb_mode_def, assert_mode_def],
            ASSUME_TAC take_irq_exception_comb_thm]
     THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
     THEN UNDISCH_ALL_TAC THEN CASE_TAC THEN RW_TAC(srw_ss()) []
     THEN Cases_on `a`
     THEN ASSUME_TAC reflex_priv_mode_similar_thm
     THEN IMP_RES_TAC downgrade_thm
     THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def]
     THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``(s with accesses := [])``, ``b:arm_state``])
     THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_mode_lem, assert_mode_def, empty_accesses_untouched_lem]
     THEN RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, comb_mode_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);



(* Step 2: the best contract we can offer *)


val mmu_arm_next_svc_thm = store_thm(
    "mmu_arm_next_svc_thm",
    ``(irpt <> HW_Reset) ==> (irpt <> HW_Fiq) ==> preserve_relation_mmu (mmu_arm_next irpt) (assert_mode 16w) mode_mix priv_mode_constraints_v4 priv_mode_similar``,
    MP_TAC mmu_arm_next_thm
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def]
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v4_def, LET_DEF]
       THEN IMP_RES_TAC similarity_implies_equal_mode_thm
       THEN `(s1.psrs (0,CPSR)).T =  (s2.psrs (0,CPSR)).T` by FULL_SIMP_TAC (srw_ss()) [similar_def]
       THEN Cases_on `ARM_MODE s1' = 19w` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [ALL_TAC, METIS_TAC []]
       THEN `((s1'.psrs (0,SPSR_svc)).T) =  ((s1.psrs (0,CPSR)).T)` by (FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def] THEN RW_TAC (srw_ss()) [])
       THEN `((s1'.psrs (0,SPSR_svc)).J) =  ((s1.psrs (0,CPSR)).J)` by (FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def] THEN RW_TAC (srw_ss()) [])
       THEN `((s2'.psrs (0,SPSR_svc)).T) =  ((s2.psrs (0,CPSR)).T)` by (FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def] THEN RW_TAC (srw_ss()) [])
       THEN `((s2'.psrs (0,SPSR_svc)).J) =  ((s2.psrs (0,CPSR)).J)` by (FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def] THEN RW_TAC (srw_ss()) [])
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2a_def]
       THEN Cases_on `a`
       THEN IMP_RES_TAC similarity_implies_equal_mode_thm
       THEN ASSUME_TAC (SPECL [``s1':arm_state``, ``s1:arm_state``, ``irpt:HWInterrupt``, ``g:word32``] (GEN_ALL bad_PC_lem))
       THEN ASSUME_TAC (SPECL [``s2':arm_state``, ``s2:arm_state``, ``irpt:HWInterrupt``, ``g:word32``] (GEN_ALL bad_PC_lem))
       THEN ASSUME_TAC (SPECL [``s1':arm_state``, ``s1:arm_state``, ``(s1.psrs (0,CPSR)).T``, ``g:word32``, ``(s1.registers (0,RName_PC))``] (GEN_ALL global_aligned_word_readable_lem))
       THEN ASSUME_TAC (SPECL [``s2':arm_state``, ``s2:arm_state``, ``(s2.psrs (0,CPSR)).T``, ``g:word32``, ``(s2.registers (0,RName_PC))``] (GEN_ALL global_aligned_word_readable_lem))
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THENL [Cases_on `(s1.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s1 (s1.psrs (0,CPSR)).T  (s1.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s1.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s1 (s1.psrs (0,CPSR)).T  (s1.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s2.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s2 (s2.psrs (0,CPSR)).T (s2.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s2.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s2 (s2.psrs (0,CPSR)).T  (s2.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def]]);



(* Step 3: relate v4 and v3 of pmc *)

val pmc_34_lem = store_thm(
    "pmc_34_lem",
    ``(mmu_requirements s1 g) ==> (priv_mode_constraints_v4 g s0 s1) ==> (priv_mode_constraints_v3 g s0 s1)``,
    RW_TAC (srw_ss()) [priv_mode_constraints_v3_def, priv_mode_constraints_v4_def]
       THEN ASSUME_TAC you_and_me_thm
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def, aligned_word_readable_def]
       THEN PAT_ASSUM ``!addr iw. X`` (fn th => ASSUME_TAC (SPECL [``s1.registers (0,RName_LRsvc) + 0xFFFFFFFEw``, ``F``] th)
                                          THEN ASSUME_TAC (SPECL [``s1.registers (0,RName_LRsvc) + 0xFFFFFFFCw``, ``F``] th))
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [negated_inequalities]
       THEN FULL_SIMP_TAC (srw_ss()) [address_border, negated_inequalities, negated_and_or, address_trans]
       THEN METIS_TAC [address_border, negated_inequalities, negated_and_or, address_trans]);





(* Step 4: the contract finally used for the switching lemma *)

val mmu_arm_next_comb_thm = store_thm(
    "mmu_arm_next_comb_thm",
    ``(irpt <> HW_Reset) ==> (irpt <> HW_Fiq) ==> preserve_relation_mmu (mmu_arm_next irpt) (assert_mode 16w) mode_mix priv_mode_constraints_v3 priv_mode_similar``,
    STRIP_TAC
      THEN IMP_RES_TAC mmu_arm_next_svc_thm
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def]
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []
      THEN IMP_RES_TAC untouched_mmu_setup_lem
      THEN IMP_RES_TAC pmc_34_lem
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);




val _ = export_theory();
