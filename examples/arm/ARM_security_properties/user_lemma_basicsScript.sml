(*  This theory covers the main part of the manual proofs needed to show the user lemma *)
(*  Author: Oliver Schwarz *)

open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory;
open tacticsLib;
open wordsTheory wordsLib;

val _ =  new_theory("user_lemma_basics");
val _ = ParseExtras.temp_loose_equality()

val _ = temp_overload_on ("return", ``constT``);
val _ = overload_on("priv_mode_constraints", ``priv_mode_constraints_v1``);
val priv_mode_constraints_def = priv_mode_constraints_v1_def;




(************************************************************)
(***********************  General    ************************)
(************************************************************)



val untouched_refl = store_thm(
    "untouched_refl",
    ``!gst s. untouched gst s s``,
    RW_TAC (srw_ss()) [untouched_def] THEN RW_TAC (srw_ss()) []);



val similarity_implies_equal_mode_thm = store_thm(
    "similarity_implies_equal_mode_thm",
    ``! g s1 s2. (similar g s1 s2) ==> (ARM_MODE s1 = ARM_MODE s2)``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THEN SPEC_ASSUM_TAC (``!(ii:iiid). X``, [``<|proc:=0|>``])
      THEN FULL_SIMP_TAC (srw_ss()) []);


val similarity_implies_equal_av_thm = store_thm(
    "similarity_implies_equal_av_thm",
    ``! g s1 s2. (similar g s1 s2) ==> (access_violation s1 = access_violation s2)``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []);


val keep_mode_lem = store_thm(
    "keep_mode_lem",
    ``!m f s s' x.
      (ARM_MODE s = m)        ==>
      (f s = ValueState x s') ==>
      (s.psrs = s'.psrs)
     ==>
      (ARM_MODE s' = m)``,
     NTAC 5 STRIP_TAC THEN EVAL_TAC THEN METIS_TAC []);



val untouched_av_on_coprocessor_update_lem = store_thm(
     "untouched_av_on_coprocessor_update_lem",
     ``!s gst. (mmu_requirements s gst) ==>
       (access_violation s =
        access_violation ((arm_state_coprocessors_fupd
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <|
SCR := scr |>)))) s))``,
     (NTAC 2 STRIP_TAC)
        THEN (`mmu_requirements ( (arm_state_coprocessors_fupd
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <|
SCR := scr |>)))) s) gst = mmu_requirements s gst` by RW_TAC
(srw_ss()) [mmu_requirements_def])
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN IMP_RES_TAC access_violation_req
        THEN RW_TAC (srw_ss()) [access_violation_pure_def]);



val preserve_relation_comb_16_27_thm = store_thm(
    "preserve_relation_comb_16_27_thm",
    ``(preserve_relation_mmu G (assert_mode 16w) (assert_mode 16w) f y) ==> (preserve_relation_mmu G (assert_mode 16w) (comb_mode 16w 27w) f y)``,
    `comb (assert_mode 16w) (assert_mode 27w) (comb_mode 16w 27w)` by (RW_TAC (srw_ss()) [ comb_mode_def, comb_def] THEN METIS_TAC [])
      THEN RW_TAC (srw_ss()) [preserve_relation_comb_thm1, comb_mode_def, comb_def]
      THEN IMP_RES_TAC preserve_relation_comb_thm1);



val empty_unt_def = Define `empty_unt (g:word32) (s1:arm_state) (s2:arm_state) = T`;
val empty_sim_def = Define `empty_sim (g:word32) (s1:arm_state) (s2:arm_state) = T`;


val strict_unt_def = Define `strict_unt (g:word32) s t =    (s.psrs         = t.psrs)
                                                         /\ (s.registers    = t.registers)
                                                         /\ (s.memory       = t.memory)
                                                         /\ (s.coprocessors = t.coprocessors)
                                                         /\ (s.information  = t.information)`;


val reflex_priv_mode_constraints_thm = store_thm("reflex_priv_mode_constraints_thm",
              `` reflexive_comp  priv_mode_constraints (assert_mode 16w)``,
                RW_TAC (srw_ss()) [reflexive_comp_def,priv_mode_constraints_v1_def,assert_mode_def]);

val reflex_priv_mode_constraints_v2_thm = store_thm("reflex_priv_mode_constraints_v2_thm",
              `` reflexive_comp  priv_mode_constraints_v2 (assert_mode 16w)``,
                RW_TAC (srw_ss()) [reflexive_comp_def,priv_mode_constraints_v1_def, reflex_priv_mode_constraints_thm,priv_mode_constraints_v2_def,assert_mode_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val reflex_priv_mode_constraints_v2a_thm = store_thm("reflex_priv_mode_constraints_v2a_thm",
              `` reflexive_comp  priv_mode_constraints_v2a (assert_mode 16w)``,
                RW_TAC (srw_ss()) [reflexive_comp_def,priv_mode_constraints_v1_def, reflex_priv_mode_constraints_thm,priv_mode_constraints_v2a_def,assert_mode_def] THEN FULL_SIMP_TAC (srw_ss()) []);



val trans_priv_mode_constraints_thm =
    store_thm("trans_priv_mode_constraints_thm",
              ``trans_fun priv_mode_constraints``,
              RW_TAC (srw_ss()) [LET_DEF, trans_fun_def,priv_mode_constraints_def]
                     THEN RW_TAC (srw_ss()) [] THEN
                     FULL_SIMP_TAC (srw_ss()) [get_base_vector_table_def,ARM_MODE_def,ARM_READ_CPSR_def]);

val reflex_priv_mode_similar_thm = store_thm(
    "reflex_priv_mode_similar_thm",
    ``refl_rel priv_mode_similar``,
    RW_TAC (srw_ss()) [refl_rel_def, priv_mode_similar_def] THEN RW_TAC (srw_ss()) []);


val generate_priv_mode_similar_lem = store_thm(
    "generate_priv_mode_similar_lem",
    ``!g s1 s2. (ARM_MODE s1 = 16w) ==> (ARM_MODE s2 = 16w) ==> (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def]);


val reflex_empty_sim_thm = store_thm(
    "reflex_empty_sim_thm",
    ``refl_rel empty_sim``,
    RW_TAC (srw_ss()) [refl_rel_def,empty_sim_def] THEN RW_TAC (srw_ss()) []);


val reflex_strict_unt_thm = store_thm(
   "reflex_strict_unt_thm",
   ``!u. reflexive_comp strict_unt (assert_mode u)``,
   RW_TAC (srw_ss()) [reflexive_comp_def, strict_unt_def,assert_mode_def]);

val strict_unt_and_priv_mode_constraints_v2_lem = store_thm(
    "strict_unt_and_priv_mode_constraints_v2_lem",
    ``strict_unt g a b ==> priv_mode_constraints_v2 g b c ==>  priv_mode_constraints_v2 g a c``,
    RW_TAC (srw_ss()) [strict_unt_def, priv_mode_constraints_v2_def, priv_mode_constraints_v1_def, ARM_MODE_def, ARM_READ_CPSR_def, LET_DEF, vector_table_address_def, get_base_vector_table_def, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val strict_unt_and_priv_mode_constraints_v2a_lem = store_thm(
    "strict_unt_and_priv_mode_constraints_v2a_lem",
    ``strict_unt g a b ==> priv_mode_constraints_v2a g b c ==>  priv_mode_constraints_v2a g a c``,
    RW_TAC (srw_ss()) [strict_unt_def, priv_mode_constraints_v2a_def, priv_mode_constraints_v1_def, ARM_MODE_def, ARM_READ_CPSR_def, LET_DEF, vector_table_address_def, get_base_vector_table_def, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val trans_strict_unt_thm =
    store_thm("trans_strict_unt_thm",
              ``trans_fun strict_unt``,
              RW_TAC (srw_ss()) [LET_DEF, trans_fun_def, strict_unt_def]
                     THEN RW_TAC (srw_ss()) [] );


val reflex_empty_unt_thm = store_thm(
   "reflex_empty_unt_thm",
   ``!u. reflexive_comp empty_unt (assert_mode u)``,
   RW_TAC (srw_ss()) [reflexive_comp_def, empty_unt_def,assert_mode_def]);


val trans_empty_unt_thm =
    store_thm("trans_empty_unt_thm",
              ``trans_fun empty_unt``,
              RW_TAC (srw_ss()) [LET_DEF, trans_fun_def, empty_unt_def]
                     THEN RW_TAC (srw_ss()) [] );

val strict_unt_lem = store_thm(
    "strict_unt_lem",
    ``! COMP.
        preserve_relation_mmu COMP (assert_mode u) (assert_mode u) strict_unt empty_sim
    ==> preserve_relation_mmu COMP (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [empty_unt_def, strict_unt_def, preserve_relation_mmu_def]
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN METIS_TAC []);

val gen_strict_unt_lem = store_thm(
    "gen_strict_unt_lem",
    ``! COMP.
        (!u. preserve_relation_mmu COMP (assert_mode u) (assert_mode u) strict_unt empty_sim)
    ==> (!u. preserve_relation_mmu COMP (assert_mode u) (assert_mode u) empty_unt empty_sim)``,
    RW_TAC (srw_ss()) [empty_unt_def, strict_unt_def, preserve_relation_mmu_def]
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN METIS_TAC []);


val empty_extras_lem = store_thm(
    "empty_extras_lem",
    ``! COMP.
       preserve_relation_mmu COMP (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar
     = preserve_relation_mmu COMP (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    STRIP_TAC THEN EQ_TAC
      THENL[ RW_TAC (srw_ss()) [LET_DEF, preserve_relation_mmu_def, assert_mode_def, empty_unt_def, empty_sim_def]
                THEN `priv_mode_similar g s1 s2` by FULL_SIMP_TAC (srw_ss()) [similar_def, priv_mode_similar_def]
                THEN METIS_TAC [],
             RW_TAC (srw_ss()) [LET_DEF, preserve_relation_mmu_def, assert_mode_def, empty_unt_def, empty_sim_def]
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_similar_def, untouched_def, LET_DEF, priv_mode_constraints_def])]);



val fixed_flags_def = Define `fixed_flags xI xF g s1 s2 = (((ARM_MODE s1 = 16w) ==> ((s1.psrs(0,CPSR)).I = xI)) /\ ((s1.psrs(0,CPSR)).F = xF) /\ ((ARM_MODE s2 = 16w) ==> ((s2.psrs(0,CPSR)).I = xI)) /\ ((s2.psrs(0,CPSR)).F = xF)) `;


val fixed_flags_empty_lem = store_thm(
    "fixed_flags_empty_lem",
    ``!COMP inv1 inv2 uf.
      ((!xI xF. preserve_relation_mmu COMP (assert_mode 16w) inv2 uf (fixed_flags xI xF) )
              = preserve_relation_mmu COMP (assert_mode 16w) inv2 uf empty_sim)
      /\
      ((!xI xF. preserve_relation_mmu COMP inv1 inv2 uf (fixed_flags xI xF) )
            ==> preserve_relation_mmu COMP inv1 inv2 uf empty_sim)``,
    NTAC 5 STRIP_TAC
       THENL[ EQ_TAC
                THENL[ RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                          THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                          THEN UNDISCH_ALL_TAC
                          THEN RW_TAC (srw_ss()) []
                          THEN Cases_on `ARM_MODE s2 = 16w`
                          THEN FULL_SIMP_TAC (srw_ss()) [],
                       RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                          THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
                          THEN METIS_TAC [untouched_def]],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s2 = 16w`
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val fix_flags_def = Define `fix_flags xI xF uy g s1 s2 =  ((uy g s1 s2) /\ (fixed_flags xI xF g s1 s2))`;


val fix_flags_lem = store_thm(
    "fix_flags_lem",
    ``!COMP inv1 inv2 uf uy.
      ((!xI xF. preserve_relation_mmu COMP (assert_mode 16w) inv2 uf (fix_flags xI xF uy) )
              = preserve_relation_mmu COMP (assert_mode 16w) inv2 uf uy)
      /\
      ((!xI xF. preserve_relation_mmu COMP inv1 inv2 uf (fix_flags xI xF uy) )
            ==> preserve_relation_mmu COMP inv1 inv2 uf uy)``,
    NTAC 6 STRIP_TAC
       THENL[ EQ_TAC
                THENL[ RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                          THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                          THEN UNDISCH_ALL_TAC
                          THEN RW_TAC (srw_ss()) []
                          THEN Cases_on `ARM_MODE s2 = 16w`
                          THEN FULL_SIMP_TAC (srw_ss()) [],
                       RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                          THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
                          THEN METIS_TAC [untouched_def]],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s2 = 16w`
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val extras_lem = store_thm(
    "extras_lem",
    ``!A. (!u. preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))
)``,
    RW_TAC (srw_ss()) [empty_extras_lem, fix_flags_lem] THEN METIS_TAC [empty_extras_lem, fix_flags_lem]);


val extras_lem2 = store_thm(
    "extras_lem2",
    ``!A.     (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``,
    RW_TAC (srw_ss()) [empty_extras_lem, fix_flags_lem] THEN METIS_TAC [empty_extras_lem, fix_flags_lem]);


val extras_lem3 = store_thm(
    "extras_lem3",
    ``!A. (!u. preserve_relation_mmu (A) (assert_mode u) (assert_mode u) strict_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode u) (assert_mode u) strict_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``,
    RW_TAC (srw_ss()) [gen_strict_unt_lem, empty_extras_lem, fix_flags_lem] THEN METIS_TAC [gen_strict_unt_lem, empty_extras_lem, fix_flags_lem]);


val extras_lem4 = store_thm(
    "extras_lem4",
    ``!A.     (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``,
    RW_TAC (srw_ss()) [strict_unt_lem, empty_extras_lem, fix_flags_lem] THEN METIS_TAC [strict_unt_lem, empty_extras_lem, fix_flags_lem]);


 val comb_monot_thm = store_thm("comb_monot_thm",
               ``!a:(arm_state -> bool). comb a a a``,
               RW_TAC (srw_ss()) [comb_def]);

val preserve_relation_comb_thm =
    store_thm ("preserve_relation_comb_thm",
               ``! a b c d f  uf uy.
              preserve_relation_mmu  f d b uf uy
              ==>
              comb a b c ==>
              preserve_relation_mmu  f d c uf uy``,
               RW_TAC (srw_ss()) [preserve_relation_mmu_def,comb_def]
                      THEN PAT_X_ASSUM ``∀g s1 s2. X``
                      (fn thm => ASSUME_TAC (SPECL [``g:bool[32]``,
                                                    ``s1:arm_state``, ``s2:arm_state``] thm))
    THEN RES_TAC
         THEN RW_TAC (srw_ss()) []);


val global_aligned_word_readable_lem = store_thm(
    "global_aligned_word_readable_lem",
    ``mmu_requirements s1 g  ==>
      mmu_requirements s2 g  ==>
      (aligned_word_readable s1 is_thumb addr =  aligned_word_readable s2 is_thumb addr)``,
     RW_TAC (srw_ss()) [aligned_word_readable_def]
       THEN (NTAC 2 RES_TAC)
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN IMP_RES_TAC same_setup_same_rights_lem
       THEN METIS_TAC [same_setup_same_rights_lem]);



val seqT_preserves_relation_comb_thm =
    store_thm ("seqT_preserves_relation_comb_thm",
    ``! f1 f2 k inv2 comb_inv  uf uy.
          (comb  (assert_mode k) inv2 comb_inv) ==>
          (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k) (comb_inv) uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) comb_inv uf uy)
``,
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def,trans_fun_def])
    THEN (UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THENL [UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN METIS_TAC [untouched_trans, comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def,comb_def]
THEN Cases_on `f2 a b`
THEN Cases_on `f2 a' b'`
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_X_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
THEN
(TRY (PAT_X_ASSUM `` ∀g st1 st2 st3. X`` (fn th => ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s1:arm_state``, ``b:arm_state``, ``b'':arm_state``] th) THEN ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s2:arm_state``, ``b':arm_state``, ``b''':arm_state``] th))))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [])),
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []]);




(************************************************************)
(*****************    Reading and Writing *******************)
(************************************************************)


val equal_mem_lem = store_thm(
    "equal_mem_lem",
    `` !s1 s2 g (addr:bool[32]) is_write.
       (similar g s1 s2)       ==>
       (mmu_requirements s1 g) ==>
       (mmu_requirements s2 g)
    ==>
       ((s1.memory addr) = (s2.memory addr))
     \/
       (
        ~ permitted_byte_pure addr is_write s1.coprocessors.state.cp15.C1
                                           s1.coprocessors.state.cp15.C2
                                           s1.coprocessors.state.cp15.C3
                                           F s1.memory
        /\
        ~ permitted_byte_pure addr is_write s2.coprocessors.state.cp15.C1
                                           s2.coprocessors.state.cp15.C2
                                           s2.coprocessors.state.cp15.C3
                                           F s2.memory
       )``,
   REPEAT STRIP_TAC
       THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN MP_TAC (SPEC ``addr:bool[32]`` negated_and_or)
       THEN MP_TAC (SPEC ``addr:word32`` address_border)
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def, similar_def]
       THEN METIS_TAC []);



val stay_similar_lem = store_thm(
    "stay_similar_lem",
    ``!s1 s2 g addr x.
      (mmu_requirements s1 g) ==>
      (mmu_requirements s2 g) ==>
      (similar g s1 s2)
     ==> ((similar g (s1 with accesses updated_by CONS (MEM_READ addr)) (s2 with accesses updated_by CONS (MEM_READ addr)))
     /\  (similar g (s1 with accesses updated_by CONS (MEM_WRITE addr x)) (s2 with accesses updated_by CONS (MEM_WRITE addr x))))``,
     NTAC 8 STRIP_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [similar_def, LET_DEF, read__reg_def, readT_def]
        THEN MP_TAC (SPECL [``addr:word32``, ``x:word8``]  mmu_requirement_accesses_update_lem)
        THEN STRIP_TAC
        THEN RES_TAC
        THEN MP_TAC access_violation_req
        THEN STRIP_TAC
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [access_violation_pure_def]
        THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
        THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
        THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN MP_TAC same_setup_same_rights_lem
        THEN STRIP_TAC
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def]
        THEN METIS_TAC []);

val keep_mode_on_accesses_update_lem = store_thm(
    "keep_mode_on_accesses_update_lem",
    ``!m s addr x.
      (ARM_MODE s = m)
     ==>
        (ARM_MODE (s with accesses updated_by CONS (MEM_READ addr)) = m) /\
        (ARM_MODE (s with accesses updated_by CONS (MEM_WRITE addr x)) = m)``,
     NTAC 4  STRIP_TAC THEN EVAL_TAC);



val read_mem1_mode_thm = store_thm(
    "read_mem1_mode_thm",
    ``!addr. keep_mode_relation (read_mem1 <|proc:=0|> addr) (assert_mode 16w) (assert_mode 16w)``,
    RW_TAC (srw_ss()) [keep_mode_relation_def, writeT_def, readT_def,  seqT_def, read_mem1_def, assert_mode_def]
       THEN UNDISCH_ALL_TAC
       THEN IF_CASES_TAC
       THEN STRIP_TAC
       THEN REPEAT (EVAL_TAC THEN RW_TAC (srw_ss()) []));



val read_mem1_similar_thm = store_thm (
    "read_mem1_similar_thm",
    ``!addr. keep_similar_relation (read_mem1 <|proc:=0|> addr) (assert_mode 16w) empty_sim``,
    PURE_ONCE_REWRITE_TAC [keep_similar_relation_def]
       THEN NTAC 8 STRIP_TAC
       THEN Cases_on `read_mem1 <|proc:=0|> addr s1`
       THEN Cases_on `read_mem1 <|proc:=0|> addr s2`
       THEN FULL_SIMP_TAC (srw_ss()) [empty_sim_def]
       THENL [FULL_SIMP_TAC (srw_ss()) [read_mem1_def, writeT_def, readT_def,  seqT_def]
                 THEN (`b = (s1 with accesses updated_by CONS (MEM_READ addr))` by
                            (Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ addr))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN (`b' = (s2 with accesses updated_by CONS (MEM_READ addr))` by
                            (Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ addr))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``, ``addr:word32``, ``F``] equal_mem_lem)
                 THEN RES_TAC
                 THENL [`similar g b b'  = similar g s1 s2` by METIS_TAC [stay_similar_lem]
                           THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ addr))`
                           THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ addr))`
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) [similar_def,arm_stepTheory.ARM_MODE_def, arm_stepTheory.ARM_READ_CPSR_def]
                           THEN METIS_TAC [],
                        ASSUME_TAC (SPECL [``addr:word32``, ``x:word8``, ``s1:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC (SPECL [``addr:word32``, ``x:word8``, ``s2:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC access_violation_req
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN MP_TAC  malicious_read
                           THEN STRIP_TAC
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN METIS_TAC [stay_similar_lem, keep_mode_on_accesses_update_lem]],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ addr))`
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ addr))`
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ addr))`
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


val read_mem1_ut_thm = store_thm (
    "read_mem1_ut_thm",
    ``!addr. keep_untouched_relation (read_mem1 <|proc:=0|> addr) (assert_mode 16w) strict_unt``,
    RW_TAC (srw_ss()) [keep_untouched_relation_def, read_mem1_def, seqT_def, writeT_def, readT_def, strict_unt_def]
       THEN Cases_on `access_violation (s with accesses updated_by CONS (MEM_READ addr))`
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF, assert_mode_def]
       THEN RW_TAC (srw_ss()) [keep_mode_on_accesses_update_lem]);


val read_mem1_strict_thm = store_thm(
    "read_mem1_strict_thm",
    ``!addr. preserve_relation_mmu (read_mem1 <|proc:=0|> addr) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim``,
    METIS_TAC [read_mem1_ut_thm, read_mem1_similar_thm, read_mem1_mode_thm, three_parts_thm]);

val read_mem1_thm = save_thm("read_mem1_thm", MATCH_MP extras_lem4 (SPEC_ALL read_mem1_strict_thm));


val write_mem1_mode_thm = store_thm(
    "write_mem1_mode_thm",
    ``!addr data. keep_mode_relation (write_mem1 <|proc:=0|> addr data) (assert_mode 16w) (assert_mode 16w)``,
    RW_TAC (srw_ss()) [keep_mode_relation_def, writeT_def, readT_def,  seqT_def, write_mem1_def, assert_mode_def]
       THEN UNDISCH_ALL_TAC
       THEN IF_CASES_TAC
       THEN STRIP_TAC
       THEN REPEAT (EVAL_TAC THEN RW_TAC (srw_ss()) []));



val write_mem1_ut_thm = store_thm (
    "write_mem1_ut_thm",
    ``!addr data. keep_untouched_relation (write_mem1 <|proc:=0|> addr data) (assert_mode 16w) empty_unt``,
    RW_TAC (srw_ss()) [keep_untouched_relation_def, empty_unt_def]
       THEN FULL_SIMP_TAC (srw_ss()) [write_mem1_def, seqT_def, writeT_def, readT_def]
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def]
       THEN PAT_X_ASSUM ``!(addr:word32) (is_write:bool). X`` (fn th => ASSUME_TAC (SPECL [``addr:word32``, ``T:bool``] th))
       THEN ASSUME_TAC (SPEC ``addr:word32`` address_complete)
       THEN Cases_on `g=guest1`
       THEN Cases_on `g=guest2`
       THEN ASSUME_TAC you_and_me_thm
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN FIRST_PROVE
            [ASSUME_TAC (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE addr data)``] trivially_untouched_mmu_setup_lem)
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC access_violation_req
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC  (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE addr data)``, ``addr:word32``, ``data:word8``] malicious_write)
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF]
                THEN RW_TAC (srw_ss()) [],
             UNDISCH_ALL_TAC
                THEN CASE_TAC
                THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF]
                THEN (RW_TAC (srw_ss()) []
                      THEN EVAL_TAC
                      THEN RW_TAC (srw_ss()) [inequal_by_inequalities])]);



val write_mem1_similar_thm = store_thm (
    "write_mem1_similar_thm",
    ``!addr data. keep_similar_relation (write_mem1 <|proc:=0|> addr data) (assert_mode 16w) empty_sim``,
    REPEAT STRIP_TAC
       THEN ASSUME_TAC (SPECL [``addr:word32``, ``data:word8``] write_mem1_ut_thm)
       THEN FULL_SIMP_TAC (srw_ss()) [keep_similar_relation_def, assert_mode_def, keep_untouched_relation_def, empty_sim_def]
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss())  [write_mem1_def, seqT_def, readT_def]
       THEN (REPEAT CASE_TAC) THEN FULL_SIMP_TAC (srw_ss()) [writeT_def] THEN IMP_RES_TAC stay_similar_lem
       THEN PAT_X_ASSUM ``!(x:word8) (addr:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``addr:word32``] th)))
       THEN RW_TAC (srw_ss()) []
       THEN THROW_AWAY_TAC ``similar g a b ==> X``
       THEN FULL_SIMP_TAC (srw_ss()) [similar_def, equal_user_register_def]
       THEN (REPEAT STRIP_TAC)
       THEN RES_TAC
       THEN UNDISCH_MATCH_TAC ``!(addr:word32). X``
       THEN EVAL_TAC
       THEN (PROTECTED_RW_TAC ``(g:word32) = X`` ORELSE RW_TAC (srw_ss()) [])
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN IMP_RES_TAC mmu_requirement_accesses_update_lem
       THEN REPEAT (PAT_X_ASSUM ``!(x:word8) (addr:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``addr:word32``] th))))
       THEN ASSUME_TAC (SPECL [``(s1:arm_state) with accesses updated_by CONS (MEM_WRITE (addr:word32) (data:word8))``,
                   ``s1 with  <|memory updated_by (addr =+ data); accesses updated_by CONS (MEM_WRITE addr data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN ASSUME_TAC (SPECL [``(s2:arm_state) with accesses updated_by CONS (MEM_WRITE (addr:word32) (data:word8))``,
                   ``s2 with  <|memory updated_by (addr =+ data); accesses updated_by CONS (MEM_WRITE addr data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);


val write_mem1_empty_thm = store_thm(
    "write_mem1_empty_thm",
    ``!addr data. preserve_relation_mmu (write_mem1 <|proc:=0|> addr data) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    METIS_TAC [write_mem1_ut_thm, write_mem1_similar_thm, write_mem1_mode_thm, three_parts_thm]);

val write_mem1_thm = store_thm(
    "write_mem1_thm",
    ``!addr data. preserve_relation_mmu (write_mem1 <|proc:=0|> addr data) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
    METIS_TAC [write_mem1_empty_thm, empty_extras_lem]);


val read_mem_strict_thm = store_thm(
    "read_mem_strict_thm",
    ``!desc size. preserve_relation_mmu (read_mem <|proc:=0|> (desc,size)) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
                 `!a. preserve_relation_mmu ((λi. read_mem1 <|proc:=0|> ((desc.paddress) + (n2w i))) a) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim` by METIS_TAC [read_mem1_thm]
                 THEN ASSUME_TAC reflex_empty_sim_thm
                 THEN ASSUME_TAC (SPEC ``16w:word5`` reflex_strict_unt_thm)
                 THEN ASSUME_TAC trans_strict_unt_thm
                 THEN IMP_RES_TAC forT_preserves_user_relation_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


val read_mem_pmc_thm = store_thm(
    "read_mem_pmc_thm",
    ``!desc size. preserve_relation_mmu (read_mem <|proc:=0|> (desc,size)) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
                 `!a. preserve_relation_mmu ((λi. read_mem1 <|proc:=0|> ((desc.paddress) + (n2w i))) a) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar` by METIS_TAC [read_mem1_thm]
                 THEN ASSUME_TAC reflex_priv_mode_similar_thm
                 THEN ASSUME_TAC reflex_priv_mode_constraints_thm
                 THEN ASSUME_TAC trans_priv_mode_constraints_thm
                 THEN IMP_RES_TAC forT_preserves_user_relation_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


val read_mem_thm = save_thm("read_mem_thm", MATCH_MP extras_lem4 (SPEC_ALL read_mem_strict_thm));

Theorem write_mem_pmc_thm:
  !desc size value.
    preserve_relation_mmu (write_mem <|proc:=0|> (desc,size) value)
                          (assert_mode 16w) (assert_mode 16w)
                          priv_mode_constraints priv_mode_similar
Proof
  RW_TAC (srw_ss()) [write_mem_def, errorT_def, LET_DEF] THENL [
    RW_TAC (srw_ss()) [preserve_relation_mmu_def],
    RW_TAC (srw_ss()) [preserve_relation_mmu_def],
    ASSUME_TAC reflex_priv_mode_similar_thm
    THEN ASSUME_TAC reflex_priv_mode_constraints_thm
    THEN ASSUME_TAC trans_priv_mode_constraints_thm
    THEN IMP_RES_TAC
         (SPECL [“(assert_mode 16w):arm_state->bool”, “priv_mode_constraints”,
                 ``priv_mode_similar``] constT_unit_preserving_lem)
    THEN PAT_X_ASSUM ``preserve_relation_mmu X1 X2 X3 X4 X5``
                     (fn th => ASSUME_TAC (GEN ``u:(unit list)`` th))
    THEN ‘preserve_relation_mmu_abs ((\u:(unit list). return()))
          (assert_mode 16w) (assert_mode 16w) priv_mode_constraints
          priv_mode_similar’
      by FULL_SIMP_TAC (srw_ss()) [second_abs_lemma]
    THEN  `!x. preserve_relation_mmu ((λi. write_mem1 <|proc:=0|> ((desc.paddress) + (n2w i)) (EL i value)) x) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar` by METIS_TAC [write_mem1_thm]
    THEN IMP_RES_TAC forT_preserves_user_relation_thm
    THEN REPEAT (PAT_X_ASSUM ``!l h. X``
                 (fn th => ASSUME_TAC
                           (SPECL [“0:num”,
                                   “(LENGTH (value:word8 list) - 1):num”] th)))
    THEN REPEAT (PAT_X_ASSUM ``!x. X`` (fn th => IMP_RES_TAC th))
    THEN REPEAT (PAT_X_ASSUM ``~X`` (fn th => IMP_RES_TAC th))
    THEN IMP_RES_TAC seqT_preserves_relation_uu_thm
    THEN gs[]
  ]
QED


val write_mem_thm = save_thm("write_mem_thm", (MATCH_MP extras_lem2 (EQ_MP (SPEC ``(write_mem <|proc := 0|> (desc,size) value):(unit M)`` (INST_TYPE [alpha |-> Type `:unit`] empty_extras_lem)) (SPEC_ALL write_mem_pmc_thm))));



(************************************************************)
(***********************   Other    *************************)
(************************************************************)



val branch_to_empty_thm = store_thm(
    "branch_to_empty_thm",
    ``!u. preserve_relation_mmu (branch_to <|proc:=0|> addr) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [branch_to_def, write__reg_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
     THEN (TRY ((`reg <> RName_PC` by (Q.UNABBREV_TAC `user_regs` THEN FULL_SIMP_TAC (srw_ss()) []))))
     THEN (TRY (UNDISCH_TAC ``(reg:RName) <> RName_PC``))
     THEN EVAL_TAC
     THEN RW_TAC (srw_ss()) []
     THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with registers updated_by ((0,RName_PC) =+ addr)``, ``g:word32``] trivially_untouched_av_lem)
     THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with registers updated_by ((0,RName_PC) =+ addr)``, ``g:word32``] trivially_untouched_av_lem)
     THEN FULL_SIMP_TAC (srw_ss()) []
     THEN RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) []);
val branch_to_thm = save_thm("branch_to_thm", MATCH_MP extras_lem branch_to_empty_thm);



val write_monitor_empty_thm = store_thm(
    "write_monitor_empty_thm",
    ``!u. preserve_relation_mmu (write_monitor <|proc:=0|> vl) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [write_monitor_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with monitors := (vl:ExclusiveMonitors)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with monitors := (vl:ExclusiveMonitors)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val write_monitor_thm = save_thm("write_monitor_thm", MATCH_MP extras_lem write_monitor_empty_thm);


val clear_event_register_empty_thm = store_thm(
    "clear_event_register_empty_thm",
    ``!u. preserve_relation_mmu (clear_event_register <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [clear_event_register_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with event_register updated_by (0=+ F)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with event_register updated_by (0=+ F)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val clear_event_register_thm = save_thm("clear_event_register_thm", MATCH_MP extras_lem clear_event_register_empty_thm);



val wait_for_interrupt_empty_thm = store_thm(
    "wait_for_interrupt_empty_thm",
    ``!u. preserve_relation_mmu (wait_for_interrupt <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [wait_for_interrupt_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with interrupt_wait updated_by (0=+ T)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with interrupt_wait updated_by (0=+ T)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN EVAL_TAC);
val wait_for_interrupt_thm = save_thm("wait_for_interrupt_thm", MATCH_MP extras_lem wait_for_interrupt_empty_thm);



val send_event_empty_thm = store_thm(
    "send_event_empty_thm",
    ``!u. preserve_relation_mmu (send_event <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [send_event_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with event_register := K T``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with event_register := K T``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val send_event_thm = save_thm("send_event_thm", MATCH_MP extras_lem send_event_empty_thm);



val psrs_update_in_update_thm = store_thm(
    "psrs_update_in_update_thm",
    ``(((0:num),CPSR) =+ psrs (0,CPSR) with IT := (psrs (0,CPSR)).IT) psrs = psrs ``,
    RW_TAC (srw_ss())  [boolTheory.FUN_EQ_THM]
      THEN EVAL_TAC
      THEN RW_TAC (srw_ss())  [ARMpsr_component_equality]);



val take_undef_instr_exception_constlem = store_thm(
    "take_undef_instr_exception_constlem",
    ``(access_violation s) ==> (take_undef_instr_exception <|proc:=0|> s = ValueState () s)``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN `!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
       THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
       THEN FULL_SIMP_TAC (srw_ss()) []);


val take_undef_instr_exception_av_thm = store_thm(
    "take_undef_instr_exception_av_thm",
     ``preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (\s. (ARM_MODE s = 16w) /\ (access_violation s)) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
     MP_TAC reflex_priv_mode_constraints_thm
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, take_undef_instr_exception_constlem, assert_mode_def, untouched_refl, reflexive_comp_def]);


val take_undef_instr_exception_combine_thm = store_thm(
    "take_undef_instr_exception_combine_thm",
    ``(preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (\s. (ARM_MODE s = 16w) /\ (~access_violation s)) (assert_mode 27w) priv_mode_constraints priv_mode_similar) ==> (preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar)``,
    MP_TAC take_undef_instr_exception_av_thm
    THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def]
    THEN IMP_RES_TAC similarity_implies_equal_av_thm
    THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
    THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
    THEN Cases_on `access_violation s2` THEN FULL_SIMP_TAC (srw_ss()) []);


val trivial_true = store_thm("trivial_true", ``T``, FULL_SIMP_TAC (srw_ss()) []);



(****** mode mixtures *****)


val mode_mix_def = Define `mode_mix = (\s. (ARM_MODE s = 16w) \/ (ARM_MODE s = 17w) \/ (ARM_MODE s = 18w) \/ (ARM_MODE s = 27w) \/ (ARM_MODE s = 23w) \/ (ARM_MODE s = 19w))`;

val little_mode_mix_def = Define `little_mode_mix = (\s. (ARM_MODE s = 16w) \/  (ARM_MODE s = 17w) \/ (ARM_MODE s = 18w) \/ (ARM_MODE s = 27w) \/ (ARM_MODE s = 23w))`;


val pmc_12_upgrade = store_thm(
    "pmc_12_upgrade",
    ``!g s t. (ARM_MODE t <> 19w) ==> (priv_mode_constraints_v1 g s t = priv_mode_constraints_v2a g s t)``,
    RW_TAC (srw_ss()) [priv_mode_constraints_v2a_def]);


val pmc_31_downgrade = store_thm(
    "pmc_31_downgrade",
    ``!A inv1 inv2 uy.
        (preserve_relation_mmu (A) inv1 inv2 priv_mode_constraints_v3 uy)
       ==>
         preserve_relation_mmu (A) inv1 inv2 priv_mode_constraints_v1 uy``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, priv_mode_constraints_v2a_def, priv_mode_constraints_v3_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []);


val little_mode_mix_upgrade = store_thm(
    "little_mode_mix_upgrade",
    ``!A inv1 uf uy.
      (   preserve_relation_mmu (A) inv1 (assert_mode 16w)   uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 27w) uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 23w) uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 17w) uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 18w) uf uy)
       ==>
          preserve_relation_mmu (A) inv1 little_mode_mix uf uy``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, little_mode_mix_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [little_mode_mix_def]);

val mode_mix_upgrade = store_thm(
    "mode_mix_upgrade",
    ``!A inv1.
      (   preserve_relation_mmu (A) inv1 (assert_mode 16w)   priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 little_mode_mix     priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 27w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 23w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 19w) priv_mode_constraints_v2a priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 17w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 18w) priv_mode_constraints_v1 priv_mode_similar)
       ==>
          preserve_relation_mmu (A) inv1 mode_mix priv_mode_constraints_v2a priv_mode_similar``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, mode_mix_def, pmc_12_upgrade, little_mode_mix_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [pmc_12_upgrade]);


val mode_mix_const_upgrade = store_thm(
    "mode_mix_const_upgrade",
    ``!A uf uy.
          (!k. preserve_relation_mmu (A) (assert_mode k) (assert_mode k) uf uy)
       ==>
          preserve_relation_mmu (A) mode_mix mode_mix uf uy``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, mode_mix_def]
       THEN `(similar g s1 s2) ==> (ARM_MODE s1 = ARM_MODE s2)`
              by (EVAL_TAC THEN RW_TAC (srw_ss()) [])
       THEN SPEC_ASSUM_TAC (``!(ii:iiid). X``, [``<|proc:=0|>``])
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN METIS_TAC []);

val mode_mix_comb_16_thm = store_thm(
    "mode_mix_comb_16_thm",
    ``comb (assert_mode 16w) mode_mix mode_mix``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN METIS_TAC []);


val little_mode_mix_comb_16_thm = store_thm(
    "little_mode_mix_comb_16_thm",
    ``comb (assert_mode 16w) little_mode_mix little_mode_mix``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN METIS_TAC []);








val _ = export_theory();
