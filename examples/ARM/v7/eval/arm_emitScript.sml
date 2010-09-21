(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Use EmitML to generate an SML version of the ARM model               *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_evalTheory", "wordsLib", "pred_setSyntax", "emitLib",
            "EmitTeX", "patricia_emitTheory", "option_emitTheory",
            "set_emitTheory", "int_emitTheory", "rich_list_emitTheory"];
*)

open HolKernel boolLib bossLib Parse wordsLib;

open arm_coretypesTheory arm_astTheory arm_seq_monadTheory
     arm_decoderTheory arm_opsemTheory armTheory arm_evalTheory;

open emitLib set_emitTheory int_emitTheory rich_list_emitTheory words_emitTheory
     patricia_emitTheory;

val _ = new_theory "arm_emit";

(* ------------------------------------------------------------------------ *)

val bytes = Q.prove(
  `!w n.
     bytes (w,n) =
       if n = 1 then
         [w2w w]
       else if n = 2 then
         [(7 >< 0) w; (15 >< 8) w]
       else if n = 4 then
         [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w]
       else
         FAIL bytes ^(mk_var("n not 1, 2 or 4",bool)) (w,n)`,
  SRW_TAC [] [bytes_def, combinTheory.FAIL_THM]);

val SUM = Q.prove(
  `!n f. SUM n f = if n = 0 then 0 else SUM (n - 1) f + f (n - 1)`,
  Cases THEN SRW_TAC [] [sum_numTheory.SUM_def]);

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val parallel_add_sub_op1 = Q.prove(
  `!w. parallel_add_sub_op1 w =
         case w
         of 0b01w -> Parallel_normal
         || 0b10w -> Parallel_saturating
         || 0b11w -> Parallel_halving
         || _ -> FAIL parallel_add_sub_op1 ^(mk_var("can't decode",bool)) w`,
  Cases THEN FULL_SIMP_TAC (srw_ss())
    [parallel_add_sub_op1_def, LESS_THM, combinTheory.FAIL_THM]);

val parallel_add_sub_op2 = Q.prove(
  `!w. parallel_add_sub_op2 w =
         case w
         of 0b000w -> Parallel_add_16
         || 0b001w -> Parallel_add_sub_exchange
         || 0b010w -> Parallel_sub_add_exchange
         || 0b011w -> Parallel_sub_16
         || 0b100w -> Parallel_add_8
         || 0b111w -> Parallel_sub_8
         || _ -> FAIL parallel_add_sub_op2 ^(mk_var("can't decode",bool)) w`,
  Cases THEN FULL_SIMP_TAC (srw_ss())
    [parallel_add_sub_op2_def, LESS_THM, combinTheory.FAIL_THM]);

val parallel_add_sub_thumb_op2 = Q.prove(
  `!w. parallel_add_sub_thumb_op2 w =
         case w
         of 0b001w -> Parallel_add_16
         || 0b010w -> Parallel_add_sub_exchange
         || 0b110w -> Parallel_sub_add_exchange
         || 0b101w -> Parallel_sub_16
         || 0b000w -> Parallel_add_8
         || 0b100w -> Parallel_sub_8
         || _ -> FAIL parallel_add_sub_thumb_op2
                   ^(mk_var("can't decode",bool)) w`,
  Cases THEN FULL_SIMP_TAC (srw_ss())
    [parallel_add_sub_thumb_op2_def, LESS_THM, combinTheory.FAIL_THM]);

(* Expand out data_processing_instr wrt ``n2w opc`` *)
local
  val dp_thm = ONCE_REWRITE_RULE [LET_THM]
                 (fetch "arm_opsem" "data_processing_instr")
  fun mk_dp_opc (i,tm) =
        let val opc = wordsSyntax.mk_wordii(i, 4) in
          boolSyntax.mk_cond
            (boolSyntax.mk_eq (``opc:word4``,opc),
            ``arm_opsem$data_processing_instr ii enc
                (Data_Processing ^opc setflags n d mode1)``,tm)
        end
  val tm = List.foldr mk_dp_opc ``ARB:unit M`` (List.tabulate(16,I))
  val thm = Q.prove(
              `data_processing_instr ii enc
                 (Data_Processing opc setflags n d mode1) = ^tm`,
              SRW_TAC [] [] THEN Cases_on `opc`
                THEN FULL_SIMP_TAC (srw_ss()) [LESS_THM]
                THEN FULL_SIMP_TAC std_ss [])
  val pos = Lib.index (Lib.equal "data_processing_instr")
              arm_opsemTheory.instruction_list
  val data_processing_instr =
        CONV_RULE (RHS_CONV
           (SIMP_CONV (srw_ss()) [dp_thm, data_processing_alu_def]
              THENC DEPTH_CONV (pairLib.LET_SIMP_CONV false))) thm
  val l = map (fetch "arm_opsem") arm_opsemTheory.instruction_list
in
  val instruction_list =
        let val (l,r) = Lib.split_after pos l in
          l @ [data_processing_instr] @ (tl r)
        end
end;

val i2bits_itself_def = Define`
  i2bits_itself (i,N,(:'a)) = (i2bits (i,N)) : 'a word`;

val signed_sat_itself_def = Define`
  signed_sat_itself (i,N,(:'a)) = (signed_sat (i,N)) : 'a word`;

val unsigned_sat_itself_def = Define`
  unsigned_sat_itself (i,N,(:'a)) = (unsigned_sat (i,N)) : 'a word`;

val signed_sat_q_itself_def = Define`
  signed_sat_q_itself (i,N,(:'a)) = (signed_sat_q (i,N)) : 'a word # bool`;

val unsigned_sat_q_itself_def = Define`
  unsigned_sat_q_itself (i,N,(:'a)) = (unsigned_sat_q (i,N)) : 'a word # bool`;

val _ = type_pp.pp_num_types := false;
val _ = type_pp.pp_array_types := false;
val _ = temp_disable_tyabbrev_printing "proc";
val _ = temp_disable_tyabbrev_printing "FullAddress";
val _ = temp_disable_tyabbrev_printing "cpid";
val _ = temp_type_abbrev("ARMextensions_set", ``:ARMextensions set``);
val _ = temp_type_abbrev("word4", ``:bool[4]``);
val _ = temp_type_abbrev("word32", ``:bool[32]``);
val _ = temp_clear_overloads_on "UInt"
val _ = temp_clear_overloads_on "SInt"
val _ = temp_overload_on("w2i", ``integer_word$w2i``);

fun f x = [QUOTE (trace ("Unicode",0) EmitTeX.datatype_thm_to_string x)]

val n2w_rule = Q.SPEC `n2w m`

val extension_rule = SIMP_RULE (srw_ss()) [thumb2_support_def];

val int_rule = SIMP_RULE std_ss (COND_RATOR :: map GSYM
  [int_emitTheory.i2w_itself_def,
   i2bits_itself_def, signed_sat_itself_def, unsigned_sat_itself_def,
   signed_sat_q_itself_def, unsigned_sat_q_itself_def]);

val cons_rule = ONCE_REWRITE_RULE [GSYM (ETA_CONV ``\l. CONS f l``)];

fun mk_word n =
let val s = Int.toString n in
  MLSIG ("type word" ^ s ^ " = wordsML.word" ^ s)
end;

val _ = emitML (!Globals.emitMLDir) ("arm",
  [OPEN  ["num", "set", "string", "fcp", "bit", "words"],
   MLSIG "type num = numML.num",
   MLSIG "type int = intML.int",
   MLSIG "type 'a ptree = 'a patriciaML.ptree",
   MLSIG "type 'a set = 'a setML.set",
   MLSIG "type 'a itself = 'a fcpML.itself",
   MLSIG "type 'a bit0 = 'a fcpML.bit0",
   MLSIG "type 'a bit1 = 'a fcpML.bit1",
   MLSIG "type 'a word = 'a wordsML.word",
   MLSIG "type ('a,'b) cart = ('a,'b) fcpML.cart",
   MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum",
   MLSTRUCT "type int = intML.int",
   MLSTRUCT "type 'a ptree = 'a patriciaML.ptree"] @
  map mk_word [2,3,4,5,6,8,12,16,24,32,64] @
  [DATATYPE (f datatype_ARMextensions),
   MLSIG    "type ARMextensions_set = ARMextensions set",
   MLSTRUCT "type ARMextensions_set = ARMextensions set"] @
  map (DATATYPE o f)
    [datatype_iiid, datatype_RName, datatype_PSRName, datatype_ARMpsr,
     datatype_CP14reg, datatype_CP15sctlr, datatype_CP15scr,
     datatype_CP15nsacr, datatype_CP15vbar, datatype_CP15reg,
     datatype_coproc_state, datatype_memory_access, datatype_ARMarch,
     datatype_ARMinfo, datatype_SRType, datatype_InstrSet, datatype_Encoding,
     datatype_MemType, datatype_MemoryAttributes, datatype_AddressDescriptor,
     datatype_MBReqDomain, datatype_MBReqTypes, datatype_addressing_mode1,
     datatype_addressing_mode2, datatype_addressing_mode3, datatype_hint,
     datatype_parallel_add_sub_op1, datatype_parallel_add_sub_op2,
     datatype_branch_instruction, datatype_data_processing_instruction,
     datatype_status_access_instruction, datatype_load_store_instruction,
     datatype_miscellaneous_instruction, datatype_coprocessor_instruction,
     datatype_ARMinstruction] @
  [MLSIG    "type CPinstruction = word4 * (word4 * coprocessor_instruction)",
   MLSTRUCT "type CPinstruction = word4 * (word4 * coprocessor_instruction)",
   MLSIG    "type exclusive_triple = word32 * (iiid * num)",
   MLSTRUCT "type exclusive_triple = word32 * (iiid * num)",
   MLSIG    "type exclusive_state = (num -> word32 set) * (word32 * num) set",
   MLSTRUCT "type exclusive_state = (num -> word32 set) * (word32 * num) set",
   MLSIG    "type 'a ExclusiveM = exclusive_state -> ('a * exclusive_state)",
   MLSTRUCT "type 'a ExclusiveM = exclusive_state -> ('a * exclusive_state)",
   MLSIG    "type 'a CoprocessorM = coproc_state -> ('a * coproc_state)",
   MLSTRUCT "type 'a CoprocessorM = coproc_state -> ('a * coproc_state)"] @
  map (DATATYPE o f)
    [datatype_ExclusiveMonitors, datatype_Coprocessors,
     datatype_arm_state, datatype_error_option] @
  [MLSIG    "type 'a M = arm_state -> ('a, arm_state) error_option",
   MLSTRUCT "type 'a M = arm_state -> ('a, arm_state) error_option"] @
  map (DEFN o SIMP_RULE (srw_ss())
         [Q.ISPEC `FST` COND_RAND, combinTheory.o_THM,
          i2bits_def, signed_sat_def, unsigned_sat_def,
          signed_sat_q_def, unsigned_sat_q_def])
    [INST_TYPE [alpha |-> ``:8``] integer_wordTheory.i2w_def, i2bits_itself_def,
     signed_sat_itself_def, unsigned_sat_itself_def,
     signed_sat_q_itself_def, unsigned_sat_q_itself_def] @
  [DEFN data_processing_thumb2_unpredictable_def] @
  map (DEFN o int_rule)
   ([IMP_DISJ_THM,
     (* arm_coretypes *)
     n2w_rule (Q.SPEC `n` sign_extend_def), n2w_rule align_def, aligned_def,
     n2w_rule count_leading_zeroes_def,
     n2w_rule lowest_set_bit_compute, SUM, bit_count_upto_def,
     n2w_rule bit_count_def, zero_extend32_def,
     sign_extend32_def, word16_def, word32_def, word64_def,
     bytes, n2w_rule LSL_C_def, LSR_C_def, n2w_rule ASR_C_def,
     n2w_rule ROR_C_def, RRX_C_def, LSL_def, LSR_def, ASR_def, ROR_def,
     RRX_def, ITAdvance_def, decode_psr_def, encode_psr_def, version_number_def,

     (* arm_ast *)
     is_mode1_immediate_def, is_mode2_immediate_def, is_mode3_immediate_def,

     (* arm_seq_monad *)
     constE_def, seqE_def, constC_def, seqC_def, constT_def,
     errorT_def, seqT_def, parT_def, lockT_def, condT_def,
     forT_def, readT_def, writeT_def, read_info_def,
     read_arch_def, read_extensions_def, read__reg_def,
     write__reg_def, read__psr_def, write__psr_def,
     read_scr_def, write_scr_def, read_nsacr_def,
     read_teehbr_def, read_sctlr_def, read_cpsr_def, write_cpsr_def,
     read_isetstate_def, write_isetstate_def,
     have_security_ext, have_jazelle, have_thumbEE, bad_mode_def, read_spsr_def,
     write_spsr_def, current_mode_is_priviledged_def,
     current_mode_is_user_or_system_def, is_secure_def,
     read_vbar_def, read_mvbar_def, current_instr_set_def,
     select_instr_set_def, RBankSelect_def, RfiqBankSelect_def,
     LookUpRName_def, read_reg_mode_def, write_reg_mode_def,
     read_pc_def, pc_store_value_def, read_reg_def,
     write_reg_def, branch_to_def, increment_pc_def,
     big_endian_def, translate_address_def, read_monitor_def,
     write_monitor_def, cons_rule read_mem1_def, cons_rule write_mem1_def,
     read_mem_def, write_mem_def, read_memA_with_priv_def,
     write_memA_with_priv_def, read_memU_with_priv_def,
     write_memU_with_priv_def, read_memA_def,
     write_memA_def, read_memA_unpriv_def, write_memA_unpriv_def,
     read_memU_def, write_memU_def, read_memU_unpriv_def,
     write_memU_unpriv_def, data_memory_barrier_def,
     data_synchronization_barrier_def,
     instruction_synchronization_barrier_def,
     hint_preload_data_for_write_def, hint_preload_data_def,
     hint_preload_instr_def, hint_yield_def, hint_debug_def,
     clear_event_register_def, event_registered_def,
     send_event_def, wait_for_event_def, wait_for_interrupt_def,
     clear_wait_for_interrupt_def, waiting_for_interrupt_def,
     set_exclusive_monitors_def, exclusive_monitors_pass_def,
     clear_exclusive_local_def, read_coprocessors_def,
     write_coprocessors_def, coproc_accepted_def,
     coproc_internal_operation_def, coproc_send_loaded_words_def,
     coproc_get_words_to_store_def, coproc_send_one_word_def,
     coproc_get_one_word_def, coproc_send_two_words_def,
     coproc_get_two_words_def,

     (* arm_opsem *)
     unaligned_support_def, arch_version_def, read_reg_literal_def,
     read_flags_def, write_flags_def, read_cflag_def, set_q_def, read_ge_def,
     write_ge_def, write_e_def, extension_rule IT_advance_def,
     cpsr_write_by_instr_def, spsr_write_by_instr_def,
     branch_write_pc_def, bx_write_pc_def, load_write_pc_def,
     alu_write_pc_def, decode_imm_shift_def, decode_reg_shift_def,
     shift_c_def, shift_def, arm_expand_imm_c_def, thumb_expand_imm_c_def,
     arm_expand_imm_def,
     address_mode1_def, address_mode2_def, address_mode3_def,
     address_mode5_def,
     signed_parallel_add_sub_16_def, signed_normal_add_sub_16_def,
     signed_saturating_add_sub_16_def, signed_halving_add_sub_16_def,
     signed_parallel_add_sub_8_def, signed_normal_add_sub_8_def,
     signed_saturating_add_sub_8_def, signed_halving_add_sub_8_def,
     unsigned_parallel_add_sub_16_def, unsigned_normal_add_sub_16_def,
     unsigned_saturating_add_sub_16_def, unsigned_halving_add_sub_16_def,
     unsigned_parallel_add_sub_8_def, unsigned_normal_add_sub_8_def,
     unsigned_saturating_add_sub_8_def, unsigned_halving_add_sub_8_def,
     parallel_add_sub_def, barrier_option_def, exc_vector_base_def,
     take_undef_instr_exception_def, take_svc_exception_def,
     take_smc_exception_def, take_prefetch_abort_exception_def,
     integer_zero_divide_trapping_enabled_def, null_check_if_thumbEE_def] @
    instruction_list @
    [condition_passed_def, branch_instruction_def,
     data_processing_instruction_def, status_access_instruction_def,
     load_store_instruction_def, miscellaneous_instruction_def,
     coprocessor_instruction_def, arm_instr_def,

     (* arm_decode and arm_eval *)
     hint_decode_def, parallel_add_sub_op1, parallel_add_sub_op2,
     parallel_add_sub_thumb_op2, parallel_add_sub_decode_def,
     parallel_add_sub_thumb_decode_def, InITBlock_def, LastInITBlock_def,
     arm_decode_def, extension_rule thumb_decode_def, thumbee_decode_def,
     thumb2_decode_aux1_def, thumb2_decode_aux2_def, thumb2_decode_aux3_def,
     thumb2_decode_aux4_def, thumb2_decode_aux5_def, thumb2_decode_aux6_def,
     thumb2_decode_aux7_def, thumb2_decode_aux8_def, thumb2_decode_aux9_def,
     extension_rule thumb2_decode_def, proc_def, ptree_read_word_def,
     ptree_read_halfword_def, fetch_arm_def, fetch_thumb_def, attempt_def,
     actual_instr_set_def, fetch_instruction_def]));

(* ------------------------------------------------------------------------ *)

val _ = export_theory ();
