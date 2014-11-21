(*  The actual instructions   *)
(*  Author: Oliver Schwarz    *)

open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory;
open tacticsLib ARM_proverLib ARM_prover_toolsLib;
open user_lemma_basicsTheory user_lemma_primitive_operationsTheory;
open wordsTheory wordsLib;

val _ =  new_theory("user_lemma_instructions");

val _ = temp_overload_on ("return", ``constT``);
val _ = diminish_srw_ss ["one"]
val _ = augment_srw_ss [rewrites [oneTheory.FORALL_ONE]]

val _ = goalStack.chatting := !Globals.interactive

(* import simplist *)
val _ = simp_thms_list := (CONJUNCTS simplist_export_thm);


(************************************************************)
(*****************  A. Status Accesses   ********************)
(************************************************************)


val _ = g `preserve_relation_mmu (status_access_instruction <|proc:=0|> (enc, inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
val _ = e (Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(* status to register *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 4;
(* register to status *)
val _ = go_on 1;
(* immediate to status *)
val _ = go_on 1;
(* change processor state *)
val _ = go_on 1;
(* set endianness *)
val _ = go_on 1;
val status_access_instruction_comb_thm = save_comb_thm ("status_access_instruction_comb_thm", top_thm(), ``status_access_instruction``);


(************************************************************)
(**********************  B. Branching   *********************)
(************************************************************)


val _ = g `preserve_relation_mmu (branch_link_exchange_imm_instr <|proc := 0|>  e  (Branch_Link_Exchange_Immediate b b0 c)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints  priv_mode_similar`;
val _ = e(Cases_on `b0` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val _ = e(Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 4;
val branch_link_exchange_imm_instr_comb_thm = save_comb_thm("branch_link_exchange_imm_instr_comb_thm", top_thm(), ``branch_link_exchange_imm_instr``);



val _ = g `preserve_relation_mmu (branch_instruction <|proc := 0|> (e,i)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints  priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [branch_instruction_def]);
val _ = e(Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 10;
val branch_instruction_comb_thm = save_comb_thm("branch_instruction_comb_thm", top_thm(), ``branch_instruction``);



(************************************************************)
(*******************   C. Memory Access  ********************)
(************************************************************)


val _ = g `preserve_relation_mmu
  ((current_mode_is_user_or_system <|proc := 0|>
      ||| current_instr_set <|proc := 0|>) >>=
   (λ(is_user_or_system,iset).
      if is_user_or_system ∨ (iset = InstrSet_ThumbEE) then
        errorT "store_return_state_instr: unpredictable"
      else
        (read_reg_mode <|proc := 0|> (13w,c)
           ||| read_reg <|proc := 0|> 14w
           ||| read_spsr <|proc := 0|>) >>=
        (λ(base,lr,spsr).
           (increment_pc <|proc := 0|> enc
              ||| write_memA <|proc := 0|>
                    (if b ⇔ b0 then
                       (if b0 then base else base + 0xFFFFFFF8w) + 4w
                     else if b0 then
                       base
                     else
                       base + 0xFFFFFFF8w,4) (bytes (lr,4))
              ||| write_memA <|proc := 0|>
                    ((if b ⇔ b0 then
                        (if b0 then base else base + 0xFFFFFFF8w) + 4w
                      else if b0 then
                        base
                      else
                        base + 0xFFFFFFF8w) + 4w,4)
                    (bytes (encode_psr spsr,4))
              ||| condT b1
                    (write_reg_mode <|proc := 0|> (13w,c)
                       (if b0 then
                          base + 8w
                        else
                          base + 0xFFFFFFF8w))) >>=
           (λ(u1,u2,u3,u4). return ())))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints  priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [user_simp_par_or_eqv_rel_lem]);
val _ = go_on 1;
val store_return_state_instr_help_let_thm = save_thm ("store_return_state_instr_help_let_thm", top_thm());


val store_return_state_instr_help_let_comb_thm = store_thm ("store_return_state_instr_help_let_comb_thm",
    ``preserve_relation_mmu
     ((current_mode_is_user_or_system <|proc := 0|>
      ||| current_instr_set <|proc := 0|>) >>=
   (λ(is_user_or_system,iset).
      if is_user_or_system ∨ (iset = InstrSet_ThumbEE) then
        errorT "store_return_state_instr: unpredictable"
      else
        (read_reg_mode <|proc := 0|> (13w,c)
           ||| read_reg <|proc := 0|> 14w
           ||| read_spsr <|proc := 0|>) >>=
        (λ(base,lr,spsr).
           (increment_pc <|proc := 0|> enc
              ||| write_memA <|proc := 0|>
                    (if b ⇔ b0 then
                       (if b0 then base else base + 0xFFFFFFF8w) + 4w
                     else if b0 then
                       base
                     else
                       base + 0xFFFFFFF8w,4) (bytes (lr,4))
              ||| write_memA <|proc := 0|>
                    ((if b ⇔ b0 then
                        (if b0 then base else base + 0xFFFFFFF8w) + 4w
                      else if b0 then
                        base
                      else
                        base + 0xFFFFFFF8w) + 4w,4)
                    (bytes (encode_psr spsr,4))
              ||| condT b1
                    (write_reg_mode <|proc := 0|> (13w,c)
                       (if b0 then
                          base + 8w
                        else
                          base + 0xFFFFFFF8w))) >>=
           (λ(u1,u2,u3,u4). return ()))))
      (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
     ASSUME_TAC store_return_state_instr_help_let_thm
        THEN ASSUME_TAC (SPECL [``16w:word5``, ``27w:word5``] comb_mode_thm)
        THEN ASSUME_TAC (SPECL [``(assert_mode 16w):(arm_state->bool)``,
                     ``(assert_mode 27w):(arm_state->bool)``,
                     ``(comb_mode 16w 27w):(arm_state->bool)``,
                     ``(assert_mode 16w):(arm_state->bool)``] (INST_TYPE [alpha |-> type_of(``()``)] preserve_relation_comb_v2_thm))
        THEN RES_TAC);
val _ =  add_to_simplist store_return_state_instr_help_let_comb_thm;




val store_multiple_part = ``(λ(base,cpsr).
                (let mode = if system then 16w else cpsr.M and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if addr then base else base − length
                 in
                 let start_address =
                       if indx ⇔ addr then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if addr then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ())))):bool[32] # ARMpsr -> unit M``;


val store_multiple_part_simp = store_thm(
    "store_multiple_part_simp",
    `` (preserve_relation_mmu(
         (read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>=
             (λ(base,cpsr).
                (let mode = if system then 16w else cpsr.M and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if addr then base else base − length
                 in
                 let start_address =
                       if indx ⇔ addr then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if addr then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ()))))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           =
         (preserve_relation_mmu
           ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>=
             (λ(base,cpsr).
                (let mode = if system then 16w else 16w and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if addr then base else base − length
                 in
                 let start_address =
                       if indx ⇔ addr then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if addr then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ()))))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)``,
    FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]
       THEN EQ_TAC
       THEN (REPEAT STRIP_TAC)
       THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``n:word4``, store_multiple_part] (INST_TYPE [alpha |-> type_of(``()``)] read_reg_read_cpsr_par_effect_lem))
       THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``n:word4``, store_multiple_part] (INST_TYPE [alpha |-> type_of(``()``)] read_reg_read_cpsr_par_effect_lem))
       THEN RES_TAC
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []);




val _ = g `!n. preserve_relation_mmu
       ((read_reg <|proc := 0|> n ||| read_cpsr <|proc := 0|>) >>=
        (λ(base,cpsr).
           forT 0 14
             (λi.
                condT ((c0:word16) ' i)
                  (if (i = (w2n n)) ∧ b2 ∧ i ≠ lowest_set_bit c0 then
                     write_memA <|proc := 0|>
                       (n2w (4 * (bit_count_upto (w2n n + 1) c0 − 1)) +
                        if b ⇔ b0 then
                          (if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0)) + 4w
                        else if b0 then
                          base
                        else
                          base + -1w * n2w (4 * bit_count c0),4)
                       BITS32_UNKNOWN
                   else
                     read_reg_mode <|proc := 0|>
                       (n2w i,if b1 then 16w else cpsr.M) >>=
                     (λd.
                        write_memA <|proc := 0|>
                          (n2w (4 * (bit_count_upto (i + 1) c0 − 1)) +
                           if b ⇔ b0 then
                             (if b0 then
                                base
                              else
                                base + -1w * n2w (4 * bit_count c0)) +
                             4w
                           else if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0),4)
                          (bytes (d,4))))) >>=
           (λunit_list.
              (condT (c0 ' 15)
                 (pc_store_value <|proc := 0|> >>=
                  (λpc.
                     write_memA <|proc := 0|>
                       (n2w (4 * (bit_count_upto 16 c0 − 1)) +
                        if b ⇔ b0 then
                          (if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0)) + 4w
                        else if b0 then
                          base
                        else
                          base + -1w * n2w (4 * bit_count c0),4)
                       (bytes (pc,4))))
                 ||| increment_pc <|proc := 0|> enc
                 ||| condT b2
                       (if b0 then
                          write_reg <|proc := 0|> n
                            (base + n2w (4 * bit_count c0))
                        else
                          write_reg <|proc := 0|> n
                            (base + -1w * n2w (4 * bit_count c0)))) >>=
              (λ(u1,u2,u3). return ())))) (assert_mode 16w)  (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``b2:bool``, ``b1:bool``, ``c0:word16``, ``n:word4``, ``b:bool``, ``enc:Encoding``, ``b0:bool``] (GEN_ALL store_multiple_part_simp)));
val _ = e(FULL_SIMP_TAC (srw_ss()) [LET_DEF]);
val _ = go_on 1;
val store_multiple_part_thm = save_thm ("store_multiple_part_thm", top_thm());
val store_multiple_part_thm_n = save_thm ("store_multiple_part_thm_n", (SPEC ``n:word4`` store_multiple_part_thm));
val store_multiple_part_thm_13 = save_thm ("store_multiple_part_thm_13", (SIMP_RULE (srw_ss()) [] (SPEC ``13w:word4`` store_multiple_part_thm)));
val store_multiple_part_thm_15 = save_thm ("store_multiple_part_thm_15", (SIMP_RULE (srw_ss()) [] (SPEC ``15w:word4`` store_multiple_part_thm)));

val _ = add_to_simplist store_multiple_part_thm;
val _ = add_to_simplist store_multiple_part_thm_n;
val _ = add_to_simplist store_multiple_part_thm_13;
val _ = add_to_simplist store_multiple_part_thm_15;


val load_multiple_part =
      ``(λ(base,cpsr).
           forT 0 14
             (λi.
                condT (c0 ' i)
                  (read_memA <|proc := 0|>
                     (n2w (4 * (bit_count_upto (i + 1) c0 − 1)) +
                      if b ⇔ b0 then
                        (if b0 then
                           base
                         else
                           base + -1w * n2w (4 * bit_count c0)) + 4w
                      else if b0 then
                        base
                      else
                        base + -1w * n2w (4 * bit_count c0),4) >>=
                   (λd.
                      write_reg_mode <|proc := 0|>
                        (n2w i,if b1 ∧ ¬c0 ' 15 then 16w else cpsr.M)
                        (word32 d)))) >>=
           (λunit_list.
              condT b2
                (if (¬(c0:word16) ' (w2n n)) then
                   if b0 then
                     write_reg <|proc := 0|> n
                       (base + n2w (4 * bit_count c0))
                   else
                     write_reg <|proc := 0|> n
                       (base + -1w * n2w (4 * bit_count c0))
                 else
                   write_reg <|proc := 0|> n UNKNOWN) >>=
              (λu.
                 if c0 ' 15 then
                   read_memA <|proc := 0|>
                     (n2w (4 * (bit_count_upto 16 c0 − 1)) +
                      if b ⇔ b0 then
                        (if b0 then
                           base
                         else
                           base + -1w * n2w (4 * bit_count c0)) + 4w
                      else if b0 then
                        base
                      else
                        base + -1w * n2w (4 * bit_count c0),4) >>=
                   (λd.
                      if b1 then
                        current_mode_is_user_or_system <|proc := 0|> >>=
                        (λis_user_or_system.
                           if is_user_or_system then
                             errorT "load_multiple_instr: unpredictable"
                           else
                             read_spsr <|proc := 0|> >>=
                             (λspsr.
                                cpsr_write_by_instr <|proc := 0|>
                                  (encode_psr spsr,15w,T) >>=
                                (λu.
                                   branch_write_pc <|proc := 0|>
                                     (word32 d))))
                      else
                        load_write_pc <|proc := 0|> (word32 d))
                 else
                   increment_pc <|proc := 0|> enc))):(word32 # ARMpsr -> unit M)``;


val _ = g `!n. preserve_relation_mmu
       ((read_reg <|proc := 0|> n ||| read_cpsr <|proc := 0|>) >>= (^load_multiple_part)) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``n:word4``, load_multiple_part, ``(assert_mode 16w)``, ``priv_mode_constraints``, ``priv_mode_similar``] (INST_TYPE [alpha |-> Type `:unit`] cpsr_par_simp_rel_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val load_multiple_part_thm = top_thm();
val load_multiple_part_thm_13 = save_thm ("load_multiple_part_thm_13", (SIMP_RULE (srw_ss()) [] (SPEC ``13w:word4`` load_multiple_part_thm)));
val load_multiple_part_thm_15 = save_thm ("load_multiple_part_thm_15", (SIMP_RULE (srw_ss()) [] (SPEC ``15w:word4`` load_multiple_part_thm)));
val _ = add_to_simplist load_multiple_part_thm;
val _ = add_to_simplist load_multiple_part_thm_13;
val _ = add_to_simplist load_multiple_part_thm_15;




val _ = g `preserve_relation_mmu (load_store_instruction <|proc:=0|> (enc,inst))(assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [load_store_instruction_def]);
val _ = e(Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(* load *)
val _ = go_on_p 1;
(* store *)
val _ = go_on_p 1;
(* load halfword *)
val _ = go_on_p 1;
(* store halfword *)
val _ = go_on_p 1;
(* load dual *)
val _ = go_on_p 1;
(* store dual *)
val _ = go_on_p 1;
(* load multiple *)
val _ = go_on_p 1;
(* store multiple *)
val _ = go_on_p 1;
(* load exclusive *)
val _ = go_on_p 1;
(* store exclusive *)
val _ = go_on_p 1;
(* load exclusive doubleword *)
val _ = go_on_p 1;
(* store exclusive doubleword *)
val _ = go_on_p 1;
(* load exclusive halfword *)
val _ = go_on_p 1;
(* store exclusive halfword *)
val _ = go_on_p 1;
(* load exclusive byte *)
val _ = go_on_p 1;
(* store exclusive byte *)
val _ = go_on_p 1;
(* store return state *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [store_return_state_instr_def, instruction_def, run_instruction_def, LET_DEF]);
val _ = go_on_p 1;
(* return from exception *)
val _ = go_on_p 1;
val load_store_instruction_comb_thm = save_comb_thm("load_store_instruction_comb_thm", top_thm(), ``load_store_instruction``);




(************************************************************)
(*******************  D. Coprocessors   *********************)
(************************************************************)


val _ = g `preserve_relation_mmu (coprocessor_instruction <|proc:=0|> (enc,cond,inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [coprocessor_instruction_def]);
val _ = e((REPEAT (CASE_TAC)) THEN FULL_SIMP_TAC (srw_ss()) [coprocessor_load_instr_def, coprocessor_store_instr_def, coprocessor_register_to_arm_instr_def, arm_register_to_coprocessor_instr_def, coprocessor_register_to_arm_two_instr_def, arm_register_to_coprocessor_two_instr_def, coprocessor_data_processing_instr_def, LET_DEF]);
val _ = go_on_p 7;
val coprocessor_instruction_comb_thm = save_comb_thm("coprocessor_instruction_comb_thm", top_thm(), ``coprocessor_instruction``);



(************************************************************)
(******************  E. Data Processing  ********************)
(************************************************************)

(* write flags for triples *)

val _ = g `preserve_relation_mmu (write_flags <|proc := 0|>  (a,b,c)) (assert_mode 16w)  (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
val _ = e(pairLib.PairCases_on `c`);
val _ = go_on 1;
val write_flags_triple_thm = top_thm();
val _ = add_to_simplist write_flags_triple_thm;

(* data processing instr *)

val data_processing_pre_part = ``((if ((c:word4) = 13w) ∨ (c = 15w) ∧ (enc ≠ Encoding_Thumb2 ∨ (c0 = 15w)) then
            return 0w
          else
            read_reg <|proc := 0|> c0)
           ||| address_mode1 <|proc := 0|> (enc = Encoding_Thumb2) a
           ||| read_flags <|proc := 0|>)
   : ((word32 # (word32 # bool) # bool # bool #bool # bool) M)``;
val data_processing_pre_part_thm = prove_and_save_e(``^data_processing_pre_part``, "data_processing_pre_part_thm");


val data_processing_core_part = ``(λ((rn :bool[32]),((shifted :bool[32]),(C_shift :bool)),(N :bool),
     (Z :bool),(C :bool),(V :bool)).
     ((if ((3 :num) -- (2 :num)) (c :bool[4]) = (2w :bool[4]) then
         increment_pc <|proc := (0 :num)|> enc
       else if (c1 :bool[4]) = (15w :bool[4]) then
         if (b :bool) then
           read_spsr <|proc := (0 :num)|> >>=
           (λ(spsr :ARMpsr).
              cpsr_write_by_instr <|proc := (0 :num)|>
                (encode_psr spsr,(15w :bool[4]),T) >>=
              (λ(u :unit).
                 branch_write_pc <|proc := (0 :num)|>
                   (FST (data_processing_alu c rn shifted C))))
         else
           alu_write_pc <|proc := (0 :num)|>
             (FST (data_processing_alu c rn shifted C))
       else
         (increment_pc <|proc := (0 :num)|> enc
            ||| write_reg <|proc := (0 :num)|> c1
                  (FST (data_processing_alu c rn shifted C))) >>=
         (λ((u1 :unit),(u2 :unit)). return ()))
        ||| if
              b ∧
              (c1 ≠ (15w :bool[4]) ∨
               (((3 :num) -- (2 :num)) c = (2w :bool[4])))
            then
              if
                (c ' (2 :num) ∨ c ' (1 :num)) ∧
                (¬c ' (3 :num) ∨ ¬c ' (2 :num))
              then
                write_flags <|proc := (0 :num)|>
                  (word_msb (FST (data_processing_alu c rn shifted C)),
                   FST (data_processing_alu c rn shifted C) =
                   (0w
                     :bool[32]),
                   SND (data_processing_alu c rn shifted C))
              else
                write_flags <|proc := (0 :num)|>
                  (word_msb (FST (data_processing_alu c rn shifted C)),
                   FST (data_processing_alu c rn shifted C) =
                   (0w
                     :bool[32]),C_shift,V)
            else
              return ()) >>= (λ((u1 :unit),(u2 :unit)). return ())):(word32 # (word32 # bool) # bool # bool #bool # bool -> unit M)``;

val _ = g `∀y. preserve_relation_mmu(^data_processing_core_part y) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
val _ = e(STRIP_TAC);
val _ = e(pairLib.PairCases_on `y`);
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val data_processing_core_part_thm1 = top_thm();
val data_processing_core_part_thm2 = SIMP_RULE (srw_ss()) [(SPECL [data_processing_core_part, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``] (INST_TYPE [alpha |-> (Type `:(word32 # (word32 # bool) # bool # bool #bool # bool)`), beta |-> type_of (``()``)] second_abs_lemma))] data_processing_core_part_thm1;
val _ = add_to_simplist data_processing_core_part_thm1;
val _ = add_to_simplist data_processing_core_part_thm2;


val _ = g `preserve_relation_mmu ((^data_processing_pre_part) >>= (^data_processing_core_part)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [seqT_preserves_relation_uu_thm, comb_monot_thm, data_processing_core_part_thm2, data_processing_pre_part_thm, trans_priv_mode_constraints_thm]);
val _ = e(ASSUME_TAC data_processing_core_part_thm2);
val _ = e(ASSUME_TAC data_processing_pre_part_thm);
val _ = e(ASSUME_TAC (SPEC ``(assert_mode 16w):(arm_state->bool)`` comb_monot_thm));
val _ = e(ASSUME_TAC (SPECL [data_processing_pre_part, data_processing_core_part,``16w:word5``, ``priv_mode_constraints``, ``priv_mode_similar``]  (INST_TYPE [alpha |-> Type `:(word32 # (word32 # bool) # bool # bool #bool # bool)`, beta |-> type_of (``()``)] seqT_preserves_relation_uu_thm)));
val _ = e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm, trans_priv_mode_constraints_thm]);
val data_processing_help_thm = top_thm();
val _ = add_to_simplist data_processing_help_thm;

(* multiply long - write flags - part *)

val multiply_long_instr_part_thm = store_thm(
    "multiply_long_instr_part_thm",
    ``preserve_relation_mmu
      ((λ(C_flag,V_flag).
      write_flags <|proc := 0|>
        (word_msb
           ((if b then (sw2sw (rm:word32):word64) * (sw2sw (rn:word32):word64) else w2w rm * w2w rn) +
            if b0 then rdhi @@ rdlo else 0w),
         (if b then (sw2sw rm :word64) * sw2sw rn else w2w rm * w2w rn) +
         (if b0 then (rdhi:word32) @@ (rdlo:word32) else (0w:word64)) =
         0w,C_flag,V_flag))
      (if (version:num) = 4 then (UNKNOWN,UNKNOWN) else (C,V)))
      (assert_mode 16w) (assert_mode 16w) priv_mode_constraints
     priv_mode_similar``,
    RW_TAC (srw_ss()) [(GEN_ALL write_flags_thm)]);
val _ = add_to_simplist multiply_long_instr_part_thm;

(* instructions *)

val _ = g `preserve_relation_mmu (data_processing_instruction <|proc := 0|> (enc,inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
val _ = e (Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(*30 subgoals *)
(* data processing *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, data_processing_instr, LET_DEF] THEN PairedLambda.GEN_BETA_TAC);
val _ = e(Q.ABBREV_TAC `xx = (shifted, C_shift)`);
val _ = go_on_p 1;
(* add sub *)
val _ = go_on_p 1;
(* move halfword  *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* multiply*)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* multiply subtract *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* signed halword multiply *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def]);
val _ = e(Cases_on `enc` THEN Cases_on `c=0w` THEN Cases_on `c=1w` THEN Cases_on `b0` THEN Cases_on `c=2w` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 32;
(* signed multiply dual *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* signed multiply long dual *)
val _ = go_on_p 1;
(* signed most significant multiply *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* signed most significant multiply subtract *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* multiply long *)
val _ = go_on_p 1;
(* multiply accumulate accumulate *)
val _ = go_on_p 1;
(* saturate *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturate_instr, LET_DEF] THEN REPEAT CASE_TAC THEN PairedLambda.GEN_BETA_TAC);
val _ = go_on_p 8;
(* saturate 16 *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturate_16_instr, LET_DEF] THEN REPEAT CASE_TAC THEN PairedLambda.GEN_BETA_TAC);
val _ = go_on_p 8;
(* saturating add subtract *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturating_add_subtract_instr, LET_DEF] THEN Cases_on `enc` THEN PairedLambda.GEN_BETA_TAC THEN  FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* pack halfword *)
val _ = e (FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, pack_halfword_instr_def]);
val _ = e (Cases_on `decode_imm_shift ((1 :+ b) 0w,c1)` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* extend byte *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* extend_byte_16 *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* extend halword *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* bit field clear insert *)
val _ = go_on_p 1;
(* count leading zeroes *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* reverse bits *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* byte reverse word *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* byte reverse packed halfword *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* byte reverse signed halword *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* bit field extract *)
val _ = go_on_p 1;
(* select bytes *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* unsigned sum absolute differences *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* parallel add subtract *)
val _ = e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, parallel_add_subtract_instr, LET_DEF] THEN PairedLambda.GEN_BETA_TAC THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on_p 4;
(* divide *)
val _ = go_on_p 1;
(* now save *)
val data_processing_instruction_comb_thm = save_comb_thm("data_processing_instruction_comb_thm", top_thm(), ``data_processing_instruction``);



(************************************************************)
(**********************    F. Misc    ***********************)
(************************************************************)




val read_info_constlem = store_thm(
    "read_info_constlem",
    ``!s. ?x. ((read_info <|proc:=0|>) s) = ValueState x s``,
    RW_TAC (srw_ss()) [read_info_def, readT_def]);


val read_info_thm = prove_and_save_s(``read_info <|proc:=0|>``, "read_info_thm");


val _ = g `preserve_relation_mmu (miscellaneous_instruction <|proc:=0|> (enc,inst)) (assert_mode 16w) mode_mix priv_mode_constraints_v2a priv_mode_similar`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [miscellaneous_instruction_def]);
val _ = e(REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []));
(* NOP *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* yield *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [yield_instr, hint_yield_def]);
val _ = go_on_p 2;
(* wait for event *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [wait_for_event_instr_def, instruction_def, run_instruction_def]);
val _ = go_on_p 2;
(* wait for interrupt *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [wait_for_interrupt_instr_def, instruction_def, run_instruction_def]);
val _ = go_on_p 2;
(* send event *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [send_event_instr_def, instruction_def, run_instruction_def]);
val _ = go_on_p 2;
(* debug *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [debug_instr_def, instruction_def, run_instruction_def]);
val _ = go_on_p 2;
(* breakpoint *)
val _ = e(MODE_MIX_TAC ``little_mode_mix``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [breakpoint_instr]);
val _ = e(SUBGOAL_THEN ``!info. preserve_relation_mmu (if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>) (assert_mode 16w) little_mode_mix priv_mode_constraints_v1 priv_mode_similar``
  (fn th => ASSUME_TAC th
       THEN ASSUME_TAC (SPEC ``(λinfo. if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>)`` (INST_TYPE [alpha |-> Type `:ARMinfo`, beta |-> Type `:unit`]  second_abs_lemma))
       THEN ASSUME_TAC trans_priv_mode_constraints_thm
       THEN ASSUME_TAC (SPECL [``(read_info <|proc:=0|>):(ARMinfo M)``, ``( \info. (if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>))``, ``16w:word5``, ``little_mode_mix``, ``little_mode_mix``, ``priv_mode_constraints_v1``, ``priv_mode_similar``] (INST_TYPE [alpha |-> Type `:ARMinfo`, beta |-> Type `:unit`] seqT_preserves_relation_comb_thm))
       THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_comb_16_thm, (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 read_info_thm)))]));
val _ = e(STRIP_TAC);
val _ = e(CASE_TAC);
val _ = e(LITTLE_MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [take_undef_instr_exception_comb_thm]);
val _ = e(LITTLE_MODE_MIX_TAC ``comb_mode 16w 23w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [take_prefetch_abort_exception_comb_thm]);
(* data memory barrier *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* data synch barrier *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* inst synch barrier *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* swap *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* preload data *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* preload instr *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* svc *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 19w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [take_svc_exception_comb_thm]);
(* secure monitor call *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* enter x leave x *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
(* clear exclusive *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [clear_exclusive_instr_def, clear_exclusive_local_def, LET_DEF]);
val _ = go_on_p 1;
(* if-then *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = go_on_p 1;
val miscellaneous_instruction_comb_thm = save_comb_thm("miscellaneous_instruction_comb_thm", top_thm(), ``miscellaneous_instruction``);



(************************************************************)
(********************  G.  arm_instr    *********************)
(************************************************************)


val IT_advance_constlem = store_thm(
    "IT_advance_constlem",
    ``((s.psrs(0,CPSR)).IT = 0w) ==> (((IT_advance <|proc :=0|>) s) = (ValueState () s))``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THENL [`!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
                THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
                THEN FULL_SIMP_TAC (srw_ss()) [],
             ALL_TAC,
             ALL_TAC]
      THEN UNDISCH_ALL_TAC
      THEN EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THEN Cases_on `s`
      THEN FULL_SIMP_TAC (srw_ss()) [arm_state_psrs_fupd]
      THEN ASSUME_TAC (SPEC ``f0:num#PSRName->ARMpsr`` (GEN_ALL psrs_update_in_update_thm))
      THEN Q.ABBREV_TAC `x = (f0 (0,CPSR)).IT`
      THEN  RW_TAC (srw_ss()) [arm_state_psrs_fupd]);

val condition_passed_constlem = store_thm(
    "condition_passed_constlem",
    ``!s cond. ?x. (condition_passed <|proc:=0|> cond) s = ValueState x s``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN RW_TAC (srw_ss()) []);

val condition_passed_similar_lem = store_thm(
    "condition_passed_similar_lem",
    ``!s1 s2 cond. (similar g s1 s2) ==> (?pass. (((condition_passed <|proc:=0|> cond) s1 = ValueState pass s1) /\ ((condition_passed <|proc:=0|> cond) s2 = ValueState pass s2)))``,
    RW_TAC (srw_ss()) []
      THEN IMP_RES_TAC  similarity_implies_equal_av_thm
      THEN UNDISCH_TAC ``similar g s1 s2``
      THEN EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN RW_TAC (srw_ss()) []);


val arm_instr_core_def = Define `arm_instr_core ii (pass:bool) (enc:Encoding) (cond:word4) (inst:ARMinstruction) =
   if pass then
           case inst of
              Unpredictable => errorT "decode: unpredictable"
           | Undefined => take_undef_instr_exception ii
           | Branch b => branch_instruction ii (enc,b)
           | DataProcessing d => data_processing_instruction ii (enc,d)
           | StatusAccess s => status_access_instruction ii (enc,s)
           | LoadStore l => load_store_instruction ii (enc,l)
           | Miscellaneous m => miscellaneous_instruction ii (enc,m)
           | Coprocessor c => coprocessor_instruction ii (enc,cond,c)
         else
           increment_pc ii enc`;



val _ = g `preserve_relation_mmu (arm_instr_core <|proc:=0|> pass enc cond inst) (assert_mode 16w) mode_mix priv_mode_constraints_v2a priv_mode_similar`;
val _ = e(RW_TAC (srw_ss()) [arm_instr_core_def]);
val _ = e(CASE_TAC);
(* 8 cases *)
(* error *)
val _ = e(MODE_MIX_TAC ``assert_mode 16w``);
val _ = go_on 1;
(* take undef instr exception *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [take_undef_instr_exception_comb_thm]);
(* branch instruction *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [branch_instruction_comb_thm]);
(* data processing instruction *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_comb_thm]);
(* status access instruction *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [status_access_instruction_comb_thm]);
(* load store instruction *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [load_store_instruction_comb_thm]);
(* misc instruction *)
val _ = e(FULL_SIMP_TAC (srw_ss()) [miscellaneous_instruction_comb_thm]);
(* coprocessor instruction *)
val _ = e(MODE_MIX_TAC ``comb_mode 16w 27w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [coprocessor_instruction_comb_thm]);
(* increment PC *)
val _ = e(MODE_MIX_TAC ``assert_mode 16w``);
val _ = e(FULL_SIMP_TAC (srw_ss()) [increment_pc_thm]);
val arm_instr_core_comb_thm = save_comb_thm("arm_instr_core_comb_thm", top_thm(), ``arm_instr_core``);


val arm_instr_alternative_def = store_thm(
    "arm_instr_alternative_def",
    ``arm_instr ii (enc,cond,inst) =
    (condition_passed ii cond >>=
      (λpass.
         arm_instr_core ii pass enc cond inst)) >>=
     (λu.
        condT
          (case inst of
             Unpredictable => T
           | Undefined => T
           | Branch v6 => T
           | DataProcessing v7 => T
           | StatusAccess v8 => T
           | LoadStore v9 => T
           | Miscellaneous (Hint v33) => T
           | Miscellaneous (Breakpoint v34) => T
           | Miscellaneous (Data_Memory_Barrier v35) => T
           | Miscellaneous (Data_Synchronization_Barrier v36) => T
           | Miscellaneous (Instruction_Synchronization_Barrier v37) =>
               T
           | Miscellaneous (Swap v38 v39 v40 v41) => T
           | Miscellaneous (Preload_Data v42 v43 v44 v45) => T
           | Miscellaneous (Preload_Instruction v46 v47 v48) => T
           | Miscellaneous (Supervisor_Call v49) => T
           | Miscellaneous (Secure_Monitor_Call v50) => T
           | Miscellaneous (Enterx_Leavex v51) => T
           | Miscellaneous Clear_Exclusive => T
           | Miscellaneous (If_Then v52 v53) => F
           | Coprocessor v11 => T) (IT_advance ii))``,
     RW_TAC (srw_ss()) [arm_instr_core_def, arm_instr_def]);


val arm_instr_comb_thm = store_thm("arm_instr_comb_thm",
    ``preserve_relation_mmu (arm_instr <|proc:=0|> (enc, cond, inst)) (assert_mode 16w) mode_mix priv_mode_constraints_v2a priv_mode_similar``,
    RW_TAC (srw_ss()) [arm_instr_alternative_def, preserve_relation_mmu_def, seqT_def, condT_def]
       THEN (ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``cond:word4``] condition_passed_similar_lem)
                THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [untouched_refl])
                THEN ASSUME_TAC reflex_priv_mode_constraints_v2a_thm
                THEN IMP_RES_TAC reflexive_comp_def
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THENL [FULL_SIMP_TAC (srw_ss()) [mode_mix_def, assert_mode_def],
                       FULL_SIMP_TAC (srw_ss()) [mode_mix_def, assert_mode_def],
                       IMP_RES_TAC similarity_implies_equal_av_thm,
                       IMP_RES_TAC similarity_implies_equal_av_thm,
                       ALL_TAC]
                THEN Cases_on `arm_instr_core <|proc := 0|> pass enc cond inst s2`
                THEN ASSUME_TAC arm_instr_core_comb_thm
                THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) [constT_def]
                THEN IMP_RES_TAC  similarity_implies_equal_av_thm
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s1' = 16w`
                THEN IMP_RES_TAC similarity_implies_equal_av_thm
                THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                THEN FULL_SIMP_TAC (srw_ss()) [])
       THENL [ASSUME_TAC (CONJUNCT1 (CONJUNCT2 IT_advance_thm))
                THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, priv_mode_constraints_v2a_def]
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1':arm_state``, ``b:arm_state``])
                THEN IMP_RES_TAC untouched_mmu_setup_lem
                THEN (NTAC 2 ((`(ARM_MODE s1' = 16w) /\ (ARM_MODE b = 16w)` by FULL_SIMP_TAC (srw_ss())  [])
                                  THEN FULL_SIMP_TAC (srw_ss()) []
                                  THEN RES_TAC
                                  THEN FULL_SIMP_TAC (srw_ss()) []))
                THEN METIS_TAC [untouched_trans, trans_priv_mode_constraints_thm, trans_fun_def, mode_mix_def],
              `((s1'.psrs (0,CPSR)).IT = 0w) /\ ((b.psrs (0,CPSR)).IT = 0w)` by FULL_SIMP_TAC (srw_ss())  [priv_mode_constraints_v2a_def, priv_mode_constraints_v1_def, LET_DEF]
                THEN IMP_RES_TAC IT_advance_constlem
                THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []]);



val _ = export_theory();
