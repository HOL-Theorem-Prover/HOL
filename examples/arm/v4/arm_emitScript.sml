(* ========================================================================= *)
(* FILE          : arm_emitScript.sml                                        *)
(* DATE          : 2005 - 2009                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "systemTheory", "basis_emitTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q updateTheory armTheory systemTheory;
open EmitML basis_emitTheory;

val _ = new_theory "arm_emit";

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

(*---------------------------------------------------------------------------*)

val num2register = prove(
  `!n. num2register n =
         if n = 0 then r0 else
         if n = 1 then r1 else
         if n = 2 then r2 else
         if n = 3 then r3 else
         if n = 4 then r4 else
         if n = 5 then r5 else
         if n = 6 then r6 else
         if n = 7 then r7 else
         if n = 8 then r8 else
         if n = 9 then r9 else
         if n = 10 then r10 else
         if n = 11 then r11 else
         if n = 12 then r12 else
         if n = 13 then r13 else
         if n = 14 then r14 else
         if n = 15 then r15 else
         if n = 16 then r8_fiq else
         if n = 17 then r9_fiq else
         if n = 18 then r10_fiq else
         if n = 19 then r11_fiq else
         if n = 20 then r12_fiq else
         if n = 21 then r13_fiq else
         if n = 22 then r14_fiq else
         if n = 23 then r13_irq else
         if n = 24 then r14_irq else
         if n = 25 then r13_svc else
         if n = 26 then r14_svc else
         if n = 27 then r13_abt else
         if n = 28 then r14_abt else
         if n = 29 then r13_und else
         if n = 30 then r14_und else
           FAIL num2register ^(mk_var("30 < n",bool)) n`,
  SRW_TAC [] [num2register_thm, combinTheory.FAIL_THM]);

val num2condition = prove(
  `!n. num2condition n =
         if n = 0 then EQ else
         if n = 1 then CS else
         if n = 2 then MI else
         if n = 3 then VS else
         if n = 4 then HI else
         if n = 5 then GE else
         if n = 6 then GT else
         if n = 7 then AL else
         if n = 8 then NE else
         if n = 9 then CC else
         if n = 10 then PL else
         if n = 11 then VC else
         if n = 12 then LS else
         if n = 13 then LT else
         if n = 14 then LE else
         if n = 15 then NV else
           FAIL num2condition ^(mk_var("15 < n",bool)) n`,
  SRW_TAC [] [num2condition_thm, combinTheory.FAIL_THM]);

val register_decl = `register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;

val psr_decl =
  `psr = CPSR | SPSR_fiq | SPSR_irq | SPSR_svc | SPSR_abt | SPSR_und`;

val exceptions_decl = `exceptions = reset | undefined | software | pabort |
                                    dabort | address |interrupt | fast`;

val mode_decl = `mode = usr | fiq | irq | svc | abt | und | sys | safe`;

val condition_decl = `condition = EQ | CS | MI | VS | HI | GE | GT | AL |
                                  NE | CC | PL | VC | LS | LT | LE | NV`;

val iclass_decl = `iclass = swp | mrs | msr | data_proc | mla_mul |
                            ldr_str | ldrh_strh | ldm_stm | br | swi_ex |
                            cdp_und | mcr | mrc | ldc_stc | unexec`;

val n2w_w2n_rule = GEN_ALL o SIMP_RULE bool_ss [wordsTheory.n2w_w2n];

val spec_word_rule16 = n2w_w2n_rule o Q.SPEC `w2n (w:word16)`;
val spec_word_rule32 = n2w_w2n_rule o Q.SPEC `w2n (w:word32)`;

val spec_word_rule12 =
  n2w_w2n_rule o INST [`opnd2` |-> `w2n (w:word12)`] o SPEC_ALL;

val mem_rule = REWRITE_RULE [GSYM mem_read_def, GSYM mem_write_def];

fun mk_word n =
  let val s = Int.toString n
      val w = "type word" ^ s ^ " = wordsML.word" ^ s
  in
    MLSIG w
  end;

val _ = eSML "update"
  (OPEN ["num", "sum", "fcp", "words"]
    :: MLSIG "type 'a word = 'a wordsML.word"
    :: MLSIG "type num = numML.num"
    :: MLSIG "type word2 = wordsML.word2"
    :: MLSIG "type word8 = wordsML.word8"
    :: MLSIG "type word16 = wordsML.word16"
    :: MLSIG "type word30 = wordsML.word30"
    :: MLSIG "type word32 = wordsML.word32"
    :: MLSTRUCT "type mem = word30->word32"
    :: MLSIG "type mem"
    :: MLSTRUCT "val mem_updates = ref ([]: word30 list)"
    :: MLSIG "val mem_updates : word30 list ref"
    :: DATATYPE (`formats = SignedByte | UnsignedByte
                          | SignedHalfWord | UnsignedHalfWord
                          | UnsignedWord`)
    :: DATATYPE (`data = Byte word8 | Half word16 | Word word32`)
    :: map DEFN [LUPDATE_def, mem_read_def, mem_write_def, mem_write_block_def]
     @ map (DEFN o mem_rule)
        [empty_memory_def, mem_items_def, addr30_def, GET_HALF_def,
         SIMP_RULE std_ss [literal_case_DEF] GET_BYTE_def,
         FORMAT_def, SET_BYTE_def, SET_HALF_def,
         MEM_WRITE_BYTE_def, MEM_WRITE_HALF_def,
         MEM_WRITE_WORD_def, MEM_WRITE_def]);

val _ = eSML "arm"
  (OPEN ["num", "sum", "option", "set", "fcp", "list", "rich_list",
         "bit", "words", "update"]
    :: MLSIG "type 'a itself = 'a fcpML.itself"
    :: MLSIG "type 'a word = 'a wordsML.word"
    :: MLSIG "type ('a,'b) cart = ('a,'b) fcpML.cart"
    :: MLSIG "type ('a,'b) sum = ('a,'b) sumML.sum"
    :: MLSIG "type 'a bit0 = 'a fcpML.bit0"
    :: MLSIG "type 'a bit1 = 'a fcpML.bit1"
    :: MLSIG "type num = numML.num"
    :: map (fn decl => DATATYPE decl)
           [register_decl, psr_decl, mode_decl, condition_decl]
     @ map (fn decl => EQDATATYPE ([], decl)) [exceptions_decl,iclass_decl]
     @ DATATYPE (`state_inp = <| state : 'a; inp : num -> 'b |>`)
    :: DATATYPE (`state_out = <| state : 'a; out : 'b |>`)
    :: map mk_word [2,3,4,5,8,12,16,24,30,32]
     @ MLSTRUCT "type registers = register->word32"
    :: MLSTRUCT "type psrs = psr->word32"
    :: MLSTRUCT "type mem = updateML.mem"
    :: MLSTRUCT "type data = updateML.data"
    :: MLSIG "type registers = register->word32"
    :: MLSIG "type psrs = psr->word32"
    :: MLSIG "type mem = updateML.mem"
    :: MLSIG "type data = updateML.data"
    :: DATATYPE (`regs = <| reg : registers; psr : psrs |>`)
    :: DATATYPE (`memop = MemRead word32 | MemWrite word32 data |
                          CPWrite word32`)
    :: DATATYPE (`arm_state = <| regs : regs; ireg : word32;
                                 exception : exceptions |>`)
    :: DATATYPE (`arm_output = <| transfers : memop list;
                                  cpi : bool; user : bool |>`)
    :: DATATYPE (`cp_output = <| data : word32 option list; absent : bool |>`)
    :: DATATYPE (`bus = <| data : word32 list; memory : mem; abort : num option;
                           cp_state : 'a |>`)
    :: DATATYPE (`arm_sys_state = <| registers : registers; psrs : psrs;
                        memory : mem; undefined : bool; cp_state : 'a |>`)
    :: DATATYPE (`interrupt = Reset regs | Undef | Prefetch |
                              Dabort num | Fiq | Irq`)
    :: DATATYPE (`arm_input = <| ireg : word32; data : word32 list;
                                 interrupt : interrupt option; no_cp : bool |>`)
    :: DATATYPE (`coproc =
           <| absent : bool -> word32 -> bool;
              f_cdp  : 'a -> bool -> word32 -> 'a;
              f_mrc  : 'a -> bool -> word32 -> word32;
              f_mcr  : 'a -> bool -> word32 -> word32 -> 'a;
              f_stc  : 'a -> bool -> word32 -> word32 option list;
              f_ldc  : 'a -> bool -> word32 -> word32 list -> 'a;
              n_ldc  : 'a -> bool -> word32 -> num |>`)
    :: MLSTRUCT "val mem_updates = ref ([]: word30 list)"
    :: MLSIG "val mem_updates : word30 list ref"
    :: map DEFN (map spec_word_rule32
         [DECODE_PSR_THM, DECODE_BRANCH_THM, DECODE_DATAP_THM,
          DECODE_MRS_THM, DECODE_MSR_THM, DECODE_LDR_STR_THM,
           DECODE_MLA_MUL_THM, DECODE_LDM_STM_THM, DECODE_SWP_THM,
           DECODE_LDC_STC_THM, DECODE_LDRH_STRH_THM, DECODE_CDP_THM,
           DECODE_MRC_MCR_THM]
       @ [DECODE_CPN_def, DECODE_CP_def, USER_def, mode_reg2num_def,
          DECODE_ARM_def, mode_num_def, exceptions2num_thm, register2num_thm,
          num2register, num2condition, SET_IFMODE_def,
          REG_READ_def, REG_WRITE_def, INC_PC_def, FETCH_PC_def,
          SET_NZCV_def, SET_NZC_def, SET_NZ_def,
          SIMP_RULE std_ss [literal_case_DEF] DECODE_MODE_def,
          NZCV_def, CARRY_def, mode2psr_def, SPSR_READ_def, CPSR_READ_def,
          CPSR_WRITE_def, SPSR_WRITE_def, exception2mode_def,
          SPECL [`r`,`e`]  EXCEPTION_def, BRANCH_def, LSL_def, LSR_def,
          ASR_def, ROR_def, IMMEDIATE_def, SHIFT_IMMEDIATE2_def,
          SHIFT_REGISTER2_def, spec_word_rule12 SHIFT_IMMEDIATE_THM,
          spec_word_rule12 SHIFT_REGISTER_THM, ADDR_MODE1_def,
          SPEC `f` ALU_arith_def, ALU_logic_def,
          ADD_def, SUB_def, AND_def, EOR_def, ORR_def,
          ALU_def, ARITHMETIC_def, TEST_OR_COMP_def, DATA_PROCESSING_def,
          MRS_def, MSR_def, ALU_multiply_def, MLA_MUL_def,
          UP_DOWN_def, ADDR_MODE2_def, IMP_DISJ_THM, LDR_STR_def,
          ADDR_MODE3_def, LDRH_STRH_def,spec_word_rule16 REGISTER_LIST_THM,
          ADDRESS_LIST_def, WB_ADDRESS_def, FIRST_ADDRESS_def,
          ADDR_MODE4_def, LDM_LIST_def, STM_LIST_def, LDM_STM_def,
          SWP_def, MRC_def, MCR_OUT_def, ADDR_MODE5_def, LDC_STC_def,
          CONDITION_PASSED2_def, CONDITION_PASSED_def,
          RUN_ARM_def, IS_Reset_def, PROJ_Dabort_def, PROJ_Reset_def ,
          interrupt2exception_def, PROJ_IF_FLAGS_def, NEXT_ARM_def,
          OUT_ARM_def, mem_rule TRANSFER_def, TRANSFERS_def,
          OUT_CP_def, RUN_CP_def, mem_rule NEXT_ARM_MMU,
          mem_rule NEXT_ARM_MEM, empty_registers_def]));

(* -------------------------------------------------------------------------- *)

val _ = export_theory();
