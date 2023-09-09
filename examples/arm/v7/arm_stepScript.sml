(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Provide interface to Hoare logic                                     *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["armTheory", "wordsLib"];
*)

open HolKernel boolLib bossLib;

open arithmeticTheory bitTheory wordsTheory combinTheory;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory armTheory;

val _ = new_theory "arm_step";
val _ = ParseExtras.temp_loose_equality()
val _ = BasicProvers.temp_delsimps ["UPDATE_EQ", "UPDATE_APPLY_ID_RWT"]

(* ------------------------------------------------------------------------- *)

val _ = numLib.prefer_num();
val _ = wordsLib.prefer_word();

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Access functions for ARM model                                            *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype`
  arm_bit = psrN | psrZ | psrC | psrV | psrQ | psrJ
          | psrE | psrA | psrI | psrF | psrT`;

val _ = Hol_datatype
  `arm_sctlr_bit = sctlrV | sctlrU | sctlrA | sctlrEE | sctlrTE | sctlrNMFI`;

val _ = Hol_datatype
  `arm_scr_bit = scrnET | scrAW | scrFW | scrEA | scrFIQ | scrIRQ | scrNS`;

val ARM_ARCH_def = Define`
  ARM_ARCH s = s.information.arch`;

val ARM_EXTENSIONS_def = Define`
  ARM_EXTENSIONS s = s.information.extensions`;

val ARM_UNALIGNED_SUPPORT_def = Define`
  ARM_UNALIGNED_SUPPORT s = s.information.unaligned_support`;

val ARM_READ_CPSR_def = Define`
  ARM_READ_CPSR s = s.psrs (0,CPSR)`;

val ARM_WRITE_CPSR_def = Define`
  ARM_WRITE_CPSR d s = s with psrs updated_by ((0,CPSR) =+ d)`;

val ARM_MODE_def = Define`
  ARM_MODE s = (ARM_READ_CPSR s).M`;

val ARM_WRITE_MODE_def = Define`
  ARM_WRITE_MODE m s = ARM_WRITE_CPSR (ARM_READ_CPSR s with M := m) s`;

val word4_def = Define`
  word4 (b3,b2,b1,b0) : word4 =
    FCP i. (i = 3) /\ b3 \/ (i = 2) /\ b2 \/ (i = 1) /\ b1 \/ (i = 0) /\ b0`;

val ARM_READ_GE_def = Define`
  ARM_READ_GE s = (ARM_READ_CPSR s).GE`;

val ARM_WRITE_GE_def = Define`
  ARM_WRITE_GE ge s = ARM_WRITE_CPSR (ARM_READ_CPSR s with GE := ge) s`;

val ARM_READ_IT_def = Define`
  ARM_READ_IT s = (ARM_READ_CPSR s).IT`;

val ARM_WRITE_IT_def = Define`
  ARM_WRITE_IT it s = ARM_WRITE_CPSR (ARM_READ_CPSR s with IT := it) s`;

val ARM_READ_STATUS_def = Define`
  (ARM_READ_STATUS psrN s = (ARM_READ_CPSR s).N) /\
  (ARM_READ_STATUS psrZ s = (ARM_READ_CPSR s).Z) /\
  (ARM_READ_STATUS psrC s = (ARM_READ_CPSR s).C) /\
  (ARM_READ_STATUS psrV s = (ARM_READ_CPSR s).V) /\
  (ARM_READ_STATUS psrQ s = (ARM_READ_CPSR s).Q) /\
  (ARM_READ_STATUS psrJ s = (ARM_READ_CPSR s).J) /\
  (ARM_READ_STATUS psrE s = (ARM_READ_CPSR s).E) /\
  (ARM_READ_STATUS psrA s = (ARM_READ_CPSR s).A) /\
  (ARM_READ_STATUS psrI s = (ARM_READ_CPSR s).I) /\
  (ARM_READ_STATUS psrF s = (ARM_READ_CPSR s).F) /\
  (ARM_READ_STATUS psrT s = (ARM_READ_CPSR s).T)`;

val ARM_WRITE_STATUS_def = Define`
  (ARM_WRITE_STATUS psrN b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with N := b) s) /\
  (ARM_WRITE_STATUS psrZ b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with Z := b) s) /\
  (ARM_WRITE_STATUS psrC b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with C := b) s) /\
  (ARM_WRITE_STATUS psrV b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with V := b) s) /\
  (ARM_WRITE_STATUS psrQ b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with Q := b) s) /\
  (ARM_WRITE_STATUS psrJ b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with J := b) s) /\
  (ARM_WRITE_STATUS psrE b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with E := b) s) /\
  (ARM_WRITE_STATUS psrA b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with A := b) s) /\
  (ARM_WRITE_STATUS psrI b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with I := b) s) /\
  (ARM_WRITE_STATUS psrF b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with F := b) s) /\
  (ARM_WRITE_STATUS psrT b s =
     ARM_WRITE_CPSR (ARM_READ_CPSR s with T := b) s)`;

val ARM_READ_SCTLR_def = Define`
  (ARM_READ_SCTLR sctlrV s = s.coprocessors.state.cp15.SCTLR.V) /\
  (ARM_READ_SCTLR sctlrA s = s.coprocessors.state.cp15.SCTLR.A) /\
  (ARM_READ_SCTLR sctlrU s = s.coprocessors.state.cp15.SCTLR.U) /\
  (ARM_READ_SCTLR sctlrEE s = s.coprocessors.state.cp15.SCTLR.EE) /\
  (ARM_READ_SCTLR sctlrTE s = s.coprocessors.state.cp15.SCTLR.TE) /\
  (ARM_READ_SCTLR sctlrNMFI s = s.coprocessors.state.cp15.SCTLR.NMFI)`;

val ARM_READ_SCR_def = Define`
  (ARM_READ_SCR scrnET s = s.coprocessors.state.cp15.SCR.nET) /\
  (ARM_READ_SCR scrAW s = s.coprocessors.state.cp15.SCR.AW) /\
  (ARM_READ_SCR scrFW s = s.coprocessors.state.cp15.SCR.FW) /\
  (ARM_READ_SCR scrEA s = s.coprocessors.state.cp15.SCR.EA) /\
  (ARM_READ_SCR scrFIQ s = s.coprocessors.state.cp15.SCR.FIQ) /\
  (ARM_READ_SCR scrIRQ s = s.coprocessors.state.cp15.SCR.IRQ) /\
  (ARM_READ_SCR scrNS s = s.coprocessors.state.cp15.SCR.NS)`;

val ARM_READ_TEEHBR_def = Define`
  ARM_READ_TEEHBR s = s.coprocessors.state.cp14.TEEHBR`;

val SPSR_MODE_def = Define`
  SPSR_MODE (m:word5) =
    case m
    of 0b10001w => SPSR_fiq
     | 0b10010w => SPSR_irq
     | 0b10011w => SPSR_svc
     | 0b10110w => SPSR_mon
     | 0b10111w => SPSR_abt
     | _        => SPSR_und`;

val ARM_READ_SPSR_MODE_def = Define`
  ARM_READ_SPSR_MODE m s = s.psrs (0,SPSR_MODE m)`;

val ARM_READ_SPSR_def = Define`
  ARM_READ_SPSR s = ARM_READ_SPSR_MODE (ARM_MODE s) s`;

val ARM_WRITE_SPSR_MODE_def = Define`
  ARM_WRITE_SPSR_MODE (m:word5) d s =
    s with psrs updated_by ((0,SPSR_MODE m) =+ d)`;

val ARM_WRITE_SPSR_def = Define`
  ARM_WRITE_SPSR d s = ARM_WRITE_SPSR_MODE (ARM_MODE s) d s`;

local
  val l = fst (listSyntax.dest_list
      ``[0b10001w;0b10010w;0b10011w;0b10110w;0b10111w;0b11011w]:word5 list``)
  fun rule thm m = GEN_ALL (RIGHT_CONV_RULE EVAL
                     (Drule.SPEC_ALL (Thm.SPEC m thm)))
in
  val ARM_READ_SPSR_MODE = save_thm("ARM_READ_SPSR_MODE",
    Drule.LIST_CONJ (List.map (rule ARM_READ_SPSR_MODE_def) l));
  val ARM_WRITE_SPSR_MODE = save_thm("ARM_WRITE_SPSR_MODE",
    Drule.LIST_CONJ (List.map (rule ARM_WRITE_SPSR_MODE_def) l));
end;

val ARM_READ_MODE_SPSR_def = Define`
  ARM_READ_MODE_SPSR s = (ARM_READ_SPSR s).M`;

val ARM_WRITE_MODE_SPSR_def = Define`
  ARM_WRITE_MODE_SPSR m s = ARM_WRITE_SPSR (ARM_READ_SPSR s with M := m) s`;

val ARM_READ_GE_SPSR_def = Define`
  ARM_READ_GE_SPSR s = (ARM_READ_SPSR s).GE`;

val ARM_WRITE_GE_SPSR_def = Define`
  ARM_WRITE_GE_SPSR ge s = ARM_WRITE_SPSR (ARM_READ_SPSR s with GE := ge) s`;

val ARM_READ_IT_SPSR_def = Define`
  ARM_READ_IT_SPSR s = (ARM_READ_SPSR s).IT`;

val ARM_WRITE_IT_SPSR_def = Define`
  ARM_WRITE_IT_SPSR it s = ARM_WRITE_SPSR (ARM_READ_SPSR s with IT := it) s`;

val ARM_READ_STATUS_SPSR_def = Define`
  (ARM_READ_STATUS_SPSR psrN s = (ARM_READ_SPSR s).N) /\
  (ARM_READ_STATUS_SPSR psrZ s = (ARM_READ_SPSR s).Z) /\
  (ARM_READ_STATUS_SPSR psrC s = (ARM_READ_SPSR s).C) /\
  (ARM_READ_STATUS_SPSR psrV s = (ARM_READ_SPSR s).V) /\
  (ARM_READ_STATUS_SPSR psrQ s = (ARM_READ_SPSR s).Q) /\
  (ARM_READ_STATUS_SPSR psrJ s = (ARM_READ_SPSR s).J) /\
  (ARM_READ_STATUS_SPSR psrE s = (ARM_READ_SPSR s).E) /\
  (ARM_READ_STATUS_SPSR psrA s = (ARM_READ_SPSR s).A) /\
  (ARM_READ_STATUS_SPSR psrI s = (ARM_READ_SPSR s).I) /\
  (ARM_READ_STATUS_SPSR psrF s = (ARM_READ_SPSR s).F) /\
  (ARM_READ_STATUS_SPSR psrT s = (ARM_READ_SPSR s).T)`;

val ARM_WRITE_STATUS_SPSR_def = Define`
  (ARM_WRITE_STATUS_SPSR psrN b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with N := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrZ b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with Z := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrC b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with C := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrV b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with V := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrQ b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with Q := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrJ b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with J := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrE b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with E := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrA b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with A := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrI b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with I := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrF b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with F := b) s) /\
  (ARM_WRITE_STATUS_SPSR psrT b s =
     ARM_WRITE_SPSR (ARM_READ_SPSR s with T := b) s)`;

val ARM_READ_EVENT_REGISTER_def = Define`
  ARM_READ_EVENT_REGISTER s = s.event_register 0`;

val ARM_READ_INTERRUPT_WAIT_def = Define`
  ARM_READ_INTERRUPT_WAIT s = s.interrupt_wait 0`;

val ARM_WAIT_FOR_EVENT_def = Define`
  ARM_WAIT_FOR_EVENT s = s with event_register updated_by (0 =+ F)`;

val ARM_SEND_EVENT_def = Define`
  ARM_SEND_EVENT s = s with event_register updated_by (K (K T))`;

val ARM_WAIT_FOR_INTERRUPT_def = Define`
  ARM_WAIT_FOR_INTERRUPT s = s with interrupt_wait updated_by (0 =+ T)`;

val ARM_READ_MEM_def = Define`
  ARM_READ_MEM a s = s.memory a`;

val ARM_WRITE_MEM_def = Define`
  ARM_WRITE_MEM a w s = s with memory updated_by (a =+ w)`;

val ARM_WRITE_MEM_WRITE_def = Define`
  ARM_WRITE_MEM_WRITE a w s = s with accesses updated_by CONS (MEM_WRITE a w)`;

val ARM_WRITE_MEM_READ_def = Define`
  ARM_WRITE_MEM_READ a s = s with accesses updated_by CONS (MEM_READ a)`;

val RevLookUpRName_def = Define`
  RevLookUpRName (n:word4,m:word5) =
    case (n,m)
    of (0w, _       ) => RName_0usr
     | (1w, _       ) => RName_1usr
     | (2w, _       ) => RName_2usr
     | (3w, _       ) => RName_3usr
     | (4w, _       ) => RName_4usr
     | (5w, _       ) => RName_5usr
     | (6w, _       ) => RName_6usr
     | (7w, _       ) => RName_7usr
     | (8w, 0b10001w) => RName_8fiq
     | (8w, _       ) => RName_8usr
     | (9w, 0b10001w) => RName_9fiq
     | (9w, _       ) => RName_9usr
     | (10w,0b10001w) => RName_10fiq
     | (10w,_       ) => RName_10usr
     | (11w,0b10001w) => RName_11fiq
     | (11w,_       ) => RName_11usr
     | (12w,0b10001w) => RName_12fiq
     | (12w,_       ) => RName_12usr
     | (13w,0b10001w) => RName_SPfiq
     | (13w,0b10010w) => RName_SPirq
     | (13w,0b10011w) => RName_SPsvc
     | (13w,0b10111w) => RName_SPabt
     | (13w,0b11011w) => RName_SPund
     | (13w,0b10110w) => RName_SPmon
     | (13w,_       ) => RName_SPusr
     | (14w,0b10001w) => RName_LRfiq
     | (14w,0b10010w) => RName_LRirq
     | (14w,0b10011w) => RName_LRsvc
     | (14w,0b10111w) => RName_LRabt
     | (14w,0b11011w) => RName_LRund
     | (14w,0b10110w) => RName_LRmon
     | (14w,_       ) => RName_LRusr
     | (15w,_       ) => RName_PC`;

val ARM_READ_REG_MODE_def = Define`
  ARM_READ_REG_MODE x s = s.registers (0,RevLookUpRName x)`;

val ARM_WRITE_REG_MODE_def = Define`
  ARM_WRITE_REG_MODE x w s =
    s with registers updated_by ((0,RevLookUpRName x) =+ w)`;

val ARM_READ_REG_def = Define`
  ARM_READ_REG n s = ARM_READ_REG_MODE (n,ARM_MODE s) s`;

val ARM_WRITE_REG_def = Define`
  ARM_WRITE_REG n w s = ARM_WRITE_REG_MODE (n,ARM_MODE s) w s`;

val CLEAR_EXCLUSIVE_BY_ADDRESS_def = Define`
  CLEAR_EXCLUSIVE_BY_ADDRESS (a,n) s =
    s with monitors updated_by (ExclusiveMonitors_state_fupd (\state.
      SND (s.monitors.ClearExclusiveByAddress (a,<| proc := 0 |>,n) state)))`;

val MARK_EXCLUSIVE_GLOBAL_def = Define`
  MARK_EXCLUSIVE_GLOBAL (a,n) s =
    s with monitors updated_by (ExclusiveMonitors_state_fupd (\state.
      SND (s.monitors.MarkExclusiveGlobal (a,<| proc := 0 |>,n) state)))`;

val MARK_EXCLUSIVE_LOCAL_def = Define`
  MARK_EXCLUSIVE_LOCAL (a,n) s =
    s with monitors updated_by (ExclusiveMonitors_state_fupd (\state.
      SND (s.monitors.MarkExclusiveLocal (a,<| proc := 0 |>,n) state)))`;

val CLEAR_EXCLUSIVE_LOCAL_def = Define`
  CLEAR_EXCLUSIVE_LOCAL s =
    s with monitors updated_by (ExclusiveMonitors_state_fupd (\state.
      SND (s.monitors.ClearExclusiveLocal 0 state)))`;

val STATE_OPTION_def = Define`
  STATE_OPTION f s =
    case f s
    of Error _ => NONE
     | ValueState _ q => SOME q`;

val ARM_NEXT_def = Define`
  ARM_NEXT inp = STATE_OPTION (arm_next <| proc := 0 |> inp)`;

(* ------------------------------------------------------------------------- *)
(* Facilitate evaluation of set_q to when the saturation condition unknown   *)
(* ------------------------------------------------------------------------- *)

val condT_set_q = Q.store_thm("condT_set_q",
  `!b ii. (if b then set_q ii else constT ()) =
          seqT (read_cpsr ii)
          (\cpsr. write_cpsr ii (if b then cpsr with Q := T else cpsr))`,
  SRW_TAC [] [FUN_EQ_THM, APPLY_UPDATE_ID, arm_state_component_equality,
    set_q_def, constT_def, condT_def, seqT_def,
    write_cpsr_def, write__psr_def, writeT_def,
    read_cpsr_def, read_cpsr_def, read__psr_def, readT_def]);

val ARM_WRITE_STATUS_Q = Q.store_thm("ARM_WRITE_STATUS_Q",
  `!b s.
     (if b then ARM_WRITE_STATUS psrQ T s else s) =
     ARM_WRITE_STATUS psrQ (b \/ ARM_READ_STATUS psrQ s) s`,
  SRW_TAC [] [ARM_WRITE_STATUS_def, ARM_READ_STATUS_def,
    ARM_WRITE_CPSR_def, ARM_READ_CPSR_def, arm_state_component_equality]
    \\ MATCH_MP_TAC (GSYM UPDATE_APPLY_IMP_ID)
    \\ SRW_TAC [] [ARMpsr_component_equality]);

(* ------------------------------------------------------------------------- *)
(* Evaluation for alignment and other miscellany                             *)
(* ------------------------------------------------------------------------- *)

val UPDATE_ID = Q.store_thm("UPDATE_ID",
  `!a b c. (a =+ b) o (a =+ c) = a =+ b`,
  SRW_TAC [] [UPDATE_def,FUN_EQ_THM]);

val UPDATE_ID_o = Q.store_thm("UPDATE_ID_o",
  `(!a b. (a =+ b) o (a =+ b) = (a =+ b)) /\
   (!a b g. (a =+ b) o ((a =+ b) o g) = (a =+ b) o g)`,
  SRW_TAC [] [FUN_EQ_THM, UPDATE_def]);

val UPDATE_ID_o2 = Q.store_thm("UPDATE_ID_o2",
  `(!a b c. (a =+ b) o (a =+ c) = (a =+ b)) /\
   (!a b c g. (a =+ b) o ((a =+ c) o g) = (a =+ b) o g)`,
  SRW_TAC [] [FUN_EQ_THM, UPDATE_def]);

val FST_SHIFT_C = Q.store_thm("FST_SHIFT_C",
  `(!w s. s <> 0 ==> (FST (LSL_C (w, s)) = w << s)) /\
   (!w s. s <> 0 ==> (FST (LSR_C (w, s)) = w >>> s)) /\
   (!w s. s <> 0 ==> (FST (ASR_C (w, s)) = w >> s)) /\
   (!w s. s <> 0 ==> (FST (ROR_C (w, s)) = w #>> s)) /\
   (!w s. (if s = 0 then w else w << s) = w << s) /\
   (!w s. (if s = 0 then w else w >>> s) = w >>> s) /\
   (!w s. (if s = 0 then w else w >> s) = w >> s) /\
   (!w s. (if s = 0 then w else w #>> s) = w #>> s)`,
  SRW_TAC [] [LSL_C_def, LSR_C_def, ASR_C_def, ROR_C_def] \\ SRW_TAC [] []);

val EXTRACT_ROR = Q.store_thm("EXTRACT_ROR",
  `(!a:word32. (( 7 >< 0 ) (a #>> 8 ) = (15 >< 8 ) a : word8)) /\
   (!a:word32. (( 7 >< 0 ) (a #>> 16) = (23 >< 16) a : word8)) /\
   (!a:word32. (( 7 >< 0 ) (a #>> 24) = (31 >< 24) a : word8)) /\
   (!a:word32. ((23 >< 16) (a #>> 8)  = (31 >< 24) a : word8)) /\
   (!a:word32. ((23 >< 16) (a #>> 16) = ( 7 >< 0 ) a : word8)) /\
   (!a:word32. ((23 >< 16) (a #>> 24) = (15 >< 8 ) a : word8)) /\
   (!a:word32. ((15 >< 0 ) (a #>> 8 ) = (23 >< 8 ) a : word16)) /\
   (!a:word32. ((15 >< 0 ) (a #>> 16) = (31 >< 16) a : word16)) /\
   (!a:word32. ((31 >< 16) (a #>> 16) = (15 >< 0 ) a : word16))`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] []);

val SInt_0 = Q.store_thm("SInt_0",
  `SInt 0w = 0`, SRW_TAC [] [integer_wordTheory.w2i_def]);

val align_1 = save_thm("align_1",
  simpLib.SIMP_PROVE (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [align_def]
    ``align(a,1) = a``);

val align_248 = save_thm("align_248",
  numLib.REDUCE_RULE
    (Drule.LIST_CONJ (List.map (fn t => Q.SPEC t align_slice) [`1`,`2`,`3`])));

val aligned_248 = Q.store_thm("aligned_248",
  `(!a:word32. aligned(a,2) = ~word_lsb a) /\
   (!a:word32. aligned(a,4) = ((1 >< 0) a = 0w:word2)) /\
   (!a:word32. aligned(a,8) = ((2 >< 0) a = 0w:word3))`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_def, align_248]);

val align_lem = Q.prove(
  `(!b:word32. align(b,2) + (0 -- 0) b = b) /\
   (!b:word32. align(b,4) + (1 -- 0) b = b) /\
   (!b:word32. align(b,8) + (2 -- 0) b = b)`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);

val align_lem2 =
  METIS_PROVE [align_lem, WORD_ADD_ASSOC]
  ``(!a:word32 b. align(a,2) + b = align(a,2) + align(b,2) + (0 -- 0) b) /\
    (!a:word32 b. align(a,4) + b = align(a,4) + align(b,4) + (1 -- 0) b) /\
    (!a:word32 b. align(a,8) + b = align(a,8) + align(b,8) + (2 -- 0) b)``;

val align_lem2b =
  METIS_PROVE [align_lem, WORD_ADD_ASSOC]
  ``(!a:word32 b. align(a,4) + b = align(a,4) + align(b,2) + (0 -- 0) b)``;

val align_2_align_4 = Q.store_thm("align_2_align_4",
  `!a:word32. align(align(a,4),2) = align(a,4)`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);

val align_aligned = Q.prove(
  `(!a:word32 b. align(align(a,2) + b,2) = align(a,2) + align(b,2)) /\
   (!a:word32 b. align(align(a,4) + b,4) = align(a,4) + align(b,4)) /\
   (!a:word32 b. align(align(a,8) + b,8) = align(a,8) + align(b,8))`,
  REPEAT STRIP_TAC
    \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [align_lem2]))
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]
    \\ REWRITE_TAC [GSYM WORD_ADD_LSL]
    \\ Q.PAT_ABBREV_TAC `x:word32 = (f a + g b)`
    << [`x << 1 + (0 >< 0) b = x << 1 || (0 >< 0) b`
        by (MATCH_MP_TAC WORD_ADD_OR \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []),
        `x << 2 + (1 >< 0) b = x << 2 || (1 >< 0) b`
        by (MATCH_MP_TAC WORD_ADD_OR \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []),
        `x << 3 + (2 >< 0) b = x << 3 || (2 >< 0) b`
        by (MATCH_MP_TAC WORD_ADD_OR \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [])]
    \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] []
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []);

val align_aligned2 = Q.store_thm("align_aligned2",
  `(!a:word32 b. align(align(a,4) + b,2) = align(a,4) + align(b,2))`,
  REPEAT STRIP_TAC
    \\ CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [align_lem2b]))
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]
    \\ REWRITE_TAC [GSYM WORD_ADD_LSL,
         wordsLib.WORD_DECIDE ``(a:word32) << 2 = a << 1 << 1``]
    \\ Q.ABBREV_TAC `x:word32 = ((31 >< 1) b + (31 >< 2) a << 1)`
    \\ `x << 1 + (0 >< 0) b = x << 1 || (0 >< 0) b`
        by (MATCH_MP_TAC WORD_ADD_OR \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [])
    \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] []
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []);

val align_aligned = save_thm("align_aligned",
  CONJ align_aligned2 align_aligned);

val align_sum = save_thm("align_sum",
  REWRITE_RULE [GSYM align_aligned, WORD_ADD_ASSOC] align_lem2);

val aligned_thm1 = Q.prove(
  `(!a:word32 b. aligned(a,2) /\ aligned(b,2) ==> (align (a + b,2) = a + b)) /\
   (!a:word32 b. aligned(a,4) /\ aligned(b,4) ==> (align (a + b,4) = a + b)) /\
   (!a:word32 b. aligned(a,8) /\ aligned(b,8) ==> (align (a + b,8) = a + b))`,
  METIS_TAC [aligned_def, align_aligned]);

val aligned_thm2 = Q.prove(
  `!a:word32. aligned(a,4) ==> aligned(a,2)`,
  METIS_TAC [aligned_def, align_2_align_4]);

val aligned_thm = save_thm("aligned_thm",
  Drule.LIST_CONJ [aligned_thm2, aligned_thm1,
    aligned_def |> Drule.SPEC_ALL |> EQ_IMP_RULE |> fst |> GSYM |> GEN_ALL]);

val align_aligned3 = Q.store_thm("align_aligned3",
  `!pc x: word32.
      aligned (pc + 8w + x, 4) /\ aligned (pc, 4) ==>
      aligned (x + align (pc, 4) + 8w, 4)`,
  METIS_TAC [aligned_thm, WORD_ADD_COMM, WORD_ADD_ASSOC]);

val aligned_align = Q.store_thm("aligned_align",
  `(!a:word32. aligned(a,1)) /\
   (!a:word32. aligned(align(a,2),2)) /\
   (!a:word32. aligned(align(a,4),2)) /\
   (!a:word32. aligned(align(a,4),4)) /\
   (!a:word32. aligned(align(a,8),8))`,
  METIS_TAC [aligned_def,aligned_thm,align_1,align_id_248]);

val aligned_sum = Q.store_thm("aligned_sum",
  `(!a:word32 b. aligned(align(a,2) + b,2) = aligned(b,2)) /\
   (!a:word32 b. aligned(align(a,4) + b,2) = aligned(b,2)) /\
   (!a:word32 b. aligned(align(a,4) + b,4) = aligned(b,4))`,
   SIMP_TAC (srw_ss()++wordsLib.WORD_ARITH_EQ_ss)
        [align_aligned, align_aligned2, aligned_def]);

val align_bits = Q.store_thm("align_bits",
  `(!a:word32. (0 -- 0) (align(a,2)) = 0w) /\
   (!a:word32. (1 -- 0) (align(a,4)) = 0w) /\
   (!a:word32. (2 -- 0) (align(a,8)) = 0w)`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);

val align_bits_sum = Q.store_thm("align_bits_sum",
  `!a:word32 n. (1 >< 0) (align (a,4) + n) = (1 >< 0) n : word2`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []
    \\ SIMP_TAC (srw_ss()) [Once WORD_ADD_BIT]
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []);

val align_or = Q.prove(
  `(!a:word32. align (a,2) + 1w = align (a,2) || 1w) /\
   (!a:word32. align (a,4) + 1w = align (a,4) || 1w) /\
   (!a:word32. align (a,4) + 2w = align (a,4) || 2w) /\
   (!a:word32. align (a,4) + 3w = align (a,4) || 3w)`, (* /\
   (!a:word32. align (a,8) + 1w = align (a,8) || 1w) /\
   (!a:word32. align (a,8) + 2w = align (a,8) || 2w) /\
   (!a:word32. align (a,8) + 3w = align (a,8) || 3w) /\
   (!a:word32. align (a,8) + 4w = align (a,8) || 4w) /\
   (!a:word32. align (a,8) + 5w = align (a,8) || 5w) /\
   (!a:word32. align (a,8) + 6w = align (a,8) || 6w) /\
   (!a:word32. align (a,8) + 7w = align (a,8) || 7w)`, *)
  REPEAT STRIP_TAC \\ MATCH_MP_TAC WORD_ADD_OR
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [align_248]);

val align_neq = Q.prove(
  `(!a:word32 b. align (a,2) + 0w <> align (b,2) + 1w) /\
   (!a:word32 b. align (a,2) + 1w <> align (b,2) + 0w) /\
   (!a:word32 b. align (a,4) + 0w <> align (b,4) + 1w) /\
   (!a:word32 b. align (a,4) + 0w <> align (b,4) + 2w) /\
   (!a:word32 b. align (a,4) + 0w <> align (b,4) + 3w) /\
   (!a:word32 b. align (a,4) + 1w <> align (b,4) + 0w) /\
   (!a:word32 b. align (a,4) + 1w <> align (b,4) + 2w) /\
   (!a:word32 b. align (a,4) + 1w <> align (b,4) + 3w) /\
   (!a:word32 b. align (a,4) + 2w <> align (b,4) + 0w) /\
   (!a:word32 b. align (a,4) + 2w <> align (b,4) + 1w) /\
   (!a:word32 b. align (a,4) + 2w <> align (b,4) + 3w) /\
   (!a:word32 b. align (a,4) + 3w <> align (b,4) + 0w) /\
   (!a:word32 b. align (a,4) + 3w <> align (b,4) + 1w) /\
   (!a:word32 b. align (a,4) + 3w <> align (b,4) + 2w)`,
  SRW_TAC [] [align_or] \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [align_248]);

val align_neq = save_thm("align_neq", SIMP_RULE (srw_ss()) [] align_neq);

val align2_add_times2 = Q.store_thm("align2_add_times2",
  `!a:word32 b.
     align (align (a,2) + 4w + 2w * b,2) = align (a,2) + 4w + 2w * b`,
  REPEAT STRIP_TAC
    \\ REWRITE_TAC
         [wordsLib.WORD_DECIDE ``a + 4w + 2w * b = a + 2w * (b + 2w)``]
    \\ Q.ABBREV_TAC `c = b + 2w:word32`
    \\ SRW_TAC [wordsLib.WORD_MUL_LSL_ss] [align_aligned]
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss,wordsLib.WORD_BIT_EQ_ss] [align_248]);

val align_1comp = Q.store_thm("align_1comp",
  `!a:word32. ~align(a,4) = align(~a,4) + 3w`,
  REWRITE_TAC [align_or] \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [align_248]);

val align_relative_thm1 = Q.prove(
  `(!a:word32 b c.
     (b = -c) ==> ((a = align (a + b, 2) + c) = aligned (a + b, 2))) /\
   (!a:word32 b c.
     (b = -c) ==> ((a = align (a + b, 4) + c) = aligned (a + b, 4))) /\
   (!a:word32 b c.
     (b = -c) ==> ((a = align (a + b, 8) + c) = aligned (a + b, 8)))`,
  REPEAT STRIP_TAC
    \\ SRW_TAC [wordsLib.WORD_ARITH_EQ_ss] [aligned_def]);

val align_relative_thm2 = Q.prove(
  `(!a:word32 b c.
     (b = c + 1w) ==> ((a = c - align (~a + b, 4)) = aligned (c - a, 4))) /\
   (!a:word32 b. ((a = b - align (b - a, 4)) = aligned (b - a, 4)))`,
  SRW_TAC [] [WORD_EQ_SUB_LADD, WORD_NOT]
    \\ SRW_TAC [wordsLib.WORD_ARITH_EQ_ss] [aligned_def]
    \\ CONV_TAC wordsLib.WORD_ARITH_CONV);

val word_add_plus1 = Q.prove(
  `!a b. n2w (w2n a + w2n b + 1) = a + b + 1w : word32`,
  SRW_TAC [] [word_add_def]
    \\ METIS_TAC [arithmeticTheory.MOD_PLUS, DECIDE ``0 < 4294967296``,
         simpLib.SIMP_PROVE (srw_ss()) [] ``1 = 1 MOD 4294967296``]);

val align_relative_thm3 = Q.prove(
  `(!a:word32 b d c.
     (b = -d) ==> ((a = align (FST (add_with_carry(a,b,c)),4) + d +
                        -(if c then 1w else 0w)) =
                   aligned (FST (add_with_carry(a,b,c)),4))) /\
   (!a:word32 b c.
     ((a = b + (if c then 0w else -1w) +
           -align (FST (add_with_carry(~a,b,c)),4)) =
      aligned (FST (add_with_carry(~a,b,c)),4))) /\
   (!a:word32 b d c.
     (b = ~d) ==> ((a = align (FST (add_with_carry(a,b,c)),4) + d +
                        (if c then 0w else 1w)) =
                   aligned (FST (add_with_carry(a,b,c)),4)))`,
  REPEAT STRIP_TAC \\ Cases_on `c`
    \\ SRW_TAC [] [FST_ADD_WITH_CARRY, align_relative_thm1]
    \\ SRW_TAC [boolSimps.LET_ss, wordsLib.WORD_ARITH_EQ_ss]
         [word_add_plus1, add_with_carry_def, aligned_def]
    \\ CONV_TAC wordsLib.WORD_ARITH_CONV);

val align_relative_thm = save_thm("align_relative_thm",
  Drule.LIST_CONJ (Drule.CONJUNCTS align_relative_thm1 @
   [align_relative_thm2 |> REWRITE_RULE [word_sub_def],
    align_relative_thm3 |> REWRITE_RULE [EVAL ``-1w:word32``],
    align_relative_thm3
      |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
      |> Q.INST [`b:word32` |-> `0w:word32`, `d:word32` |-> `0w:word32`]
      |> SIMP_RULE std_ss [WORD_NEG_0, WORD_ADD_0],
    align_relative_thm3
      |> Thm.CONJUNCT2 |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
      |> Q.INST [`b:word32` |-> `0w:word32`]
      |> SIMP_RULE std_ss [EVAL ``-1w:word32``, WORD_ADD_0],
    align_relative_thm3
      |> Drule.CONJUNCTS |> last |> Drule.SPEC_ALL
      |> Q.INST [`b:word32` |-> `0xFFFFFFFFw:word32`,
                 `d:word32` |-> `0w:word32`]
      |> SIMP_RULE std_ss [EVAL ``0xFFFFFFFFw = ~0w:word32``, WORD_ADD_0],
    align_relative_thm2
      |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
      |> Q.INST [`b:word32` |-> `1w:word32`, `c:word32` |-> `0w:word32`]
      |> SIMP_RULE std_ss [WORD_SUB_LZERO, WORD_ADD_0]]));

val align_relative_add_with_carry = Q.prove(
  `(!a:word32 b c d.
     (b = -d) ==>
     (FST (add_with_carry (a,b,c)) + -1w * (if c then 1w else 0w) + d = a)) /\
   (!a:word32 b c d.
     (b = ~d) ==>
     (FST (add_with_carry (a,b,c)) + (if c then 0w else 1w) + d = a)) /\
   (!a:word32 b c.
     (-1w * FST (add_with_carry (-1w * a + -1w,b,c)) +
      (if c then 0w else 0xFFFFFFFFw) + b = a)) /\
   (!a:word32 b c d.
     (b = -d) ==>
     (d + FST (add_with_carry (a,b,c)) + -1w * (if c then 1w else 0w) = a)) /\
   (!a:word32 b c d.
     (b = ~d) ==>
     (d + FST (add_with_carry (a,b,c)) + (if c then 0w else 1w) = a)) /\
   (!a:word32 b c.
     (b + -1w * FST (add_with_carry (-1w * a + -1w,b,c)) +
      (if c then 0w else 0xFFFFFFFFw) = a)) /\
   (!a:word32 b c d e.
     (b = -(d + e)) ==>
     (d + FST (add_with_carry (a,b,c)) +
      -1w * (if c then 1w else 0w) + e = a)) /\
   (!a:word32 b c d e.
     (b = ~(d + e)) ==>
     (d + FST (add_with_carry (a,b,c)) + (if c then 0w else 1w) + e = a)) /\
   (!a:word32 b c.
     (b + -1w * FST (add_with_carry (-1w * a + -1w,b + 8w,c)) +
      (if c then 0w else 0xFFFFFFFFw) + 8w = a)) /\
   (!a:word32 b c d.
     (b = -d) ==>
     (FST (add_with_carry (a,b,c)) + d + -1w * (if c then 1w else 0w) = a)) /\
   (!a:word32 b c d.
     (b = ~d) ==>
     (FST (add_with_carry (a,b,c)) + d + (if c then 0w else 1w) = a)) /\
   (!a:word32 b c.
     (-1w * FST (add_with_carry (-1w * a + -1w,b,c)) +
      b + (if c then 0w else 0xFFFFFFFFw) = a))`,
  REPEAT STRIP_TAC \\ Cases_on `c` \\ SRW_TAC [] [FST_ADD_WITH_CARRY]
    \\ SRW_TAC [boolSimps.LET_ss, wordsLib.WORD_ARITH_EQ_ss]
         [word_add_plus1, add_with_carry_def]);

val align_relative_add_with_carry = save_thm("align_relative_add_with_carry",
  Drule.LIST_CONJ
    [align_relative_add_with_carry,
     align_relative_add_with_carry
       |> Thm.CONJUNCT2 |> Thm.CONJUNCT2 |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
       |> Q.INST [`b:word32` |-> `0w:word32`]
       |> SIMP_RULE std_ss [WORD_ADD_0]
       |> GEN_ALL,
     align_relative_add_with_carry
       |> Thm.CONJUNCT2 |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
       |> Q.INST [`b:word32` |-> `0xFFFFFFFFw:word32`,
                  `d:word32` |-> `0w:word32`]
       |> SIMP_RULE std_ss [EVAL ``0xFFFFFFFFw = ~0w:word32``, WORD_ADD_0]
       |> GEN_ALL,
     align_relative_add_with_carry
       |> Thm.CONJUNCT1 |> Drule.SPEC_ALL
       |> Q.INST [`b:word32` |-> `0w:word32`, `d:word32` |-> `0w:word32`]
       |> SIMP_RULE std_ss [WORD_NEG_0, WORD_ADD_0]
       |> GEN_ALL]);

val aligned_con_thm = Q.prove(
   `!n a:word32. 0 < n ==>
      (aligned((if aligned(a + a,n) then a else 0w) +
               (if aligned(a + a,n) then a else 0w),n))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]);

val aligned_con_thms = save_thm("aligned_con_thms",
  Drule.LIST_CONJ
    (List.map (fn t => aligned_con_thm
                  |> Q.SPEC t
                  |> SIMP_RULE std_ss []) [`2`,`4`]));

val aligned_con_plus4_thm = Q.store_thm("aligned_con_plus4_thm",
   `!a:word32.
      (aligned((if aligned(a + a,4) then a else 0w) +
               (if aligned(a + a,4) then a else 0w) + 4w,4))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]
    \\ METIS_TAC [aligned_def, align_aligned, EVAL ``align(4w:word32,4)``]);

val aligned_con_shift_thm = Q.prove(
  `!n f:bool[32] # num -> bool[32] # bool x a:word32.
      0 < n /\ x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      (aligned((if aligned(a + FST (f (a,x)),n) then a else 0w) +
               FST (f (if aligned(a + FST (f (a,x)),n) then a else 0w,x)),n))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]);

val aligned_con_shift_neg_thm = Q.prove(
  `!n f:bool[32] # num -> bool[32] # bool x a:word32.
     0 < n /\ x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     (aligned((if aligned(a + -FST (f (a,x)),n) then a else 0w) +
              -FST (f (if aligned(a + -FST (f (a,x)),n) then a else 0w,x)),n))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]);

val aligned_con_shift_thm2 = Q.SPEC `2` aligned_con_shift_thm;
val aligned_con_shift_thm4 = Q.SPEC `4` aligned_con_shift_thm;
val aligned_con_shift_neg_thm2 = Q.SPEC `2` aligned_con_shift_neg_thm;
val aligned_con_shift_neg_thm4 = Q.SPEC `4` aligned_con_shift_neg_thm;

val NUMERAL_NOT_ZERO = Q.prove(
  `(!n. NUMERAL (BIT1 n) <> 0n) /\ (!n. NUMERAL (BIT2 n) <> 0n)`,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
         arithmeticTheory.BIT1, arithmeticTheory.BIT2]
    \\ DECIDE_TAC);

val NUMERAL_FST_SHIFT_C = Drule.LIST_CONJ
  (List.map (fn t => CONJ (Q.SPECL [`0w`,`NUMERAL (BIT1 n)`] t)
                     (Q.SPECL [`0w`,`NUMERAL (BIT2 n)`] t)
               |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,ZERO_SHIFT]
               |> GEN_ALL)
    (List.take(Drule.CONJUNCTS FST_SHIFT_C,4)));

val aligned_con_shift_thms = save_thm("aligned_con_shift_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                          (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
     [aligned_con_shift_thm2,aligned_con_shift_thm4,
      aligned_con_shift_neg_thm2, aligned_con_shift_neg_thm4])));

val aligned_con_rrx_thm = Q.prove(
  `!n b a:word32. n IN {2; 4} ==>
     (aligned((if aligned(a + SND (word_rrx (b,a)),n) then a else 0w) +
              SND (word_rrx
                (b,if aligned(a + SND (word_rrx (b,a)),n) then a else 0w)),n))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]);

val aligned_con_rrx_neg_thm = Q.prove(
  `!n b a:word32. n IN {2; 4} ==>
    (aligned((if aligned(a + -SND (word_rrx (b,a)),n) then a else 0w) +
             -SND (word_rrx
               (b,if aligned(a + -SND (word_rrx (b,a)),n) then a else 0w)),n))`,
  SRW_TAC [] [] \\ EVAL_TAC \\ SRW_TAC [] [arithmeticTheory.ZERO_DIV]);

val aligned_con_rrx_thms = save_thm("aligned_con_rrx_thms",
  Drule.LIST_CONJ
     [aligned_con_rrx_thm |> Q.SPEC `2`,
      aligned_con_rrx_thm |> Q.SPEC `4`,
      aligned_con_rrx_neg_thm |> Q.SPEC `2`,
      aligned_con_rrx_neg_thm |> Q.SPEC `4`]
    |> SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) []);

(* ------------------------------------------------------------------------- *)

val aligned_bx_def = zDefine `aligned_bx a = (1 >< 0) a <> (0b10w:word2)`;

val aligned_bx_n2w = save_thm("aligned_bx_n2w",
let val thm = aligned_bx_def |> Q.SPEC `n2w a` |> GEN_ALL in
  CONJ (INST_TYPE [alpha |-> ``:32``] thm)
       (INST_TYPE [alpha |-> ``:8``] thm)
    |> SIMP_RULE (srw_ss()) [bitTheory.BITS_ZERO3, word_extract_n2w]
end);

val _ = computeLib.add_persistent_funs ["aligned_bx_n2w"];

val aligned_bx_0w = EVAL ``aligned_bx (0w:word32)``;
val aligned_bx_1w = EVAL ``aligned_bx (1w:word32)``;
val aligned_bx_m1w = EVAL ``aligned_bx (-1w:word32)``;

val align_bx_bit = Q.store_thm("align_bx_bit",
  `(!a:word32. (~a) ' 0 = ~a ' 0) /\
   (!a:word32 n. (a && n2w n) ' 0 = a ' 0 /\ ODD n) /\
   (!a:word32 n. (a || n2w n) ' 0 = a ' 0 \/ ODD n) /\
   (!a:word32 n. (a ?? n2w n) ' 0 = a ' 0 <> ODD n) /\
   (!a:word32 n. (a + n2w n) ' 0  = a ' 0 <> ODD n)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [WORD_ADD_BIT0, n2w_def, BIT0_ODD]);

val aligned_bx_thm = Q.store_thm("aligned_bx_thm",
  `!a:word32. aligned_bx a = (~a ' 0 ==> ~a ' 1)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_bx_def] \\ METIS_TAC []);

val aligned_bx_branch = Q.store_thm("aligned_bx_branch",
  `!a:word32. aligned_bx ((if aligned_bx a then a else 0w))`,
  SRW_TAC [] [aligned_bx_def, aligned_bx_0w]);

val aligned_bx_1comp = Q.store_thm("aligned_bx_1comp",
  `!a:word32. aligned_bx (~(if aligned_bx (~a) then a else 0w))`,
  SRW_TAC [] [aligned_bx_def]);

val aligned_bx_2comp = Q.store_thm("aligned_bx_2comp",
  `!a:word32. aligned_bx (-(if aligned_bx (-a) then a else 0w))`,
  SRW_TAC [] [aligned_bx_def]);

val aligned_bx_and = Q.store_thm("aligned_bx_and",
  `!a:word32 b. aligned_bx ((if aligned_bx (a && b) then a else 0w) && b)`,
  SRW_TAC [] [aligned_bx_def]);

val aligned_bx_eor = Q.store_thm("aligned_bx_eor",
  `!a:word32 b. aligned_bx ((if aligned_bx (a ?? b) then a else b) ?? b)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_bx_def] \\ METIS_TAC []);

val aligned_bx_orr = Q.prove(
  `!a:word32 b. aligned_bx ((if aligned_bx (a || b) then a else 1w) || b)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_bx_def] \\ METIS_TAC []);

val aligned_bx_orr = save_thm("aligned_bx_orr",
  CONJ (aligned_bx_orr |> Q.SPECL [`a`,`0w`] |> SIMP_RULE (srw_ss()) [])
       aligned_bx_orr);

val word_plus8 = Q.prove(
  `!pc:word32. align (pc,4) + 8w = (align (pc,4) >>> 2 + 2w) << 2`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);

val aligned_bx_and_pc = Q.store_thm("aligned_bx_and_pc",
  `(!pc:word32 b. aligned_bx ((align (pc,4) + 8w) && b)) /\
   !pc:word32 b. ~(((align (pc,4) + 8w) && b) ' 0)`,
  NTAC 2 STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] [aligned_bx_def]);

val aligned_bx_bic_pc = Q.store_thm("aligned_bx_bic_pc",
  `!pc:word32 b. (b && ~(align (pc,4) + 8w)) ' 0 = b ' 0`,
  STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] [aligned_bx_def]);

val aligned_bx_eor_pc = Q.store_thm("aligned_bx_eor_pc",
  `(!pc:word32 b. aligned_bx ((align (pc,4) + 8w) ?? b) = aligned_bx b) /\
   !pc:word32 b. ((align (pc,4) + 8w) ?? b) ' 0 = b ' 0`,
  NTAC 2 STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] [aligned_bx_def]);

val aligned_bx_orr_pc = Q.store_thm("aligned_bx_orr_pc",
  `(!pc:word32 b. aligned_bx ((align (pc,4) + 8w) || b) = aligned_bx b) /\
   !pc:word32 b. ((align (pc,4) + 8w) || b) ' 0 = b ' 0`,
  NTAC 2 STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] [aligned_bx_def]);

val eor_bit0 = Q.prove(
  `(!a b:word32. (b + (a ?? 1w)) ' 0 = ~(a + b) ' 0) /\
    !a b:word32. (b + ~(a ?? 1w)) ' 0 = ~(~a + b) ' 0`,
  SRW_TAC [] [WORD_ADD_BIT0,
              wordsLib.WORD_DECIDE ``!a:word32. (~(a ?? 1w)) ' 0 = ~(~a) ' 0``,
              wordsLib.WORD_DECIDE ``!a:word32. (a ?? 1w) ' 0 = ~a ' 0``]
    \\ METIS_TAC []);

val eor_bit0_cor =
  eor_bit0 |> Drule.CONJUNCTS
           |> List.map (SIMP_RULE (srw_ss()) [] o Q.SPECL [`a`,`b + 1w`])
           |> Drule.LIST_CONJ;

val aligned_bx_add_with_carry = Q.store_thm("aligned_bx_add_with_carry",
  `(!a:word32 b c.
      aligned_bx (FST (add_with_carry
         (if aligned_bx (FST (add_with_carry(a,b,c))) then
            a
          else
            a ?? 1w,b,c)))) /\
   (!a:word32 b c.
      aligned_bx (FST (add_with_carry
         (~if aligned_bx (FST (add_with_carry(~a,b,c))) then
             a
           else
             a ?? 1w,b,c))))`,
  SRW_TAC [] [aligned_bx_def] \\ Cases_on `c`
    \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [add_with_carry_def, GSYM word_add_def, word_add_plus1,
          GSYM aligned_bx_def, aligned_bx_thm]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss)
         [eor_bit0, eor_bit0_cor]);

val aligned_bx_add_sub = Q.prove(
  `!a:word32 b. aligned_bx ((if aligned_bx (a + b) then a else a ?? 1w) + b)`,
  SRW_TAC [] [aligned_bx_def]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss)
         [GSYM aligned_bx_def, aligned_bx_thm, eor_bit0]);

val aligned_bx_rev_add_sub = Q.prove(
  `!a:word32 b. aligned_bx (b + -(if aligned_bx (b + -a) then a else a ?? 1w))`,
  SRW_TAC [] [aligned_bx_def, WORD_NEG]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss)
         [GSYM aligned_bx_def, aligned_bx_thm, eor_bit0, eor_bit0_cor]);

val aligned_bx_rsb = Q.prove(
  `!a:word32 b.
      aligned_bx (~(if aligned_bx (~a + b) then a else a ?? 1w) + b)`,
  SRW_TAC [] [aligned_bx_def]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss)
         [GSYM aligned_bx_def, aligned_bx_thm, eor_bit0]);

val aligned_bx_add_sub = save_thm("aligned_bx_add_sub",
  Drule.LIST_CONJ
    [aligned_bx_add_sub |> Q.SPECL [`a`,`0w`] |> SIMP_RULE (srw_ss()) [word_0],
     aligned_bx_rev_add_sub |> Q.SPECL [`a`,`0w`]
                            |> SIMP_RULE std_ss [WORD_ADD_0],
     aligned_bx_rsb |> Q.SPECL [`a`,`0w`] |> SIMP_RULE (srw_ss()) [],
     aligned_bx_add_sub, aligned_bx_rev_add_sub, aligned_bx_rsb]);

val aligned_bx_add_sub_pc = Q.prove(
  `(!a:word32 b. (align(a,4) + b) ' 0 = b ' 0) /\
    !a:word32 b. aligned_bx (align(a,4) + b) = aligned_bx b`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss]
          [aligned_bx_thm, align_248, WORD_ADD_BIT0, Once WORD_ADD_BIT]
     \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []);

val extract_bit0_plus1 = Q.prove(
  `!b:word32. ((0 >< 0) b + 1w:word32) ' 1 <=> b ' 0`,
  STRIP_TAC
    \\ `((0 >< 0) b = 0w:word32) \/ ((0 >< 0) b = 1w:word32)`
    by SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []);

val aligned_bx_add_sub_pc2 = Q.prove(
  `(!a:word32 b. (align(a,4) + 8w + b) ' 0 = b ' 0) /\
   (!a:word32 b. (~(align(a,4) + 8w) + b) ' 0 = ~b ' 0) /\
   (!a:word32 b. aligned_bx (align(a,4) + 8w + b) = aligned_bx b) /\
    !a:word32 b. aligned_bx (~(align(a,4) + 8w) + b) =
                   ((1 >< 0) b <> 3w:word2)`,
  NTAC 3 STRIP_TAC \\ REPEAT GEN_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (a,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss]
          [aligned_bx_thm, align_248, WORD_ADD_BIT0, Once WORD_ADD_BIT,
           extract_bit0_plus1,
           wordsLib.WORD_DECIDE ``!a:word32. (0 >< 0) (~(a << 2)) = 1w:word32``,
           wordsLib.WORD_DECIDE ``!a:word32. ~(a << 2) ' 1``,
           wordsLib.WORD_DECIDE ``!a:word32. ~(a << 2) ' 0``,
           wordsLib.WORD_DECIDE ``!a:word32. (~(a << 2)) ' 1``,
           wordsLib.WORD_DECIDE ``!a:word32. (~(a << 2)) ' 0``]
     \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []
     \\ METIS_TAC []);

val aligned_bx_add_sub_pc3 = Q.prove(
  `!a:word32 pc.
      aligned_bx
         ((if aligned_bx (a + -(align(pc,4) + 8w)) then a else 0w) +
           -(align(pc,4) + 8w))`,
  NTAC 2 STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] [aligned_bx_def]);

val aligned_bx_add_sub_pc = save_thm("aligned_bx_add_sub_pc",
  Drule.LIST_CONJ
    [CONJ (aligned_bx_add_sub_pc |> Thm.CONJUNCT1 |> Q.SPECL [`a`,`0w`])
          (aligned_bx_add_sub_pc |> Thm.CONJUNCT2 |> Q.SPECL [`a`,`0w`])
       |> SIMP_RULE (srw_ss()) [word_0, aligned_bx_0w],
     aligned_bx_add_sub_pc, aligned_bx_add_sub_pc2, aligned_bx_add_sub_pc3]);

val aligned_bx_add_with_carry_pair = Q.store_thm(
  "aligned_bx_add_with_carry_pair",
  `(!a:word32 c.
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,a,c))) then a else 0w,
           if aligned_bx (FST (add_with_carry (a,a,c))) then a else 0w,
           c)))) /\
   (!a:word32 c.
     aligned_bx
       (FST (add_with_carry
          (~if aligned_bx (FST (add_with_carry (~a,a,c))) then a else 0w,
           if aligned_bx (FST (add_with_carry (~a,a,c))) then a else 0w,
           c)))) /\
   (!a:word32 c.
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,~a,c))) then a else 0w,
           ~if aligned_bx (FST (add_with_carry (a,~a,c))) then a else 0w,
           c))))`,
  SRW_TAC [] [aligned_bx_def]
    \\ SRW_TAC [boolSimps.LET_ss] [add_with_carry_def]);

val aligned_bx_add_pair = Q.store_thm("aligned_bx_add_pair",
  `!a:word32.
      aligned_bx
        ((if aligned_bx (a + a) then a else 0w) +
         (if aligned_bx (a + a) then a else 0w))`,
  SRW_TAC [] [aligned_bx_def]);

val aligned_bx_shift_pair = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a && FST (f (a,x))) then a else 0w) &&
         FST (f (if aligned_bx (a && FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a && ~FST (f (a,x))) then a else 0w) &&
         ~FST (f (if aligned_bx (a && ~FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a ?? FST (f (a,x))) then a else 0w) ??
         FST (f (if aligned_bx (a ?? FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a || FST (f (a,x))) then a else 0w) ||
         FST (f (if aligned_bx (a || FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (f (if aligned_bx (FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (~FST (f (if aligned_bx (~FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (-FST (f (if aligned_bx (-FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a + FST (f (a,x))) then a else 0w) +
         FST (f (if aligned_bx (a + FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        ((if aligned_bx (a + -FST (f (a,x))) then a else 0w) +
         -FST (f (if aligned_bx (a + -FST (f (a,x))) then a else 0w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (f (if aligned_bx (FST (f (a,x)) + -a) then a else 0w,x)) +
         -if aligned_bx (FST (f (a,x)) + -a) then a else 0w))`,
  SRW_TAC [] [aligned_bx_def]);

val aligned_bx_rrx_pair = Q.store_thm("aligned_bx_rrx_pair",
  `(!x a:word32.
      aligned_bx
        ((if aligned_bx (a && SND (word_rrx (x,a))) then a else 0w) &&
         SND (word_rrx (x,if aligned_bx (a && SND (word_rrx (x,a)))
                          then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        ((if aligned_bx (a && ~SND (word_rrx (x,a))) then a else 0w) &&
         ~SND (word_rrx (x,if aligned_bx (a && ~SND (word_rrx (x,a)))
                           then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        ((if aligned_bx (a ?? SND (word_rrx (x,a))) then a else 0w) ??
         SND (word_rrx (x,if aligned_bx (a ?? SND (word_rrx (x,a)))
                          then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        ((if aligned_bx (a || SND (word_rrx (x,a))) then a else 0w) ||
         SND (word_rrx (x,if aligned_bx (a || SND (word_rrx (x,a)))
                          then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        (SND (word_rrx
           (x,if aligned_bx (SND (word_rrx (x,a))) then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        (~SND (word_rrx
           (x,if aligned_bx (~SND (word_rrx (x,a))) then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        (-SND (word_rrx
           (x,if aligned_bx (-SND (word_rrx (x,a))) then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        ((if aligned_bx (a + SND (word_rrx (x,a))) then a else 0w) +
         SND (word_rrx (x,if aligned_bx (a + SND (word_rrx (x,a)))
                          then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        ((if aligned_bx (a + -SND (word_rrx (x,a))) then a else 0w) +
         -SND (word_rrx (x,if aligned_bx (a + -SND (word_rrx (x,a)))
                           then a else 0w)))) /\
   (!x a:word32.
      aligned_bx
        (SND (word_rrx (x,if aligned_bx (SND (word_rrx (x,a)) + -a)
                          then a else 0w)) +
         -if aligned_bx (SND (word_rrx (x,a)) + -a) then a else 0w))`,
  SRW_TAC [] [aligned_bx_def] \\ Cases_on `x` \\ SRW_TAC [] [word_rrx_0]);

val aligned_bx_add_with_carry_shift_pair = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,FST (f (a,x)),c)))
           then a else 0w,
           FST (f (if aligned_bx (FST (add_with_carry (a,FST (f (a,x)),c)))
                   then a else 0w,x)),
           c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          (~if aligned_bx (FST (add_with_carry (~a,FST (f (a,x)),c)))
            then a else 0w,
           FST (f (if aligned_bx (FST (add_with_carry (~a,FST (f (a,x)),c)))
                   then a else 0w,x)),
           c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,~FST (f (a,x)),c)))
           then a else 0w,
           ~FST (f (if aligned_bx (FST (add_with_carry (a,~FST (f (a,x)),c)))
                    then a else 0w,x)),
           c))))`,
  SRW_TAC [] [aligned_bx_def]
    \\ SRW_TAC [boolSimps.LET_ss] [add_with_carry_def]);

val aligned_bx_add_with_carry_rrx_pair = Q.store_thm(
  "aligned_bx_add_with_carry_rrx_pair",
  `(!x a:word32.
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,SND (word_rrx (x,a)),c)))
           then a else 0w,
           SND (word_rrx (x,
             if aligned_bx (FST (add_with_carry (a,SND (word_rrx (x,a)),c)))
             then a else 0w)),
           c)))) /\
   (!x a:word32.
     aligned_bx
       (FST (add_with_carry
          (~if aligned_bx (FST (add_with_carry (~a,SND (word_rrx (x,a)),c)))
            then a else 0w,
           SND (word_rrx (x,
             if aligned_bx (FST (add_with_carry (~a,SND (word_rrx (x,a)),c)))
             then a else 0w)),
           c)))) /\
   (!x a:word32.
     aligned_bx
       (FST (add_with_carry
          (if aligned_bx (FST (add_with_carry (a,~SND (word_rrx (x,a)),c)))
           then a else 0w,
           ~SND (word_rrx (x,
             if aligned_bx (FST (add_with_carry (a,~SND (word_rrx (x,a)),c)))
             then a else 0w)),
           c))))`,
  SRW_TAC [] [aligned_bx_def] \\ Cases_on `x`
    \\ SRW_TAC [boolSimps.LET_ss] [add_with_carry_def, word_rrx_0]);

val lem = Q.prove(
  `(!x:word32. n2w (w2n x + 4294967296) = x) /\
   (!x:word32. n2w (w2n x + 4294967295) = x + -1w) /\
   (!x:word32. n2w (w2n x + 0x80000000) = x + 0x80000000w) /\
   (!x:word32. n2w (w2n x + 0x7FFFFFFF) = x + 0x7FFFFFFFw) /\
   (!x:word32. n2w (w2n (~x) + 1) = ~x + 1w) /\
    !x:word32. n2w (w2n (x << 2) + 1) = x << 2 || 1w`,
  REPEAT STRIP_TAC
    << [
      ONCE_REWRITE_TAC [GSYM n2w_mod]
        \\ SRW_TAC [ARITH_ss] [ADD_MODULUS_LEFT,
             n2w_mod |> INST_TYPE [alpha |-> ``:32``] |> EVAL_RULE],
      SRW_TAC [] [word_add_def],
      SRW_TAC [] [word_add_def],
      SRW_TAC [] [word_add_def],
      SRW_TAC [] [word_add_def],
      `n2w (w2n (x << 2) + 1) = x << 2 + 1w` by SRW_TAC [] [word_add_def]
        \\ POP_ASSUM SUBST1_TAC
        \\ MATCH_MP_TAC WORD_ADD_OR
        \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []]);

val lem2 = Q.prove(
  `(!x:word32. (1 >< 0) (x << 2 + -1w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (x << 2 + 1w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (x << 2 + 0x7FFFFFFFw) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (x << 2 + 0x80000001w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (~(x << 2) + 0x80000000w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (~(x << 2)) <> 2w:word2)`,
  SRW_TAC [fcpLib.FCP_ss,wordsLib.SIZES_ss]
         [word_extract_def, w2w, word_bits_def]
    \\ Q.EXISTS_TAC `0`
    \\ SRW_TAC [fcpLib.FCP_ss,ARITH_ss] []
    \\ SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [Once WORD_ADD_BIT0]);

val lem3 = Q.prove(
  `(!x:word32. (1 >< 0) (~(x << 2) + 1w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (~(x << 2) + 0x80000001w) <> 2w:word2) /\
   (!x:word32. (1 >< 0) (x << 2 + 0x80000000w) <> 2w:word2)`,
  SRW_TAC [fcpLib.FCP_ss,wordsLib.SIZES_ss]
         [word_extract_def, w2w, word_bits_def, word_1comp_def]
    \\ Q.EXISTS_TAC `1`
    \\ SRW_TAC [fcpLib.FCP_ss,wordsLib.WORD_EXTRACT_ss,ARITH_ss]
         [Once WORD_ADD_BIT, extract_bit0_plus1]
    \\ FULL_SIMP_TAC (std_ss++wordsLib.WORD_BIT_EQ_ss) []);

val aligned_bx_add_sub_shift_pc = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32 pc.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (f (if aligned_bx (FST (f (a,x)) + -(align (pc,4) + 8w))
                 then a else 0w,x)) + -(align (pc,4) + 8w))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 pc.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (add_with_carry (~(align (pc,4) + 8w),
           FST (f
             (if aligned_bx (FST (add_with_carry
                   (~(align (pc, 4) + 8w), FST (f (a,x)), c)))
              then
                a
              else
                0w,x)),c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 pc.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (add_with_carry (align (pc,4) + 8w,
           ~FST (f
             (if aligned_bx (FST (add_with_carry
                   (align (pc, 4) + 8w, ~FST (f (a,x)), c)))
              then
                a
              else
                0w,x)),c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 pc.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned_bx
        (FST (add_with_carry (align (pc,4) + 8w,
           FST (f
             (if aligned_bx (FST (add_with_carry
                   (align (pc, 4) + 8w, FST (f (a,x)), c)))
              then
                a
              else
                0w,x)),c))))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `z = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [boolSimps.LET_ss] [aligned_bx_def, add_with_carry_def,
         GSYM word_add_def, word_add_plus1]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_EXTRACT_ss)
         [lem, lem2, lem3, GSYM word_add_def, word_add_plus1]);

val aligned_bx_add_sub_rrx_pc = Q.store_thm("aligned_bx_add_sub_rrx_pc",
  `(!x a:word32 pc.
      aligned_bx
        (SND (word_rrx
           (x,if aligned_bx (SND (word_rrx (x,a)) + -(align (pc,4) + 8w))
              then a else 0w)) + -(align (pc,4) + 8w))) /\
   (!x a:word32 pc.
      aligned_bx
        (FST (add_with_carry (~(align (pc,4) + 8w),
           SND (word_rrx
             (x,if aligned_bx (FST (add_with_carry
                     (~(align (pc, 4) + 8w), SND (word_rrx (x,a)), c)))
                then a else 0w)),c)))) /\
   (!x a:word32 pc.
      aligned_bx
        (FST (add_with_carry (align (pc,4) + 8w,
           ~SND (word_rrx
             (x,if aligned_bx (FST (add_with_carry
                     (align (pc, 4) + 8w, ~SND (word_rrx (x,a)), c)))
                then a else 0w)),c)))) /\
   (!x a:word32 pc.
      aligned_bx
        (FST (add_with_carry (align (pc,4) + 8w,
           SND (word_rrx
             (x,if aligned_bx (FST (add_with_carry
                     (align (pc, 4) + 8w, SND (word_rrx (x,a)), c)))
                then a else 0w)),c))))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [word_plus8] \\ Cases_on `x`
    \\ Q.ABBREV_TAC `z = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [boolSimps.LET_ss] [aligned_bx_def, add_with_carry_def,
         GSYM word_add_def, word_add_plus1, word_rrx_0]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_EXTRACT_ss)
         [lem, lem2, lem3, GSYM word_add_def, word_add_plus1]);

val aligned_bx_pair_shift_thms = save_thm("aligned_bx_pair_shift_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
    (Drule.CONJUNCTS aligned_bx_shift_pair @
     Drule.CONJUNCTS aligned_bx_add_sub_shift_pc @
     Drule.CONJUNCTS aligned_bx_add_with_carry_shift_pair))));

val aligned_bx_add_with_carry_literal_pc =
  Q.store_thm("aligned_bx_add_with_carry_literal_pc",
  `(!pc:word32 n c.
     aligned_bx
       (FST (add_with_carry (align (pc,4) + 8w, n2w n, c))) =
     if c then aligned_bx (n2w n + 9w:word32)
          else aligned_bx (n2w n + 8w:word32)) /\
   (!pc:word32 n c.
     aligned_bx
       (FST (add_with_carry (~(align (pc,4) + 8w), n2w n, c))) =
     if c then (1 >< 0) (n2w n + 1w:word32) <> 3w:word2
          else (1 >< 0) (n2w n : word32) <> 3w:word2)`,
  REPEAT STRIP_TAC \\ Cases_on `c`
    \\ SRW_TAC [] [FST_ADD_WITH_CARRY]
    \\ Q.ABBREV_TAC `x:word32 = n2w n`
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, aligned_bx_add_sub_pc,
         ONCE_REWRITE_RULE [WORD_ADD_COMM] aligned_bx_add_sub_pc,
         ``x + -1w * (a + 0x8w) = ~(a + 8w) + (x + 0x1w)``
            |> wordsLib.WORD_ARITH_CONV |> EQT_ELIM]
    \\ SRW_TAC [] [WORD_NOT, WORD_LEFT_ADD_DISTRIB]
    );

val aligned_bx_1comp_pc = Q.store_thm("aligned_bx_1comp_pc",
  `!a:word32. aligned_bx (~(align (a,4) + 8w))`,
  STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (a,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] [aligned_bx_def]);

val aligned_bx_add_with_carry_pc = Q.store_thm("aligned_bx_add_with_carry_pc",
  `(!pc a:word32.
     aligned_bx
       (FST (add_with_carry
          (align (pc,4) + 8w,
           if aligned_bx (FST (add_with_carry (align (pc,4) + 8w,a,c)))
           then a else 0w,c)))) /\
   (!pc a:word32.
     aligned_bx
       (FST (add_with_carry
          (~(align (pc,4) + 8w),
           if aligned_bx (FST (add_with_carry (~(align (pc,4) + 8w),a,c)))
           then a else 0w,c)))) /\
   (!pc a:word32.
     aligned_bx
       (FST (add_with_carry
          (align (pc,4) + 8w,
           ~if aligned_bx (FST (add_with_carry (align (pc,4) + 8w,~a,c)))
            then a else 0w,c))))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [word_plus8]
    \\ Q.ABBREV_TAC `x = align (pc,4) >>> 2 + 2w : word32`
    \\ SRW_TAC [] [aligned_bx_def]
    \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss,boolSimps.LET_ss,ARITH_ss]
         [GSYM word_add_def, word_add_plus1, add_with_carry_def,
          lem, lem2, lem3]
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []);

val aligned_bx_add_with_carry_pair_pc = Q.store_thm(
  "aligned_bx_add_with_carry_pair_pc",
  `(!a:word32 c.
     aligned_bx
       (FST (add_with_carry (align (a,4) + 8w, align (a,4) + 8w, c)))) /\
   (!a:word32 c.
     aligned_bx
       (FST (add_with_carry (~(align (a,4) + 8w), align (a,4) + 8w, c)))) /\
   (!a:word32 c.
     aligned_bx
       (FST (add_with_carry (align (a,4) + 8w, ~(align (a,4) + 8w), c))))`,
  SRW_TAC [boolSimps.LET_ss]
         [WORD_NOT, WORD_LEFT_ADD_DISTRIB, GSYM word_add_def, word_add_plus1,
          add_with_carry_def]
    \\ SIMP_TAC std_ss [aligned_bx_add_sub_pc, GSYM WORD_ADD_ASSOC,
         wordsLib.WORD_DECIDE ``2w * a = a + a:word32``]
    \\ EVAL_TAC);

val aligned_and_aligned_bx = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w ?? FST (f (a + 8w,x)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (~(a + 8w), FST (f (a + 8w,x)), c)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (a + 8w, FST (f (a + 8w,x)), c)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (a + 8w, ~FST (f (a + 8w,x)), c)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (FST (f (a + 8w,x)) + -(a + 8w))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w + FST (f (a + 8w,x)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w + -FST (f (a + 8w,x)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (FST (f (a + 8w,x)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (~FST (f (a + 8w,x)))
        then a else -8w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w || FST (f (a + 8w,x)))
        then a else -8w,4))`,
  SRW_TAC [] [] \\ EVAL_TAC);

val minus8 = EVAL ``-8w:word32``;

val aligned_and_aligned_bx_thms = save_thm("aligned_and_aligned_bx_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm => map (fn t => thm |> Q.SPEC t |> REWRITE_RULE [minus8])
                     [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
    (Drule.CONJUNCTS aligned_and_aligned_bx))));

val aligned_and_aligned_bx_rrx = Q.prove(
  `(!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w ?? SND (word_rrx (x,a + 8w)))
        then a else -8w,4)) /\
   (!a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (~(a + 8w), SND (word_rrx (x,a + 8w)), c)))
        then a else -8w,4)) /\
   (!a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (a + 8w, SND (word_rrx (x,a + 8w)), c)))
        then a else -8w,4)) /\
   (!a:word32 x c.
     aligned
       (if aligned (a,4) /\
           aligned_bx (FST (add_with_carry
             (a + 8w, ~SND (word_rrx (x,a + 8w)), c)))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (SND (word_rrx (x,a + 8w)) + -(a + 8w))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w + SND (word_rrx (x,a + 8w)))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w + -SND (word_rrx (x,a + 8w)))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (SND (word_rrx (x,a + 8w)))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (~SND (word_rrx (x,a + 8w)))
        then a else -8w,4)) /\
   (!a:word32 x.
     aligned
       (if aligned (a,4) /\ aligned_bx (a + 8w || SND (word_rrx (x,a + 8w)))
        then a else -8w,4))`,
  SRW_TAC [] [] \\ EVAL_TAC);

val aligned_and_aligned_bx_rrx = save_thm("aligned_and_aligned_bx_rrx",
  REWRITE_RULE [minus8] aligned_and_aligned_bx_rrx);

val lem = Q.prove(
  `(!a:word32. FST (add_with_carry (a,0w,c)) = if c then a + 1w else a) /\
   (!a:word32. FST (add_with_carry (0w,a,c)) = if c then a + 1w else a)`,
  SRW_TAC [boolSimps.LET_ss] [add_with_carry_def, word_add_def]);

val aligned_bx_and_aligned_add_with_carry = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32 c.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          ((if aligned (a,4) /\
               aligned_bx (FST (add_with_carry
                 (a + 8w, FST (f (a + 8w,x)),c)))
            then a else -8w) + 8w,
        FST (f ((if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (a + 8w, FST (f (a + 8w,x)),c)))
                 then a else -8w) + 8w,x)),c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 c.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          (~((if aligned (a,4) /\
                 aligned_bx (FST (add_with_carry
                   (~(a + 8w), FST (f (a + 8w,x)),c)))
              then a else -8w) + 8w),
        FST (f ((if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (~(a + 8w), FST (f (a + 8w,x)),c)))
                 then a else -8w) + 8w,x)),c)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 c.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (add_with_carry
          ((if aligned (a,4) /\
               aligned_bx (FST (add_with_carry
                 (a + 8w, ~FST (f (a + 8w,x)),c)))
            then a else -8w) + 8w,
        ~FST (f ((if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (a + 8w, ~FST (f (a + 8w,x)),c)))
                 then a else -8w) + 8w,x)),c))))`,
  SRW_TAC [] [aligned_bx_0w, lem]
    \\ SRW_TAC [] [aligned_bx_0w, aligned_bx_1w, aligned_bx_m1w]);

val aligned_bx_and_aligned_add_with_carry_rrx = Q.prove(
  `(!x a:word32 c.
     aligned_bx
       (FST (add_with_carry
          ((if aligned (a,4) /\
               aligned_bx (FST (add_with_carry
                 (a + 8w, SND (word_rrx (x,a + 8w)),c)))
            then a else -8w) + 8w,
        SND (word_rrx (x,(if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (a + 8w, SND (word_rrx (x,a + 8w)),c)))
                 then a else -8w) + 8w)),c)))) /\
   (!x a:word32 c.
     aligned_bx
       (FST (add_with_carry
          (~((if aligned (a,4) /\
                 aligned_bx (FST (add_with_carry
                   (~(a + 8w), SND (word_rrx (x,a + 8w)),c)))
              then a else -8w) + 8w),
        SND (word_rrx (x,(if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (~(a + 8w), SND (word_rrx (x,a + 8w)),c)))
                 then a else -8w) + 8w)),c)))) /\
   (!x a:word32 c.
     aligned_bx
       (FST (add_with_carry
          ((if aligned (a,4) /\
               aligned_bx (FST (add_with_carry
                 (a + 8w, ~SND (word_rrx (x,a + 8w)),c)))
            then a else -8w) + 8w,
        ~SND (word_rrx (x,(if aligned (a,4) /\
                    aligned_bx (FST (add_with_carry
                      (a + 8w, ~SND (word_rrx (x,a + 8w)),c)))
                 then a else -8w) + 8w)),c))))`,
  SRW_TAC [] [aligned_bx_0w, lem] \\ Cases_on `x`
    \\ SRW_TAC [] [word_rrx_0, lem, aligned_bx_0w, aligned_bx_1w,
         aligned_bx_m1w,
         EVAL ``aligned_bx (0x80000000w:word32)``,
         EVAL ``aligned_bx (0x80000001w:word32)``,
         EVAL ``aligned_bx (0x7FFFFFFFw:word32)``]
    \\ Cases_on `c`
    \\ SRW_TAC [boolSimps.LET_ss] [add_with_carry_def]
    \\ EVAL_TAC);

val aligned_bx_and_aligned_add_with_carry_rrx = save_thm(
  "aligned_bx_and_aligned_add_with_carry_rrx",
  REWRITE_RULE [minus8] aligned_bx_and_aligned_add_with_carry_rrx);

val aligned_bx_and_aligned = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w ?? FST (f (a + 8w,x)))
         then a else -8w) + 8w ??
        FST (f ((if aligned (a,4) /\ aligned_bx (a + 8w ?? FST (f (a + 8w,x)))
                 then a else -8w) + 8w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (f ((if aligned (a,4) /\ aligned_bx (FST (f (a + 8w,x)) + -(a + 8w))
                 then a else -8w) + 8w,x)) +
       -((if aligned (a,4) /\ aligned_bx (FST (f (a + 8w,x)) + -(a + 8w))
          then a else -8w) + 8w))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w + FST (f (a + 8w,x)))
         then a else -8w) + 8w +
        FST (f ((if aligned (a,4) /\ aligned_bx (a + 8w + FST (f (a + 8w,x)))
                 then a else -8w) + 8w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w + -FST (f (a + 8w,x)))
         then a else -8w) + 8w +
        -FST (f ((if aligned (a,4) /\ aligned_bx (a + 8w + -FST (f (a + 8w,x)))
                  then a else -8w) + 8w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (FST (f ((if aligned (a,4) /\ aligned_bx (FST (f (a + 8w,x)))
                 then a else -8w) + 8w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       (~FST (f ((if aligned (a,4) /\ aligned_bx (~FST (f (a + 8w,x)))
                  then a else -8w) + 8w,x)))) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
     x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w || FST (f (a + 8w,x)))
         then a else -8w) + 8w ||
        FST (f ((if aligned (a,4) /\ aligned_bx (a + 8w || FST (f (a + 8w,x)))
                 then a else -8w) + 8w,x))))`,
  SRW_TAC [] [aligned_bx_0w] \\ EVAL_TAC);

val aligned_bx_and_aligned_thms = save_thm("aligned_bx_and_aligned_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
             |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C,minus8])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
    (Drule.CONJUNCTS aligned_bx_and_aligned_add_with_carry @
     Drule.CONJUNCTS aligned_bx_and_aligned))));

val aligned_bx_and_aligned_rrx = Q.prove(
  `(!x a:word32.
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w ?? SND (word_rrx (x,a + 8w)))
         then a else -8w) + 8w ??
        SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (a + 8w ?? SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w)))) /\
   (!x a:word32.
     aligned_bx
       (SND (word_rrx (x,
         (if aligned (a,4) /\ aligned_bx (SND (word_rrx (x,a + 8w)) + -(a + 8w))
          then a else -8w) + 8w)) +
       -((if aligned (a,4) /\ aligned_bx (SND (word_rrx (x,a + 8w)) + -(a + 8w))
          then a else -8w) + 8w))) /\
   (!x a:word32.
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w + SND (word_rrx (x,a + 8w)))
         then a else -8w) + 8w +
        SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (a + 8w + SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w)))) /\
   (!x a:word32.
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w + -SND (word_rrx (x,a + 8w)))
         then a else -8w) + 8w +
        -SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (a + 8w + -SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w)))) /\
   (!x a:word32.
     aligned_bx
       (SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w)))) /\
   (!x a:word32.
     aligned_bx
       (~SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (~SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w)))) /\
   (!x a:word32.
     aligned_bx
       ((if aligned (a,4) /\ aligned_bx (a + 8w || SND (word_rrx (x,a + 8w)))
         then a else -8w) + 8w ||
        SND (word_rrx (x,
          (if aligned (a,4) /\ aligned_bx (a + 8w || SND (word_rrx (x,a + 8w)))
           then a else -8w) + 8w))))`,
  SRW_TAC [] [aligned_bx_0w] \\ Cases_on `x` \\ EVAL_TAC);

val aligned_bx_and_aligned_rrx = save_thm("aligned_bx_and_aligned_rrx",
  REWRITE_RULE [minus8] aligned_bx_and_aligned_rrx);

val align_ldr_lsl = Q.store_thm("align_ldr_lsl",
  `!pc rm: word32.
     align (pc,4) <>
     align (pc,4) + 8w +
     FST
       (LSL_C
          (if
             aligned (align (pc,4) + 8w +
             FST (LSL_C (if rm << 2 <> 0xFFFFFFF8w then rm else 0w,2)), 4)
           then
             (if rm << 2 <> 0xFFFFFFF8w then rm else 0w)
           else
             0w,2))`,
  SRW_TAC [boolSimps.LET_ss, wordsLib.WORD_CANCEL_ss] [LSL_C_def]);

(* ------------------------------------------------------------------------- *)

val aligned_aligned = Q.store_thm("aligned_aligned",
  `(!a:word32 b. aligned(if b then align(a,4) else 0xFFFFFFF8w,4)) /\
   (!a:word32 b. aligned (if aligned (a,4) /\ b then a else 0xFFFFFFF8w, 4)) /\
   (!a:word8. aligned (if aligned (a,4) then a else 0w, 4)) /\
   (!a:word32 b c.
      aligned
        ((if b /\ aligned (a + 8w,4) /\ c then a else 0xFFFFFFF8w) + 8w, 4)) /\
   (!a:word32. aligned(if aligned(a,4) then a else 0w,4)) /\
   (!a:word32. aligned(~(if aligned(~a,4) then a else 0xFFFFFFFFw),4)) /\
   (!a:word32 b. aligned((if aligned(a && b,4) then a else 0w) && b,4)) /\
   (!a:word32 b. aligned((if aligned(a ?? b,4) then a else b) ?? b,4)) /\
   (!a:word32 b:word32.
      aligned((if aligned(a,4) /\ aligned(b,4) then a else 0w),4) /\
      aligned((if aligned(a,4) /\ aligned(b,4) then b else 0w),4)) /\
   (!a:word32 b.
      aligned(align(a,4) + 8w +
        (if aligned(align(a,4) + 8w + b,4) then b else 0w),4)) /\
   (!a:word32 b.
      aligned(align(a,4) + 8w +
        -(if aligned(align(a,4) + 8w + -b,4) then b else 0w),4))`,
  SRW_TAC [] [aligned_align, aligned_sum] \\ EVAL_TAC);

val aligned_over_bitwise = Q.store_thm("aligned_over_bitwise",
  `(!a b:word32. aligned(align(a,4) + 8w && b, 4)) /\
   (!a:word32. ~aligned(~(align(a,4) + 8w), 4)) /\
   (!a b:word32. aligned(align(a,4) + 8w ?? b, 4) = aligned(b,4)) /\
   (!a b:word32. aligned(a || b, 4) = aligned(a,4) /\ aligned(b,4))`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_bits_sum, aligned_248, align_248,
         wordsLib.WORD_DECIDE ``((1 >< 0) (~a) = 0w:word2) =
                                ((1 >< 0) (a:word32) = 3w:word2)``]
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []
    \\ METIS_TAC []);

val word2_cases = wordsLib.WORD_DECIDE
  ``!a:word2. (a = 0w) \/ (a = 1w) \/ (a = 2w) \/ (a = 3w)``;

val align_over_and =
  wordsTheory.WORD_w2w_OVER_ADD
       |> INST_TYPE [alpha |-> ``:32``, beta |-> ``:2``]
       |> SIMP_RULE (srw_ss())
            [wordsLib.WORD_DECIDE ``w2w (w:word32) = ((1 >< 0) w):word2``]
       |> Once;

val aligned_neg = Q.store_thm("aligned_neg",
  `!a:word32. aligned(-a,4) = aligned(a,4)`,
  SRW_TAC [] [WORD_NEG, aligned_248, align_over_and,
    wordsLib.WORD_DECIDE ``(1 >< 0) (~(a:word32)) = ~((1 >< 0) a) : word2``]
    \\ Q.SPEC_THEN `(1 >< 0) a` STRIP_ASSUME_TAC word2_cases
    \\ ASM_SIMP_TAC (srw_ss()) []);

val aligned_neg_pc = Q.store_thm("aligned_neg_pc",
  `!a:word32. aligned(-(align(a,4) + 8w),4)`,
  SRW_TAC [] [aligned_sum, aligned_neg] \\ EVAL_TAC);

val aligned_neg_pc =
  CONJ (SIMP_RULE (srw_ss()) [] aligned_neg_pc)
       (SIMP_RULE (srw_ss()) [WORD_LEFT_ADD_DISTRIB] aligned_neg_pc);

val lem = Q.prove(
  `(!x:word32. n2w (w2n x + 1) = x + 1w)`, SRW_TAC [] [word_add_def]);

val aligned_aligned_add_with_carry = Q.store_thm(
  "aligned_aligned_add_with_carry",
  `(!a:word32 b c.
      aligned (FST (add_with_carry
         (align(a,4) + 8w,
          if aligned (FST (add_with_carry (align(a,4) + 8w,b,c)),4) then b else
            if c then 0xFFFFFFFFw else 0w,c)),4)) /\
   (!a:word32 b c.
      aligned (FST (add_with_carry
         (align(a,4) + 8w,
          ~(if aligned (FST (add_with_carry (align(a,4) + 8w,~b,c)),4) then b
            else if c then 0w else 0xFFFFFFFFw),c)),4)) /\
   (!a:word32 b c.
      aligned (FST (add_with_carry
         (~(align(a,4) + 8w),
          if aligned (FST (add_with_carry (~(align(a,4) + 8w),b,c)),4) then b
            else if c then 0w else 1w,c)),4))`,
  REPEAT STRIP_TAC \\ Cases_on `c`
    \\ SIMP_TAC (std_ss++boolSimps.LET_ss)
         [add_with_carry_def, GSYM word_add_def, word_add_plus1, lem]
    \\ SRW_TAC [] [aligned_sum]
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_NOT, aligned_neg_pc]
    \\ EVAL_TAC);

val aligned_aligned_shift = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32 b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (FST (f (if aligned (a,4) /\ aligned (FST (f (b,x)), 4)
                       then b else 0w,x)),4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32 b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (FST (f ((if aligned (a,4) /\ aligned (FST (f (b + 8w,x)), 4)
                        then b else 0xFFFFFFF8w) + 8w,x)),4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a && FST (f (b,x)), 4) then a else 0w) &&
        FST (f (if aligned (a && FST (f (b,x)), 4) then b else 0w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a && ~FST (f (b,x)), 4) then a else 0w) &&
       ~FST (f (if aligned (a && ~FST (f (b,x)), 4) then b else 0w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a ?? FST (f (b,x)), 4) then a else 0w) ??
        FST (f (if aligned (a ?? FST (f (b,x)), 4) then b else 0w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a || FST (f (b,x)), 4) then a else 0w) ||
        FST (f (if aligned (a || FST (f (b,x)), 4) then b else 0w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (FST (f (if aligned (FST (f (a,x)) + -a,4) then a else 0w, x)) +
                      -if aligned (FST (f (a,x)) + -a,4) then a else 0w,4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (align(a,4) + 8w +
          FST (f (if aligned (align(a,4) + 8w + FST (f (b,x)),4)
                  then b else 0w, x)),4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (FST (f (if aligned (FST (f (b,x)) + -(align(a,4) + 8w),4)
                       then b else 0w, x)) + -(align(a,4) + 8w),4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned (align(a,4) + 8w +
          -FST (f (if aligned (align(a,4) + 8w + -FST (f (b,x)),4)
                   then b else 0w, x)),4))`,
  SRW_TAC [] [aligned_sum, aligned_neg_pc] \\ EVAL_TAC);

val aligned_aligned_shift =
  CONJ
    (aligned_aligned_shift
       |> Thm.CONJUNCT1
       |> Drule.SPEC_ALL
       |> Q.INST [`a` |-> `0w`]
       |> REWRITE_RULE [EVAL ``aligned (0w:word32,4)``]
       |> Q.GEN `b` |> Q.GEN `x` |> Q.GEN `f`)
    aligned_aligned_shift;

val aligned_aligned_shift_thms = save_thm("aligned_aligned_shift_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
     (Drule.CONJUNCTS aligned_aligned_shift))));

val aligned_aligned_shift_pc = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32 b c.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned
        (FST (f ((if b /\ c /\ aligned (FST (f (a + 8w,x)),4)
                  then a else 0xFFFFFFF8w) + 8w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned
        ((if b /\ aligned (a + 8w ?? FST (f (a + 8w,x)), 4)
          then a else 0xFFFFFFF8w) + 8w ??
           FST (f ((if b /\ aligned (a + 8w ?? FST (f (a + 8w,x)), 4)
                    then a else 0xFFFFFFF8w) + 8w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned
        ((if b /\ aligned (a + 8w + FST (f (a + 8w,x)), 4)
          then a else 0xFFFFFFF8w) + 8w +
           FST (f ((if b /\ aligned (a + 8w + FST (f (a + 8w,x)), 4)
                    then a else 0xFFFFFFF8w) + 8w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned
        ((if b /\ aligned (a + 8w + -FST (f (a + 8w,x)), 4)
          then a else 0xFFFFFFF8w) + 8w +
           -FST (f ((if b /\ aligned (a + 8w + -FST (f (a + 8w,x)), 4)
                     then a else 0xFFFFFFF8w) + 8w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a b.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned
        (FST (f ((if b /\ aligned (FST (f (a + 8w,x)) + -(a + 8w), 4)
                  then a else 0xFFFFFFF8w) + 8w,x)) +
         -((if b /\ aligned (FST (f (a + 8w,x)) + -(a + 8w), 4)
            then a else 0xFFFFFFF8w) + 8w), 4))`,
  SRW_TAC [] [aligned_sum, aligned_neg_pc] \\ EVAL_TAC);

val aligned_aligned_shift_pc_thms = save_thm("aligned_aligned_shift_pc_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
     (Drule.CONJUNCTS aligned_aligned_shift_pc))));

val aligned_neg_pc2 = Q.prove(
  `!a:word32. aligned(-(align(a,4) + 0x80000008w),4)`,
  SRW_TAC [] [aligned_sum, aligned_neg] \\ EVAL_TAC);

val aligned_neg_pc2 =
  SIMP_RULE (srw_ss()) [EVAL ``-1w:word32``, WORD_LEFT_ADD_DISTRIB]
    aligned_neg_pc2;

val aligned_aligned_rrx = Q.prove(
  `(!x a:word32 b.
      aligned (SND (word_rrx (x,
        if b /\ aligned (SND (word_rrx (x,a)), 4) then a else 0w)),4)) /\
   (!x a:word32 b.
      aligned (SND (word_rrx (x,
        (if b /\ aligned (SND (word_rrx (x,a + 8w)), 4)
         then a else 0xFFFFFFF8w) + 8w)),4)) /\
   (!x a:word32 b.
      aligned ((if aligned (a && SND (word_rrx (x,b)), 4) then a else 0w) &&
        SND (word_rrx (x,
          if aligned (a && SND (word_rrx (x,b)), 4) then b else 0w)), 4)) /\
   (!x a:word32 b.
      aligned ((if aligned (a && ~SND (word_rrx (x,b)), 4) then a else 0w) &&
       ~SND (word_rrx (x,
          if aligned (a && ~SND (word_rrx (x,b)), 4) then b else 0w)), 4)) /\
   (!x a:word32 b.
      aligned ((if aligned (a ?? SND (word_rrx (x,b)), 4) then a else 0w) ??
        SND (word_rrx (x,
          if aligned (a ?? SND (word_rrx (x,b)), 4) then b else 0w)), 4)) /\
   (!x a:word32 b.
      aligned ((if aligned (a || SND (word_rrx (x,b)), 4) then a else 0w) ||
        SND (word_rrx (x,
          if aligned (a || SND (word_rrx (x,b)), 4) then b else 0w)), 4)) /\
   (!x a:word32.
      aligned (SND (word_rrx (x,
          if aligned (SND (word_rrx (x,a)) + -a,4) then a else 0w)) +
         -if aligned (SND (word_rrx (x,a)) + -a,4) then a else 0w,4)) /\
   (!x a:word32 b.
      aligned (align(a,4) + 8w +
        SND (word_rrx (x,
          if aligned (align(a,4) + 8w + SND (word_rrx (x,b)),4)
          then b else 0w)),4)) /\
   (!x a:word32 b.
      aligned (SND (word_rrx (x,
          if aligned (SND (word_rrx (x,b)) + -(align(a,4) + 8w),4)
          then b else 0w)) + -(align(a,4) + 8w),4)) /\
   (!x a:word32 b.
      aligned (align(a,4) + 8w +
       -SND (word_rrx (x,
          if aligned (align(a,4) + 8w + -SND (word_rrx (x,b)),4)
          then b else 0w)),4))`,
  REPEAT STRIP_TAC \\ Cases_on `x`
    \\ SRW_TAC []
         [WORD_LEFT_ADD_DISTRIB, aligned_sum, aligned_neg_pc, word_rrx_0]
    \\ EVAL_TAC \\ REWRITE_TAC [aligned_neg_pc2]);

val aligned_aligned_rrx = save_thm("aligned_aligned_rrx",
  CONJ
    (aligned_aligned_rrx
       |> Thm.CONJUNCT1
       |> Drule.SPEC_ALL
       |> Q.INST [`b` |-> `T`]
       |> REWRITE_RULE []
       |> GEN_ALL)
    aligned_aligned_rrx);

val aligned_aligned_rrx_pc = Q.store_thm("aligned_aligned_rrx_pc",
  `(!x a:word32 b c.
      aligned
        (SND (word_rrx (x,(if b /\ c /\ aligned (SND (word_rrx (x,a + 8w)),4)
                           then a else 0xFFFFFFF8w) + 8w)), 4)) /\
   (!x a:word32 b.
      aligned
        ((if b /\ aligned (a + 8w ?? SND (word_rrx (x,a + 8w)), 4)
          then a else 0xFFFFFFF8w) + 8w ??
           SND (word_rrx (x,
             (if b /\ aligned (a + 8w ?? SND (word_rrx (x,a + 8w)), 4)
              then a else 0xFFFFFFF8w) + 8w)), 4)) /\
   (!x a:word32 b.
      aligned
        ((if b /\ aligned (a + 8w + SND (word_rrx (x,a + 8w)), 4)
          then a else 0xFFFFFFF8w) + 8w +
           SND (word_rrx (x,
             (if b /\ aligned (a + 8w + SND (word_rrx (x,a + 8w)), 4)
              then a else 0xFFFFFFF8w) + 8w)), 4)) /\
   (!x a:word32 b.
      aligned
        ((if b /\ aligned (a + 8w + -SND (word_rrx (x,a + 8w)), 4)
          then a else 0xFFFFFFF8w) + 8w +
           -SND (word_rrx (x,
              (if b /\ aligned (a + 8w + -SND (word_rrx (x,a + 8w)), 4)
               then a else 0xFFFFFFF8w) + 8w)), 4)) /\
   (!x a:word32 b.
      aligned
        (SND (word_rrx (x,
          (if b /\ aligned (SND (word_rrx (x,a + 8w)) + -(a + 8w), 4)
           then a else 0xFFFFFFF8w) + 8w)) +
         -((if b /\ aligned (SND (word_rrx (x,a + 8w)) + -(a + 8w), 4)
            then a else 0xFFFFFFF8w) + 8w), 4))`,
  REPEAT STRIP_TAC \\ Cases_on `x`
    \\ SRW_TAC [] [aligned_sum, aligned_neg_pc, word_rrx_0]
    \\ EVAL_TAC);

val aligned_pc_pc = Q.store_thm("aligned_pc_pc",
  `!a:word32. aligned(align(a,4) + 8w + (align(a,4) + 8w),4)`,
  SIMP_TAC std_ss [aligned_sum,
         wordsLib.WORD_DECIDE ``a + b + (a + b) = a + (a + (b + b)) : 'a word``]
    \\ EVAL_TAC);

val aligned_aligned_rsb = Q.store_thm("aligned_aligned_rsb",
  `(!a:word32 b.
      aligned((if aligned(b + -(align(a,4) + 8w),4) then b else 0w) +
              -(align(a,4) + 8w),4))`,
  SRW_TAC [] [aligned_neg_pc]);

val add_with_carry = Q.store_thm("add_with_carry",
  `(!a:word32 b c d.
     FST (add_with_carry (a + d + -(if c then 1w else 0w),b,c)) =
     a + (d + b)) /\
   (!a:word32 b c d.
     FST (add_with_carry (a + d + (if c then 0w else 1w),b,c)) =
     a + (d + b + 1w)) /\
   (!a:word32 b c d.
     FST (add_with_carry (~(d + (if c then 0w else 0xFFFFFFFFw) + a),b,c)) =
     -a + (b - d))`,
  SRW_TAC [boolSimps.LET_ss]
          [WORD_NOT, WORD_LEFT_ADD_DISTRIB, GSYM word_add_def,
           add_with_carry_def, word_add_plus1]);

val add_with_carry0 = save_thm("add_with_carry0",
  Drule.LIST_CONJ
    [add_with_carry
      |> Thm.CONJUNCT1
      |> Q.SPECL [`a`,`0w`,`c`,`0w`]
      |> REWRITE_RULE [WORD_ADD_0]
      |> GEN_ALL,
     add_with_carry
      |> Thm.CONJUNCT2 |> Thm.CONJUNCT1
      |> Q.SPECL [`a`,`0xFFFFFFFFw`,`c`,`0x0w`]
      |> REWRITE_RULE [WORD_ADD_0, EVAL ``0xFFFFFFFFw + 1w : word32``]
      |> GEN_ALL,
     add_with_carry
      |> Thm.CONJUNCT2 |> Thm.CONJUNCT2
      |> Q.SPECL [`a`,`0w`,`c`,`0x0w`]
      |> REWRITE_RULE [WORD_ADD_0, WORD_SUB_RZERO]
      |> GEN_ALL]);

val aligned_pc_thm = Q.store_thm("aligned_pc_thm",
  `!a:word32. aligned (a,4) ==> aligned (a + 8w, 4)`,
  METIS_TAC [aligned_thm, aligned_def, EVAL ``aligned (8w:word32,4)``]);

val aligned_bitwise_thm = Q.store_thm("aligned_bitwise_thm",
  `(!a:word32 b.
      aligned (a,4) /\ aligned (b,4) ==> (align (a || b, 4) = a || b)) /\
   (!a:word32 b.
      aligned (a,4) /\ aligned (b,4) ==> (align (a ?? b, 4) = a ?? b)) /\
   (!a:word32 b. aligned (a,4) ==> (align (a && b,4) = a && b))`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_248, align_248]);

(* ------------------------------------------------------------------------- *)

val align4  = EVAL ``align (4w:word32,4)``;
val align8  = EVAL ``align (8w:word32,4)``;
val align4m = EVAL ``align (0xFFFFFFFCw:word32,4)``;

val align_plus4 = Q.prove(
  `!a:word32. align (a + 4w, 4) = align (a,4) + 4w`,
  SUBST1_TAC (SYM align4)
    \\ SRW_TAC [] [ONCE_REWRITE_RULE [WORD_ADD_COMM] align_aligned, align4]);

val align_plus_extra = Q.prove(
  `(!a:word32. align (a + 8w, 4) = align (a,4) + 8w) /\
   (!a:word32. align (a + 0xFFFFFFFCw, 4) = align (a,4) + 0xFFFFFFFCw)`,
  SUBST1_TAC (SYM align8)
    \\ SUBST1_TAC (SYM align4m)
    \\ SRW_TAC [] [ONCE_REWRITE_RULE [WORD_ADD_COMM] align_aligned,
         align8,align4m]);

val aligned_mul4 = Q.prove(
  `!a:word32. aligned (4w * a, 4)`,
  SRW_TAC [wordsLib.WORD_MUL_LSL_ss,wordsLib.WORD_EXTRACT_ss] [aligned_248]);

val align_mul4 = aligned_mul4 |> REWRITE_RULE [aligned_def] |> GSYM;

val neq_align_plus4 = Q.prove(
  `!a:word32. align (a + 4w, 4) <> align (a, 4)`,
  SRW_TAC [wordsLib.WORD_ARITH_EQ_ss] [align_plus4]);

val BIT_ALIGN4 = Q.prove(
  `(!n. NUMERAL (BIT2 (BIT1 n)) = 4 * (n + 1)) /\
   (!n. NUMERAL (BIT1 (BIT2 n)) = 4 * (n + 1) + 1) /\
   (!n. NUMERAL (BIT2 (BIT2 n)) = 4 * (n + 1) + 2) /\
   (!n. NUMERAL (BIT1 (BIT1 (BIT1 n))) = 4 * (2 * n + 1) + 3) /\
   (!n. NUMERAL (BIT1 (BIT1 (BIT2 n))) = 4 * (2 * n + 2) + 3)`,
  REPEAT STRIP_TAC
     \\ CONV_TAC (LHS_CONV (REWRITE_CONV [NUMERAL_DEF, BIT2, BIT1]))
     \\ DECIDE_TAC);

val aligned_numeric = Q.prove(
  `aligned (0w:word32,4) /\
   !n. aligned (n2w (NUMERAL (BIT2 (BIT1 n))) : word32, 4)`,
  REPEAT STRIP_TAC >> EVAL_TAC
    \\ Q.SPEC_THEN `n` SUBST1_TAC (Thm.CONJUNCT1 BIT_ALIGN4)
    \\ REWRITE_TAC [GSYM word_mul_n2w, aligned_mul4]);

val align_sum_numeric = Q.prove(
  `(!n. n2w (NUMERAL (BIT2 (BIT1 n))) =
        align (n2w (NUMERAL (BIT2 (BIT1 n))),4) :word32) /\
   (!n. n2w (NUMERAL (BIT1 (BIT2 n))) =
        align (n2w (NUMERAL (BIT2 (BIT1 n))),4) + 1w :word32) /\
   (!n. n2w (NUMERAL (BIT2 (BIT2 n))) =
        align (n2w (NUMERAL (BIT2 (BIT1 n))),4) + 2w :word32) /\
   (!n. n2w (NUMERAL (BIT1 (BIT1 (BIT1 n)))) =
       align (4w * (2w * n2w n + 1w),4) + 3w :word32) /\
   (!n. n2w (NUMERAL (BIT1 (BIT1 (BIT2 n)))) =
       align (4w * (2w * n2w n + 2w),4) + 3w :word32)`,
  REWRITE_TAC [align_mul4]
    \\ ONCE_REWRITE_TAC [BIT_ALIGN4]
    \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB, GSYM word_mul_n2w, GSYM word_add_n2w,
         align_plus4, align_mul4,
         METIS_PROVE [ALT_ZERO, ADD_CLAUSES]
           ``(ZERO + 1 = 1) /\ (n2w ZERO = 0w)``]);

val align_neq2 = Q.store_thm("align_neq2",
  `!a:word32 b n.
     aligned (a, 4) ==>
     align (b, 4) <> a + 1w /\
     align (b, 4) <> a + 2w /\
     align (b, 4) <> a + 3w /\
     align (b, 4) <> a + n2w (NUMERAL (BIT1 (BIT2 n))) /\ (* 1 *)
     align (b, 4) <> a + n2w (NUMERAL (BIT2 (BIT2 n))) /\ (* 2 *)
     align (b, 4) <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT1 n)))) /\ (* 3 *)
     align (b, 4) <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT2 n)))) /\ (* 3 *)
     align (b, 4) + 1w <> a /\
     align (b, 4) + 1w <> a + 2w /\
     align (b, 4) + 1w <> a + 3w /\
     align (b, 4) + 1w <> a + n2w (NUMERAL (BIT2 (BIT1 n))) /\ (* 0 *)
     align (b, 4) + 1w <> a + n2w (NUMERAL (BIT2 (BIT2 n))) /\ (* 2 *)
     align (b, 4) + 1w <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT1 n)))) /\ (* 3 *)
     align (b, 4) + 1w <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT2 n)))) /\ (* 3 *)
     align (b, 4) + 2w <> a /\
     align (b, 4) + 2w <> a + 1w /\
     align (b, 4) + 2w <> a + 3w /\
     align (b, 4) + 2w <> a + n2w (NUMERAL (BIT2 (BIT1 n))) /\ (* 0 *)
     align (b, 4) + 2w <> a + n2w (NUMERAL (BIT1 (BIT2 n))) /\ (* 1 *)
     align (b, 4) + 2w <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT1 n)))) /\ (* 3 *)
     align (b, 4) + 2w <> a + n2w (NUMERAL (BIT1 (BIT1 (BIT2 n)))) /\ (* 3 *)
     align (b, 4) + 3w <> a /\
     align (b, 4) + 3w <> a + 1w /\
     align (b, 4) + 3w <> a + 2w /\
     align (b, 4) + 3w <> a + n2w (NUMERAL (BIT2 (BIT1 n))) /\ (* 0 *)
     align (b, 4) + 3w <> a + n2w (NUMERAL (BIT1 (BIT2 n))) /\ (* 1 *)
     align (b, 4) + 3w <> a + n2w (NUMERAL (BIT2 (BIT2 n)))`, (* 2 *)
  NTAC 4 STRIP_TAC
    \\ POP_ASSUM (fn th =>
         REPEAT CONJ_TAC \\
         ONCE_REWRITE_TAC [th |> REWRITE_RULE [aligned_def]])
    \\ REWRITE_TAC [align_neq]
    \\ ONCE_REWRITE_TAC [align_sum_numeric]
    \\ REWRITE_TAC [align_neq, GSYM align_aligned, WORD_ADD_ASSOC]);

val align2 = EVAL ``align (2w:word32,2)``;

val align_plus2 = Q.prove(
  `!a:word32. align (a + 2w, 2) = align (a,2) + 2w`,
  SUBST1_TAC (SYM align2)
    \\ SRW_TAC [] [ONCE_REWRITE_RULE [WORD_ADD_COMM] align_aligned, align2]);

val aligned_mul2 = Q.prove(
  `!a:word32. aligned (2w * a, 2)`,
  SRW_TAC [wordsLib.WORD_MUL_LSL_ss,wordsLib.WORD_EXTRACT_ss] [aligned_248]);

val align_mul2 = aligned_mul2 |> REWRITE_RULE [aligned_def] |> GSYM;

val BIT_ALIGN2 = Q.prove(
  `(!n. NUMERAL (BIT1 n) = 2 * n + 1) /\
   (!n. NUMERAL (BIT2 n) = 2 * (n + 1))`,
  REPEAT STRIP_TAC
     \\ CONV_TAC (LHS_CONV (REWRITE_CONV [NUMERAL_DEF, BIT2, BIT1]))
     \\ DECIDE_TAC);

val align_sum_numeric2 = Q.prove(
  `(!n. n2w (NUMERAL (BIT2 n)) =
        align (n2w (NUMERAL (BIT2 n)),2) :word32) /\
   (!n. n2w (NUMERAL (BIT1 n)) =
        align (2w * n2w n,2) + 1w :word32)`,
  REWRITE_TAC [align_mul2]
    \\ ONCE_REWRITE_TAC [BIT_ALIGN2]
    \\ SRW_TAC [] [WORD_LEFT_ADD_DISTRIB, GSYM word_mul_n2w, GSYM word_add_n2w,
         align_mul2, align_plus2,
         METIS_PROVE [ALT_ZERO, ADD_CLAUSES]
           ``(ZERO + 1 = 1) /\ (n2w ZERO = 0w)``]);

val align_neq3 = Q.store_thm("align_neq3",
  `!a:word32 b m n.
     aligned (a, 2) ==>
     align (b, 2) <> a + n2w (NUMERAL (BIT1 n)) /\ (* 0,1 *)
     align (b, 2) + n2w (NUMERAL (BIT2 m)) <>
       a + n2w (NUMERAL (BIT1 n)) /\ (* 0,1 *)
     align (b, 2) + n2w (NUMERAL (BIT1 n)) <> a /\ (* 1,0 *)
     align (b, 2) + n2w (NUMERAL (BIT1 m)) <>
       a + n2w (NUMERAL (BIT2 n))`, (* 1,0 *)
  NTAC 5 STRIP_TAC
    \\ POP_ASSUM (fn th =>
         REPEAT CONJ_TAC \\
         ONCE_REWRITE_TAC [th |> REWRITE_RULE [aligned_def]])
    \\ REWRITE_TAC [align_neq]
    \\ ONCE_REWRITE_TAC [align_sum_numeric2]
    \\ REWRITE_TAC [align_neq, GSYM align_aligned, WORD_ADD_ASSOC]);

val neq_pc_plus4a = Q.prove(
  `(!b:word32 pc a.
      pc <> align ((if pc <> align (a + b,4) then a else a + 4w) + b,4)) /\
   (!pc:word32 a.
      pc + 1w <>
      align ((if pc <> align (a + 4w,4) then a else a + 4w),4) + 5w) /\
   (!pc:word32 a.
      pc + 2w <>
      align ((if pc <> align (a + 4w,4) then a else a + 4w),4) + 6w) /\
   (!pc:word32 a.
      pc + 3w <>
      align ((if pc <> align (a + 4w,4) then a else a + 4w),4) + 7w) /\
   (!pc:word32 a.
      pc + 1w <>
      align ((if pc <> align (a + 8w,4) then a else a + 4w),4) + 9w) /\
   (!pc:word32 a.
      pc + 2w <>
      align ((if pc <> align (a + 8w,4) then a else a + 4w),4) + 10w) /\
   (!pc:word32 a.
      pc + 3w <>
      align ((if pc <> align (a + 8w,4) then a else a + 4w),4) + 11w) /\
   (!pc:word32 a.
      pc + 1w <>
      align ((if pc <> align (a + 0xFFFFFFFCw,4) then a else a + 4w),4) +
      0xFFFFFFFDw) /\
   (!pc:word32 a.
      pc + 2w <>
      align ((if pc <> align (a + 0xFFFFFFFCw,4) then a else a + 4w),4) +
      0xFFFFFFFEw) /\
   (!pc:word32 a.
      pc + 3w <>
      align ((if pc <> align (a + 0xFFFFFFFCw,4) then a else a + 4w),4) +
      0xFFFFFFFFw)`,
  SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [align_plus4, align_plus_extra]
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_ARITH_EQ_ss)
         [align_aligned |> ONCE_REWRITE_RULE [WORD_ADD_COMM]]
);

val neq_pc_plus4 = Q.prove(
  `!b:word32 pc a.
      aligned (b,4) ==>
      pc <> align ((if pc <> align (a + b,4)
                    then a else a + 4w),4) + b`,
  SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [aligned_def, align_plus4]
    \\ Q.PAT_ASSUM `c = align (c,4)` SUBST_ALL_TAC
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_ARITH_EQ_ss)
         [align_aligned |> ONCE_REWRITE_RULE [WORD_ADD_COMM]]);

val neq_pc_plus4_plus = Q.prove(
  `(!a:word32 c d.
      aligned (c,4) ==>
      (align ((if pc <> align(x,4) then a else a + 4w) + c,4) =
       align (if pc <> align(x,4) then a else a + 4w,4) + c)) /\
   (!a:word32 c d.
      aligned (c,4) ==>
      (align ((if pc <> align(x,4) /\ y then a else a + 4w) + c,4) =
       align (if pc <> align(x,4) /\ y then a else a + 4w,4) + c))`,
  SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [aligned_def, align_plus4]
    \\ Q.PAT_ASSUM `c = align (c,4)` SUBST_ALL_TAC
    \\ FULL_SIMP_TAC (srw_ss())
         [align_aligned |> ONCE_REWRITE_RULE [WORD_ADD_COMM]]);

val neq_pc_plus4_plus = save_thm("neq_pc_plus4_plus",
  Drule.LIST_CONJ
    (List.map (fn thm => GEN_ALL (MATCH_MP (Drule.SPEC_ALL thm)
                   (aligned_numeric |> Thm.CONJUNCT2 |> Drule.SPEC_ALL)))
     (Drule.CONJUNCTS neq_pc_plus4_plus)));

val neq_pc_plus4 = save_thm("neq_pc_plus4",
  Drule.LIST_CONJ
    [neq_pc_plus4a,
     MATCH_MP (Drule.SPEC_ALL neq_pc_plus4)
       (aligned_numeric |> Thm.CONJUNCT2 |> Drule.SPEC_ALL),
     neq_pc_plus4 |> Q.SPEC `0w`
       |> REWRITE_RULE [Thm.CONJUNCT1 aligned_numeric, WORD_ADD_0]]);

val neq_pc_plus4_t2 = Q.prove(
  `(!b:word32 pc a.
      aligned (b,4) ==>
      pc <> align ((if pc <> align (a + b,4) /\ pc + 2w <> align (a + b,4)
                    then a else a + 4w),4) + b) /\
   (!b:word32 pc a.
      aligned (b,4) ==>
      pc + 2w <> align ((if pc <> align (a + b,4) /\ pc + 2w <> align (a + b,4)
                         then a else a + 4w),4) + b)`,
  SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [aligned_def, align_plus4]
    \\ Q.PAT_ASSUM `c = align (c,4)` SUBST_ALL_TAC
    \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_ARITH_EQ_ss)
         [align_aligned |> ONCE_REWRITE_RULE [WORD_ADD_COMM]]
    \\ ASM_REWRITE_TAC [wordsLib.WORD_DECIDE
         ``a + 0xFFFFFFFCw = a + 2w + 0xFFFFFFFAw:word32``]
    \\ EVAL_TAC);

val neq_pc_plus4_t2 = save_thm("neq_pc_plus4_t2",
  Drule.LIST_CONJ
    (List.map (fn thm => MATCH_MP (Drule.SPEC_ALL thm)
                      (aligned_numeric |> Thm.CONJUNCT2 |> Drule.SPEC_ALL))
    (Drule.CONJUNCTS neq_pc_plus4_t2)));

val aligned_over_memread = Q.store_thm("aligned_over_memread",
  `(!b x:word8 y.
      aligned (if b then x else y,4) =
      if b then aligned (x,4) else aligned (y,4)) /\
   (!b x:word8 y.
      aligned_bx (if b then x else y) =
      if b then aligned_bx x else aligned_bx y) /\
   (!b c x:word8 y z.
      aligned_bx (if b then x else if c then y else z) =
      if b then aligned_bx x else if c then aligned_bx y else aligned_bx z)`,
  SRW_TAC [] []);

val aligned_concat = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("aligned_concat",
  `!a:word8 b:word8 c:word8 d:word8.
     aligned ((a @@ b @@ c @@ d) : word32, 4) = aligned (d,4)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_248, aligned_def, align_248]);

val aligned_bx_concat = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("aligned_bx_concat",
  `!a:word8 b:word8 c:word8 d:word8.
     aligned_bx ((a @@ b @@ c @@ d) : word32) = aligned_bx d`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [aligned_bx_def]);

val aligned_bx_aligned_bx = Q.store_thm("aligned_bx_aligned_bx",
  `!a:word8. aligned_bx (if aligned_bx a then a else 0w)`,
  SRW_TAC [] [] \\ EVAL_TAC);

val it_mode_concat = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("it_mode_concat",
  `!a:word8 b:word8 c:word8 d:word8.
     ((4 >< 0) ((a @@ b @@ c @@ d) : word32) = (4 >< 0) d) /\
     ((15 >< 10) ((a @@ b @@ c @@ d) : word32) = (7 >< 2) c) /\
     ((26 >< 25) ((a @@ b @@ c @@ d) : word32) = (2 >< 1) a)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []);

(* ------------------------------------------------------------------------- *)

val extract_of_double_word = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("extract_of_double_word",
  `!a:word32 b:word32.
      ((63 >< 32) (a @@ b) = a) /\ ((31 >< 0 ) (a @@ b) = b)`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] []);

val aligned_pair = Q.prove(
  `!a:word32.
      aligned ((if aligned (a + a,4) then a else 0w) +
               (if aligned (a + a,4) then a else 0w), 4)`,
  SRW_TAC [] [] \\ EVAL_TAC);

fun aligned_neq_thms thm =
  MATCH_MP (Drule.SPEC_ALL align_neq2) (Drule.SPEC_ALL thm);

fun aligned_neq_thms2 thm =
  MATCH_MP (Drule.SPEC_ALL align_neq3) (Drule.SPEC_ALL thm);

val aligned_pair_thms = save_thm("aligned_pair_thms",
   aligned_neq_thms aligned_pair);

val aligned_shift_pair = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x a:word32.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a + FST (f (a,x)),4) then a else 0w) +
        FST (f (if aligned (a + FST (f (a,x)),4) then a else 0w,x)), 4)) /\
   (!f:bool[32] # num -> bool[32] # bool x a:word32.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
      aligned ((if aligned (a + -FST (f (a,x)),4) then a else 0w) +
        -FST (f (if aligned (a + -FST (f (a,x)),4) then a else 0w,x)), 4))`,
  SRW_TAC [] [] \\ EVAL_TAC);

val aligned_rrx_pair = Q.prove(
  `(!x a:word32.
      aligned ((if aligned (a + SND (word_rrx (x,a)),4) then a else 0w) +
        SND (word_rrx (x,
                if aligned (a + SND (word_rrx (x,a)),4) then a else 0w)), 4)) /\
   (!x a:word32.
      aligned ((if aligned (a + -SND (word_rrx (x,a)),4) then a else 0w) +
       -SND (word_rrx (x,
                if aligned (a + -SND (word_rrx (x,a)),4) then a else 0w)), 4))`,
  CONJ_TAC \\ Cases \\ SRW_TAC [] [] \\ EVAL_TAC);

val aligned_shift_pair_thms =
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`,`a`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`,`a`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
    (Drule.CONJUNCTS aligned_shift_pair)));

val aligned_rm_thms = Q.store_thm("aligned_rm_thms",
  `(!pc:word32 b.
     aligned (align (pc,4) + 8w +
              if aligned (align (pc,4) + 8w + b,4) then b else 0w,4)) /\
   (!pc:word32 b.
     aligned (align (pc,4) + 8w +
              -(if aligned (align (pc,4) + 8w + -b,4) then b else 0w),4)) /\
   (!pc:word32 b.
     aligned (align (pc,4) + 8w +
              (if aligned (align (pc,4) + 8w + b,4) then b else 0w) + 4w,4)) /\
   (!pc:word32 b.
     aligned (align (pc,4) + 8w +
             -(if aligned (align (pc,4) + 8w + -b,4) then b else 0w) + 4w,4)) /\
   (!pc:word32 b.
     aligned (align (pc,4) + 8w +
              if aligned (align (pc,4) + 8w + b,2) then b else 0w,2)) /\
   (!pc:word32 b.
     aligned (align (pc,4) + 8w +
              -(if aligned (align (pc,4) + 8w + -b,2) then b else 0w),2))`,
  SRW_TAC [] [aligned_sum] \\ EVAL_TAC
    \\ FULL_SIMP_TAC std_ss [aligned_def, align_aligned, aligned_align,
          align_plus4, WORD_EQ_ADD_LCANCEL, EVAL ``-1w:word32``,
          wordsLib.WORD_DECIDE ``b + a + 8w = a + (b + 8w) : word32``,
          wordsLib.WORD_DECIDE ``b + a + 12w = a + (b + 8w + 4w) : word32``]
    \\ POP_ASSUM (SUBST1_TAC o SYM) \\ DECIDE_TAC);

val aligned_shift_rm = Q.prove(
  `(!f:bool[32] # num -> bool[32] # bool x.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned (align (pc,4) + 8w +
              FST (f (if aligned (align (pc,4) + 8w + FST (f (b,x)),4)
                      then b else 0w,x)),4)) /\
   (!f:bool[32] # num -> bool[32] # bool x.
      x <> 0 /\ (FST (f (0w, x)) = 0w) ==>
     aligned (align (pc,4) + 8w +
              -FST (f (if aligned (align (pc,4) + 8w + -FST (f (b,x)),4)
                       then b else 0w,x)),4))`,
  SRW_TAC [] [aligned_sum] \\ EVAL_TAC);

val aligned_rrx_rm_thms = Q.store_thm("aligned_rrx_rm_thms",
  `(!pc:word32 b x.
     aligned
       (align (pc,4) + 8w +
        SND (word_rrx (x,if aligned (align (pc,4) + 8w + SND (word_rrx (x,b)),4)
                         then b else 0w)),4)) /\
   (!pc:word32 b x.
     aligned
       (align (pc,4) + 8w +
        -SND (word_rrx (x,
           if aligned (align (pc,4) + 8w + -SND (word_rrx (x,b)),4)
           then b else 0w)),4))`,
  REPEAT STRIP_TAC \\ Cases_on `x`
    \\ SRW_TAC [] [aligned_sum, word_rrx_0] \\ EVAL_TAC);

val aligned_shift_rm_thms = save_thm("aligned_shift_rm_thms",
  Drule.LIST_CONJ (List.concat
    (List.map (fn thm =>
       List.map (fn t => (CONJ (thm |> Q.SPECL [t,`NUMERAL (BIT1 n)`])
                               (thm |> Q.SPECL [t,`NUMERAL (BIT2 n)`]))
                    |> SIMP_RULE std_ss [NUMERAL_NOT_ZERO,NUMERAL_FST_SHIFT_C])
       [`LSL_C`,`LSR_C`,`ASR_C`,`ROR_C`])
    (Drule.CONJUNCTS aligned_shift_rm))));

val aligned_rrx_pair_thms = save_thm("aligned_rrx_pair_thms",
  Drule.LIST_CONJ
    (List.map aligned_neq_thms (Drule.CONJUNCTS aligned_rrx_pair)));

val aligned_shift_pair_thms = save_thm("aligned_shift_pair_thms",
  Drule.LIST_CONJ
    (List.map aligned_neq_thms (Drule.CONJUNCTS aligned_shift_pair_thms)));

val aligned_align_shift_rm_thms = save_thm("aligned_align_shift_rm_thms",
  Drule.LIST_CONJ
    (List.map aligned_neq_thms (Drule.CONJUNCTS aligned_shift_rm_thms)));

val aligned_align_rrx_rm_thms = save_thm("aligned_align_rrx_rm_thms",
  Drule.LIST_CONJ
    (List.map aligned_neq_thms (Drule.CONJUNCTS aligned_rrx_rm_thms)));

val aligned_align_rm_thms = save_thm("aligned_align_rm_thms",
  Drule.LIST_CONJ
    ((List.map aligned_neq_thms
       (List.take(Drule.CONJUNCTS aligned_rm_thms,4))) @
     (List.map aligned_neq_thms2
       (List.drop(Drule.CONJUNCTS aligned_rm_thms,4)))));

val aligned_0_thms = save_thm("aligned_0_thms",
  aligned_neq_thms (``aligned (0w:word32, 4)`` |> EVAL |> EQT_ELIM)
    |> SIMP_RULE (srw_ss()) []);

val aligned_align_thms = save_thm("aligned_align_thms",
  aligned_neq_thms (aligned_align |> Drule.CONJUNCTS |> el 4));

val aligned_align_thms2 = save_thm("aligned_align_thms2",
  aligned_neq_thms2 (aligned_align |> Drule.CONJUNCTS |> el 3));

(* ------------------------------------------------------------------------- *)

val _ = Parse.overload_on
  ("GOOD_MODE", ``\m:word5. m IN {16w; 17w; 18w; 19w; 23w; 27w; 31w}``);

val good_mode = Q.store_thm("good_mode",
  `(!n:word32.
     (4 >< 0) (if GOOD_MODE ((4 >< 0) n) then n else n || 31w) <> 22w:word5) /\
   (!n:word32.
     GOOD_MODE ((4 >< 0) (if GOOD_MODE ((4 >< 0) n) then n else n || 31w))) /\
   (!n:word8.
     (4 >< 0) (if GOOD_MODE ((4 >< 0) n) then n else n || 31w) <> 22w:word5) /\
   (!n:word8.
     GOOD_MODE ((4 >< 0) (if GOOD_MODE ((4 >< 0) n) then n else n || 31w))) /\
   (!psr.
     (if GOOD_MODE (psr.M) /\ (psr.IT = 0w) then psr
      else psr with <| IT := 0w; M := 16w |>).M <> 22w) /\
   (!psr.
     GOOD_MODE ((if GOOD_MODE (psr.M) /\ (psr.IT = 0w) then psr
                 else psr with <| IT := 0w; M := 16w |>).M))`,
  SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_EXTRACT_ss) []);

val good_it = Q.store_thm("good_it",
  `!b it:word8. (if b /\ (it = 0w) then it else 0w) = 0w`,
  SRW_TAC [] []);

val IT_concat = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("IT_concat",
  `!w:word8. (7 >< 2) w @@ (1 >< 0) w = w`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] []);

val IT_concat0 = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("IT_concat0",
  `!a:word8 b:word8. ((7 >< 2) a @@ (2 >< 1) b = 0w) =
                     ((7 >< 2) a = 0w) /\ ((2 >< 1) b = 0w)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [] \\ DECIDE_TAC);

val divisor_neq_zero = Q.store_thm("divisor_neq_zero",
  `!m:word32. (if m <> 0w then m else 1w) <> 0w`,
  SRW_TAC [] []);

val it_con_thm = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("it_con_thm",
  `(!a:word8. (7 >< 2) (if (7 >< 2) a = 0w then a else 0w) = 0w) /\
   (!a:word8. (2 >< 1) (if (2 >< 1) a = 0w then a else 0w) = 0w)`,
  SRW_TAC [] []);

val it_mode_imp_thm = with_flag (wordsLib.guessing_word_lengths,true)
  Q.store_thm("it_mode_imp_thm",
  `(!a:word8 b:word8 c:word8 d:word8.
     GOOD_MODE ((4 >< 0) (a @@ b @@ c @@ d)) ==> GOOD_MODE ((4 >< 0) d)) /\
   (!a:word8 b:word8 c:word8 d:word8.
     ((15 >< 10) (a @@ b @@ c @@ d) @@ (26 >< 25) (a @@ b @@ c @@ d) = 0w) ==>
      ((2 >< 1) a = 0w) /\ ((7 >< 2) c = 0w))`,
  SRW_TAC [] [it_mode_concat, IT_concat0]);

(* ------------------------------------------------------------------------- *)

val FCP_ISET = Q.prove(
   `((FCP i. F) = 0w:word2) /\ ((FCP i. (i = 0)) = 1w:word2) /\
    ((FCP i. (i = 1)) = 2w:word2) /\ ((FCP i. (i = 1) \/ (i = 0)) = 3w:word2)`,
  SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []);

val bx_write_pc_thm = Q.prove(
  `!address:word32.
       (if address ' 0 then
          select_instr_set ii InstrSet_Thumb >>=
          (\u. branch_to ii ((31 '' 1) address))
        else if ~(address ' 1) then
          select_instr_set ii InstrSet_ARM >>=
          (\u. branch_to ii address)
        else
          errorT s) =
       if aligned_bx address then
           (\s.
             if (s.psrs (ii.proc,CPSR)).J /\ (s.psrs (ii.proc,CPSR)).T /\
               ~(address ' 0)
             then
               errorT "select_instr_set: unpredictable" s
             else
               write_cpsr ii
                 ((s.psrs (ii.proc,CPSR)) with
                     <| J := F; T := address ' 0 |>) s) >>=
           (\u. branch_to ii
              (if address ' 0 then (31 '' 1) address else address))
       else
         errorT s`,
  SRW_TAC [] [aligned_bx_thm, select_instr_set_def,
              current_instr_set_def,
              read_isetstate_def, write_isetstate_def,
              read_cpsr_def, read__psr_def,
              write_cpsr_def, write__psr_def,
              seqT_def, readT_def, writeT_def, constT_def,
              EVAL ``1w:word2 ' 1``, EVAL ``1w:word2 ' 0``, word_0,  FUN_EQ_THM]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `(x.psrs (ii.proc,CPSR)).J`
    \\ Cases_on `(x.psrs (ii.proc,CPSR)).T`
    \\ ASM_SIMP_TAC (srw_ss()) [FCP_ISET]);

val align32 =
  align_248 |> INST_TYPE [alpha |-> ``:32``]
            |> SIMP_RULE (srw_ss()) []
            |> GSYM;

val bx_write_pc = save_thm("bx_write_pc",
  SIMP_RULE std_ss [align32, bx_write_pc_thm, branch_to_def] bx_write_pc_def);

val branch_write_pc = Q.store_thm("branch_write_pc",
  `!address ii.
     branch_write_pc ii address =
     seqT (parT (arch_version ii) (read_cpsr ii))
     (\(version,cpsr).
       if version < 6 /\ ~aligned(address,4) /\ ~cpsr.J /\ ~cpsr.T
       then
         errorT "branch_write_pc: unpredictable"
       else
         branch_to ii
           (if ~cpsr.J /\ ~cpsr.T then
              align (address,4)
            else
              align (address,2)))`,
  SRW_TAC [] [branch_write_pc_def, arch_version_def, read_cpsr_def,
        read__psr_def, current_instr_set_def,
        read_isetstate_def, branch_to_def, errorT_def,
        read_arch_def, version_number_def,
        parT_def, seqT_def, readT_def, writeT_def,
        constT_def,
        FUN_EQ_THM]
    \\ Cases_on `(x.psrs (ii.proc,CPSR)).J`
    \\ Cases_on `(x.psrs (ii.proc,CPSR)).T`
    \\ ASM_SIMP_TAC (srw_ss()) [GSYM aligned_248, align32, FCP_ISET]);

val compare_branch_instr_thm = Q.prove(
  `!ii imm6:word6.
      (\rn:word32.
          if nonzero <=/=> (rn = 0w) then
            read_reg ii 15w >>=
            (\pc.
              let imm32 = w2w imm6 << 1 in
                branch_write_pc ii (pc + imm32))
          else
            increment_pc ii Encoding_Thumb) =
      (\rn.
         (read_reg ii 15w ||| current_instr_set ii) >>=
         (\(pc,iset).
            if (iset = InstrSet_ARM) then
              if nonzero <=/=> (rn = 0w) then
                branch_write_pc ii (pc + w2w imm6 << 1)
              else
                increment_pc ii Encoding_Thumb
            else
              branch_to ii (if nonzero <=/=> (rn = 0w) then
                              (31 '' 1) (pc + w2w imm6 << 1)
                            else
                              pc - 2w)))`,
  SRW_TAC [boolSimps.LET_ss] [current_instr_set_def,
        read_isetstate_def, read_cpsr_def, read__psr_def,
        read_reg_def, read_pc_def, read__reg_def,
        parT_def, seqT_def, readT_def, writeT_def,
        constT_def, branch_write_pc_def, arch_version_def,
        read_arch_def, branch_to_def,
        increment_pc_def,
        FUN_EQ_THM]
    \\ NTAC 2 (SRW_TAC [] []));

val compare_branch_instr = save_thm("compare_branch_instr",
  REWRITE_RULE [compare_branch_instr_thm, align32]
  arm_opsemTheory.compare_branch_instr);

val error_option_case_COND_RAND = Q.store_thm("error_option_case_COND_RAND",
  `!c f f1 a0 a1 a2 a3.
     error_option_CASE (if c then ValueState a0 a1 else ValueState a2 a3) f f1 =
     if c then
       f a0 a1
     else
       f a2 a3`,
  SRW_TAC [] []);

(* ------------------------------------------------------------------------- *)

val ARM_READ_REG_FROM_MODE = Q.store_thm("ARM_READ_REG_FROM_MODE",
  `(!s m. ARM_READ_REG_MODE (0w, m) s = ARM_READ_REG 0w s) /\
   (!s m. ARM_READ_REG_MODE (1w, m) s = ARM_READ_REG 1w s) /\
   (!s m. ARM_READ_REG_MODE (2w, m) s = ARM_READ_REG 2w s) /\
   (!s m. ARM_READ_REG_MODE (3w, m) s = ARM_READ_REG 3w s) /\
   (!s m. ARM_READ_REG_MODE (4w, m) s = ARM_READ_REG 4w s) /\
   (!s m. ARM_READ_REG_MODE (5w, m) s = ARM_READ_REG 5w s) /\
   (!s m. ARM_READ_REG_MODE (6w, m) s = ARM_READ_REG 6w s) /\
   (!s m. ARM_READ_REG_MODE (7w, m) s = ARM_READ_REG 7w s) /\
   (!s. (ARM_MODE s = 0b10001w) ==>
      (ARM_READ_REG_MODE (8w, 0b10001w) s = ARM_READ_REG 8w s)) /\
   (!s m. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_READ_REG_MODE (8w, m) s = ARM_READ_REG 8w s)) /\
   (!s. (ARM_MODE s = 0b10001w) ==>
      (ARM_READ_REG_MODE (9w, 0b10001w) s = ARM_READ_REG 9w s)) /\
   (!s m. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_READ_REG_MODE (9w, m) s = ARM_READ_REG 9w s)) /\
   (!s. (ARM_MODE s = 0b10001w) ==>
      (ARM_READ_REG_MODE (10w, 0b10001w) s = ARM_READ_REG 10w s)) /\
   (!s m. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_READ_REG_MODE (10w, m) s = ARM_READ_REG 10w s)) /\
   (!s. (ARM_MODE s = 0b10001w) ==>
      (ARM_READ_REG_MODE (11w, 0b10001w) s = ARM_READ_REG 11w s)) /\
   (!s m. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_READ_REG_MODE (11w, m) s = ARM_READ_REG 11w s)) /\
   (!s. (ARM_MODE s = 0b10001w) ==>
      (ARM_READ_REG_MODE (12w, 0b10001w) s = ARM_READ_REG 12w s)) /\
   (!s m. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_READ_REG_MODE (12w, m) s = ARM_READ_REG 12w s)) /\
   (!s m. (ARM_MODE s = m) ==>
      (ARM_READ_REG_MODE (13w, m) s = ARM_READ_REG 13w s)) /\
   (!s m. (ARM_MODE s = m) ==>
      (ARM_READ_REG_MODE (14w, m) s = ARM_READ_REG 14w s)) /\
   (!s m. ARM_READ_REG_MODE (15w,m) s = ARM_READ_REG 15w s)`,
  SRW_TAC [] [ARM_READ_REG_MODE_def,ARM_READ_REG_def,RevLookUpRName_def]);

val ARM_WRITE_REG_FROM_MODE = Q.store_thm("ARM_WRITE_REG_FROM_MODE",
  `(!s m d. ARM_WRITE_REG_MODE (0w, m) d s = ARM_WRITE_REG 0w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (1w, m) d s = ARM_WRITE_REG 1w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (2w, m) d s = ARM_WRITE_REG 2w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (3w, m) d s = ARM_WRITE_REG 3w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (4w, m) d s = ARM_WRITE_REG 4w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (5w, m) d s = ARM_WRITE_REG 5w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (6w, m) d s = ARM_WRITE_REG 6w d s) /\
   (!s m d. ARM_WRITE_REG_MODE (7w, m) d s = ARM_WRITE_REG 7w d s) /\
   (!s d. (ARM_MODE s = 0b10001w) ==>
      (ARM_WRITE_REG_MODE (8w, 0b10001w) d s = ARM_WRITE_REG 8w d s)) /\
   (!s m d. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_WRITE_REG_MODE (8w, m) d s = ARM_WRITE_REG 8w d s)) /\
   (!s d. (ARM_MODE s = 0b10001w) ==>
      (ARM_WRITE_REG_MODE (9w, 0b10001w) d s = ARM_WRITE_REG 9w d s)) /\
   (!s m d. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_WRITE_REG_MODE (9w, m) d s = ARM_WRITE_REG 9w d s)) /\
   (!s d. (ARM_MODE s = 0b10001w) ==>
      (ARM_WRITE_REG_MODE (10w, 0b10001w) d s = ARM_WRITE_REG 10w d s)) /\
   (!s m d. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_WRITE_REG_MODE (10w, m) d s = ARM_WRITE_REG 10w d s)) /\
   (!s d. (ARM_MODE s = 0b10001w) ==>
      (ARM_WRITE_REG_MODE (11w, 0b10001w) d s = ARM_WRITE_REG 11w d s)) /\
   (!s m d. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_WRITE_REG_MODE (11w, m) d s = ARM_WRITE_REG 11w d s)) /\
   (!s d. (ARM_MODE s = 0b10001w) ==>
      (ARM_WRITE_REG_MODE (12w, 0b10001w) d s = ARM_WRITE_REG 12w d s)) /\
   (!s m d. (ARM_MODE s <> 0b10001w) /\ (m <> 0b10001w) ==>
      (ARM_WRITE_REG_MODE (12w, m) d s = ARM_WRITE_REG 12w d s)) /\
   (!s m d. (ARM_MODE s = m) ==>
      (ARM_WRITE_REG_MODE (13w, m) d s = ARM_WRITE_REG 13w d s)) /\
   (!s m d. (ARM_MODE s = m) ==>
      (ARM_WRITE_REG_MODE (14w, m) d s = ARM_WRITE_REG 14w d s)) /\
   (!s m d. ARM_WRITE_REG_MODE (15w,m) d s = ARM_WRITE_REG 15w d s)`,
  SRW_TAC [] [ARM_WRITE_REG_MODE_def,ARM_WRITE_REG_def,RevLookUpRName_def]);

val ARM_READ_SPSR_FROM_MODE = Q.store_thm("ARM_READ_SPSR_FROM_MODE",
  `(!s. (ARM_MODE s = 0b10001w) ==>
     (ARM_READ_SPSR_MODE 0b10001w s = ARM_READ_SPSR s)) /\
   (!s. (ARM_MODE s = 0b10010w) ==>
     (ARM_READ_SPSR_MODE 0b10010w s = ARM_READ_SPSR s)) /\
   (!s. (ARM_MODE s = 0b10011w) ==>
     (ARM_READ_SPSR_MODE 0b10011w s = ARM_READ_SPSR s)) /\
   (!s. (ARM_MODE s = 0b10110w) ==>
     (ARM_READ_SPSR_MODE 0b10110w s = ARM_READ_SPSR s)) /\
   (!s. (ARM_MODE s = 0b10111w) ==>
     (ARM_READ_SPSR_MODE 0b10111w s = ARM_READ_SPSR s)) /\
   (!s. (ARM_MODE s = 0b11011w) ==>
     (ARM_READ_SPSR_MODE 0b11011w s = ARM_READ_SPSR s))`,
  SRW_TAC [] [ARM_READ_SPSR_def]);

val ARM_WRITE_SPSR_FROM_MODE = Q.store_thm("ARM_WRITE_SPSR_FROM_MODE",
  `(!d s. (ARM_MODE s = 0b10001w) ==>
     (ARM_WRITE_SPSR_MODE 0b10001w d s = ARM_WRITE_SPSR d s)) /\
   (!d s. (ARM_MODE s = 0b10010w) ==>
     (ARM_WRITE_SPSR_MODE 0b10010w d s = ARM_WRITE_SPSR d s)) /\
   (!d s. (ARM_MODE s = 0b10011w) ==>
     (ARM_WRITE_SPSR_MODE 0b10011w d s = ARM_WRITE_SPSR d s)) /\
   (!d s. (ARM_MODE s = 0b10110w) ==>
     (ARM_WRITE_SPSR_MODE 0b10110w d s = ARM_WRITE_SPSR d s)) /\
   (!d s. (ARM_MODE s = 0b10111w) ==>
     (ARM_WRITE_SPSR_MODE 0b10111w d s = ARM_WRITE_SPSR d s)) /\
   (!d s. (ARM_MODE s = 0b11011w) ==>
     (ARM_WRITE_SPSR_MODE 0b11011w d s = ARM_WRITE_SPSR d s))`,
  SRW_TAC [] [ARM_WRITE_SPSR_def]);

val ARM_WRITE_CPSR = Q.store_thm("ARM_WRITE_CPSR",
  `(!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with N := b) state =
         ARM_WRITE_STATUS psrN b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with Z := b) state =
         ARM_WRITE_STATUS psrZ b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with C := b) state =
         ARM_WRITE_STATUS psrC b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with V := b) state =
         ARM_WRITE_STATUS psrV b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with Q := b) state =
         ARM_WRITE_STATUS psrQ b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with J := b) state =
         ARM_WRITE_STATUS psrJ b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with E := b) state =
         ARM_WRITE_STATUS psrE b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with A := b) state =
         ARM_WRITE_STATUS psrA b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with I := b) state =
         ARM_WRITE_STATUS psrI b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with F := b) state =
         ARM_WRITE_STATUS psrF b state)) /\
   (!b state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with T := b) state =
         ARM_WRITE_STATUS psrT b state)) /\
   (!ge state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with GE := ge) state =
         ARM_WRITE_GE ge state)) /\
   (!it state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with IT := it) state =
         ARM_WRITE_IT it state)) /\
   (!m state cpsr.
      (ARM_READ_CPSR state = cpsr) ==>
        (ARM_WRITE_CPSR (cpsr with M := m) state =
         ARM_WRITE_MODE m state))`,
  SRW_TAC [] [ARM_WRITE_STATUS_def, ARM_WRITE_GE_def, ARM_WRITE_IT_def,
    ARM_WRITE_MODE_def, ARM_READ_CPSR_def, ARM_WRITE_CPSR_def,
    APPLY_UPDATE_THM, FUN_EQ_THM, arm_state_component_equality]);

val ARM_WRITE_SPSR = Q.store_thm("ARM_WRITE_SPSR",
  `(!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with N := b) state =
         ARM_WRITE_STATUS_SPSR psrN b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with Z := b) state =
         ARM_WRITE_STATUS_SPSR psrZ b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with C := b) state =
         ARM_WRITE_STATUS_SPSR psrC b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with V := b) state =
         ARM_WRITE_STATUS_SPSR psrV b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with Q := b) state =
         ARM_WRITE_STATUS_SPSR psrQ b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with J := b) state =
         ARM_WRITE_STATUS_SPSR psrJ b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with E := b) state =
         ARM_WRITE_STATUS_SPSR psrE b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with A := b) state =
         ARM_WRITE_STATUS_SPSR psrA b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with I := b) state =
         ARM_WRITE_STATUS_SPSR psrI b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with F := b) state =
         ARM_WRITE_STATUS_SPSR psrF b state)) /\
   (!b state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with T := b) state =
         ARM_WRITE_STATUS_SPSR psrT b state)) /\
   (!ge state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with GE := ge) state =
         ARM_WRITE_GE_SPSR ge state)) /\
   (!it state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with IT := it) state =
         ARM_WRITE_IT_SPSR it state)) /\
   (!m state cpsr.
      (ARM_READ_SPSR state = cpsr) ==>
        (ARM_WRITE_SPSR (cpsr with M := m) state =
         ARM_WRITE_MODE_SPSR m state))`,
  SRW_TAC [] [ARM_WRITE_STATUS_SPSR_def, ARM_WRITE_GE_SPSR_def,
    ARM_WRITE_IT_SPSR_def, ARM_WRITE_MODE_SPSR_def, ARM_READ_SPSR_def,
    ARM_WRITE_SPSR_def, ARM_READ_SPSR_MODE_def, ARM_WRITE_SPSR_MODE_def,
    APPLY_UPDATE_THM, FUN_EQ_THM, arm_state_component_equality]);

(* ------------------------------------------------------------------------- *)

val MARK_AND_CLEAR_EXCLUSIVE = Q.store_thm("MARK_AND_CLEAR_EXCLUSIVE",
  `(!mon mstate a n s.
     (mon = s.monitors) ==>
     (s with monitors := mon with state :=
       SND (mon.ClearExclusiveByAddress (a,<| proc := 0 |>,n)
            mstate) =
      CLEAR_EXCLUSIVE_BY_ADDRESS (a,n)
        (s with monitors := mon with state := mstate)) /\
     (s with monitors := mon with state := mon.state = s)) /\
   (!mon mstate a n s.
     (mon = s.monitors) ==>
     (s with monitors := mon with state :=
       SND (mon.MarkExclusiveLocal (a,<| proc := 0 |>,n)
            mstate) =
      MARK_EXCLUSIVE_LOCAL (a,n)
        (s with monitors := mon with state := mstate)) /\
     (s with monitors := mon with state := mon.state = s)) /\
   (!mon mstate a n s.
     (mon = s.monitors) ==>
     (s with monitors := mon with state :=
       SND (mon.MarkExclusiveGlobal (a,<| proc := 0 |>,n)
            mstate) =
      MARK_EXCLUSIVE_GLOBAL (a,n)
        (s with monitors := mon with state := mstate)) /\
     (s with monitors := mon with state := mon.state = s)) /\
   (!mon mstate s.
     (mon = s.monitors) ==>
     (s with monitors := mon with state :=
       SND (mon.ClearExclusiveLocal 0 mstate) =
      CLEAR_EXCLUSIVE_LOCAL
        (s with monitors := mon with state := mstate)) /\
     (s with monitors := mon with state := mon.state = s))`,
  SRW_TAC [] [CLEAR_EXCLUSIVE_BY_ADDRESS_def, MARK_EXCLUSIVE_GLOBAL_def,
    MARK_EXCLUSIVE_LOCAL_def, CLEAR_EXCLUSIVE_LOCAL_def,
    arm_state_component_equality, ExclusiveMonitors_component_equality]);

val ARM_WRITE_MEM_o = Q.store_thm("ARM_WRITE_MEM_o",
  `(!a w g s.
     (ARM_WRITE_MEM a w (s with memory updated_by g) =
       (s with memory updated_by (a =+ w) o g))) /\
   (!a w g s.
     (ARM_WRITE_MEM_WRITE a w (s with accesses updated_by g) =
       (s with accesses updated_by (CONS (MEM_WRITE a w)) o g))) /\
   (!a g s.
     (ARM_WRITE_MEM_READ a (s with accesses updated_by g) =
       (s with accesses updated_by (CONS (MEM_READ a)) o g)))`,
  SRW_TAC []
    [ARM_WRITE_MEM_def, ARM_WRITE_MEM_WRITE_def, ARM_WRITE_MEM_READ_def]);

val ARM_WRITE_REG_o = Q.store_thm("ARM_WRITE_REG_o",
  `!x w g s.
     (ARM_WRITE_REG_MODE x w (s with registers updated_by g) =
       (s with registers updated_by ((0,RevLookUpRName x) =+ w) o g))`,
  SRW_TAC [] [ARM_WRITE_REG_MODE_def]);

val ARM_WRITE_PSR_o = Q.store_thm("ARM_WRITE_PSR_o",
  `(!w g s.
     (ARM_WRITE_CPSR w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,CPSR) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b10001w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_fiq) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b10010w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_irq) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b10011w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_svc) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b10110w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_mon) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b10111w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_abt) =+ w) o g))) /\
   (!w g s.
     (ARM_WRITE_SPSR_MODE 0b11011w w (s with psrs updated_by g) =
       (s with psrs updated_by ((0,SPSR_und) =+ w) o g)))`,
  SRW_TAC [] [ARM_WRITE_CPSR_def, ARM_WRITE_SPSR_MODE_def, SPSR_MODE_def]);

val ARM_WRITE_CPSR_o = Q.store_thm("ARM_WRITE_CPSR_o",
  `(!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_N_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrN b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_Z_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrZ b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_C_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrC b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_V_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrV b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_Q_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrQ b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_J_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrJ b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_E_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrE b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_A_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrA b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_I_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrI b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_F_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrF b (ARM_WRITE_CPSR cpsr state)) /\
   (!b state cpsr.
       ARM_WRITE_CPSR (ARMpsr_T_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS psrT b (ARM_WRITE_CPSR cpsr state)) /\
   (!ge state cpsr.
       ARM_WRITE_CPSR (ARMpsr_GE_fupd (K ge) cpsr) state =
       ARM_WRITE_GE ge (ARM_WRITE_CPSR cpsr state)) /\
   (!it state cpsr.
       ARM_WRITE_CPSR (ARMpsr_IT_fupd (K it) cpsr) state =
       ARM_WRITE_IT it (ARM_WRITE_CPSR cpsr state))`,
  SRW_TAC [] [ARM_WRITE_STATUS_def, ARM_WRITE_GE_def, ARM_WRITE_IT_def,
    ARM_WRITE_MODE_def, ARM_READ_CPSR_def, ARM_WRITE_CPSR_def,
    APPLY_UPDATE_THM, FUN_EQ_THM, arm_state_component_equality]);

val SPSR_MODE_NOT_CPSR = Q.prove(
  `!m. SPSR_MODE m <> CPSR`,
  STRIP_TAC \\ Cases_on `m IN {17w; 18w; 19w; 22w; 23w}`
    \\ FULL_SIMP_TAC (srw_ss()) [SPSR_MODE_def]);

val ARM_WRITE_SPSR_o = Q.store_thm("ARM_WRITE_SPSR_o",
  `(!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_N_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrN b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_Z_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrZ b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_C_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrC b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_V_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrV b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_Q_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrQ b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_J_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrJ b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_E_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrE b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_A_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrA b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_I_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrI b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_F_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrF b (ARM_WRITE_SPSR cpsr state))) /\
   (!b state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_T_fupd (K b) cpsr) state =
       ARM_WRITE_STATUS_SPSR psrT b (ARM_WRITE_SPSR cpsr state))) /\
   (!ge state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_GE_fupd (K ge) cpsr) state =
       ARM_WRITE_GE_SPSR ge (ARM_WRITE_SPSR cpsr state))) /\
   (!it state cpsr.
      (ARM_WRITE_SPSR (ARMpsr_IT_fupd (K it) cpsr) state =
       ARM_WRITE_IT_SPSR it (ARM_WRITE_SPSR cpsr state)))`,
   SRW_TAC [] [ARM_WRITE_STATUS_SPSR_def, ARM_WRITE_GE_SPSR_def,
     ARM_WRITE_IT_SPSR_def, ARM_WRITE_MODE_SPSR_def, ARM_READ_SPSR_def,
     ARM_WRITE_SPSR_def, ARM_READ_SPSR_MODE_def, ARM_WRITE_SPSR_MODE_def,
     ARM_MODE_def, ARM_READ_CPSR_def, APPLY_UPDATE_THM, FUN_EQ_THM,
     SPSR_MODE_NOT_CPSR, arm_state_component_equality]);

(* ------------------------------------------------------------------------- *)

fun arm_reg_rule thm =
  Drule.LIST_CONJ
    (List.tabulate(16, fn i =>
      let val r = wordsSyntax.mk_wordii(i,4) in
        (GEN_ALL o RIGHT_CONV_RULE EVAL o Drule.SPEC_ALL o Thm.SPEC r) thm
      end));

local
  val regs =
        [(0, "10000"), (1, "10000"), (2, "10000"), (3, "10000"), (4, "10000"),
         (5, "10000"), (6, "10000"), (7, "10000"), (8, "10000"), (8, "10001"),
         (9, "10000"), (9, "10001"), (10,"10000"), (10,"10001"), (11,"10000"),
         (11,"10001"), (12,"10000"), (12,"10001"), (13,"10000"), (13,"10001"),
         (13,"10010"), (13,"10011"), (13,"10111"), (13,"11011"), (13,"10110"),
         (14,"10000"), (14,"10001"), (14,"10010"), (14,"10011"), (14,"10111"),
         (14,"11011"), (14,"10110"), (15,"10000")]
in
  fun arm_reg_rule thm =
    Drule.LIST_CONJ (List.map (fn (i,s) =>
      let val n = wordsSyntax.mk_wordii(i,4)
          val m = wordsSyntax.mk_wordi(Arbnum.fromBinString s,5)
          val x = pairSyntax.mk_pair(n,m)
      in
        (GEN_ALL o RIGHT_CONV_RULE EVAL o Drule.SPEC_ALL o Thm.SPEC x) thm
      end) regs)
end;

val ARM_READ_REG_MODE = save_thm("ARM_READ_REG_MODE",
  SIMP_RULE (srw_ss()) [ARM_READ_REG_FROM_MODE]
    (arm_reg_rule ARM_READ_REG_MODE_def));

val ARM_WRITE_REG_MODE = save_thm("ARM_WRITE_REG_MODE",
  SIMP_RULE (srw_ss()) [ARM_WRITE_REG_FROM_MODE]
    (arm_reg_rule ARM_WRITE_REG_MODE_def));

Theorem ARM_WRITE_REG_o[allow_rebind] =
  SIMP_RULE (srw_ss()) [ARM_WRITE_REG_FROM_MODE]
            (arm_reg_rule ARM_WRITE_REG_o);

(* ------------------------------------------------------------------------- *)

val PSR_OF_UPDATES = Q.store_thm("PSR_OF_UPDATES",
  `(!n m d s. ARM_READ_CPSR (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_CPSR s) /\
   (!n d s. ARM_READ_CPSR (ARM_WRITE_REG n d s) = ARM_READ_CPSR s) /\
   (!a d s. ARM_READ_CPSR (ARM_WRITE_MEM a d s) = ARM_READ_CPSR s) /\
   (!a d s. ARM_READ_CPSR (ARM_WRITE_MEM_WRITE a d s) = ARM_READ_CPSR s) /\
   (!a s. ARM_READ_CPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_CPSR s) /\
   (!d s. ARM_READ_CPSR (ARM_WRITE_CPSR d s) = d) /\
   (!d s. ARM_READ_CPSR (ARM_WRITE_SPSR d s) = ARM_READ_CPSR s) /\
   (!m d s. ARM_READ_CPSR (ARM_WRITE_SPSR_MODE m d s) = ARM_READ_CPSR s) /\
   (!f d s. ARM_READ_CPSR (ARM_WRITE_STATUS_SPSR f d s) = ARM_READ_CPSR s) /\
   (!d s. ARM_READ_CPSR (ARM_WRITE_GE_SPSR d s) = ARM_READ_CPSR s) /\
   (!x y s. ARM_READ_CPSR (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
            ARM_READ_CPSR s) /\
   (!d s. ARM_READ_CPSR (ARM_WRITE_IT_SPSR d s) = ARM_READ_CPSR s) /\
   (!d s. ARM_READ_CPSR (ARM_WRITE_MODE_SPSR d s) = ARM_READ_CPSR s) /\
   (!n m d s. ARM_READ_SPSR (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_SPSR s) /\
   (!n d s. ARM_READ_SPSR (ARM_WRITE_REG n d s) = ARM_READ_SPSR s) /\
   (!a d s. ARM_READ_SPSR (ARM_WRITE_MEM a d s) = ARM_READ_SPSR s) /\
   (!a d s. ARM_READ_SPSR (ARM_WRITE_MEM_WRITE a d s) = ARM_READ_SPSR s) /\
   (!a s. ARM_READ_SPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_SPSR s) /\
   (!d s. ARM_READ_SPSR (ARM_WRITE_CPSR d s) = ARM_READ_SPSR_MODE d.M s) /\
   (!d s. ARM_READ_SPSR (ARM_WRITE_SPSR d s) = d)`,
  REPEAT STRIP_TAC \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_WRITE_REG_MODE_def, ARM_WRITE_REG_def, ARM_WRITE_MEM_def,
                   ARM_WRITE_MEM_READ_def, ARM_WRITE_MEM_WRITE_def,
                   ARM_WRITE_SPSR_def, ARM_WRITE_CPSR_def, ARM_READ_CPSR_def,
                   ARM_WRITE_SPSR_MODE_def, ARM_WRITE_STATUS_SPSR_def,
                   ARM_WRITE_GE_SPSR_def, ARM_WRITE_IT_SPSR_def,
                   ARM_WRITE_MODE_SPSR_def, ARM_READ_SPSR_def,
                   CLEAR_EXCLUSIVE_BY_ADDRESS_def]
    \\ SRW_TAC [] [ARM_WRITE_SPSR_MODE_def, SPSR_MODE_NOT_CPSR, UPDATE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def, SPSR_MODE_NOT_CPSR,
         ARM_READ_SPSR_MODE_def, ARM_READ_CPSR_def]);

val CPSR_COMPONENTS_OF_UPDATES = Q.store_thm("CPSR_COMPONENTS_OF_UPDATES",
  `(!f n m d s.
      ARM_READ_STATUS f (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_STATUS f s) /\
   (!f n d s. ARM_READ_STATUS f (ARM_WRITE_REG n d s) = ARM_READ_STATUS f s) /\
   (!f a d s. ARM_READ_STATUS f (ARM_WRITE_MEM a d s) = ARM_READ_STATUS f s) /\
   (!f a d s. ARM_READ_STATUS f (ARM_WRITE_MEM_WRITE a d s) =
              ARM_READ_STATUS f s) /\
   (!f a s. ARM_READ_STATUS f (ARM_WRITE_MEM_READ a s) = ARM_READ_STATUS f s) /\
   (!f ge s. ARM_READ_STATUS f (ARM_WRITE_GE ge s) = ARM_READ_STATUS f s) /\
   (!f it s. ARM_READ_STATUS f (ARM_WRITE_IT it s) = ARM_READ_STATUS f s) /\
   (!f m s. ARM_READ_STATUS f (ARM_WRITE_MODE m s) = ARM_READ_STATUS f s) /\
   (!f b s. ARM_READ_STATUS f (ARM_WRITE_STATUS f b s) = b) /\
   (!f f2 b s. f2 <> f ==>
        (ARM_READ_STATUS f (ARM_WRITE_STATUS f2 b s) = ARM_READ_STATUS f s)) /\
   (!f x y s. ARM_READ_STATUS f (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
              ARM_READ_STATUS f s) /\
   (!f d s. ARM_READ_STATUS f (ARM_WRITE_SPSR d s) = ARM_READ_STATUS f s) /\
   (!f it s. ARM_READ_STATUS f (ARM_WRITE_IT_SPSR it s) =
             ARM_READ_STATUS f s) /\
   (!f ge s. ARM_READ_STATUS f (ARM_WRITE_GE_SPSR ge s) =
             ARM_READ_STATUS f s) /\
   (!f m s. ARM_READ_STATUS f (ARM_WRITE_MODE_SPSR m s) =
            ARM_READ_STATUS f s) /\
   (!f f2 b s. ARM_READ_STATUS f (ARM_WRITE_STATUS_SPSR f2 b s) =
               ARM_READ_STATUS f s) /\
   (!n m d s. ARM_READ_IT (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_IT s) /\
   (!n d s. ARM_READ_IT (ARM_WRITE_REG n d s) = ARM_READ_IT s) /\
   (!a d s. ARM_READ_IT (ARM_WRITE_MEM a d s) = ARM_READ_IT s) /\
   (!a d s. ARM_READ_IT (ARM_WRITE_MEM_WRITE a d s) = ARM_READ_IT s) /\
   (!a s. ARM_READ_IT (ARM_WRITE_MEM_READ a s) = ARM_READ_IT s) /\
   (!ge s. ARM_READ_IT (ARM_WRITE_GE ge s) = ARM_READ_IT s) /\
   (!it s. ARM_READ_IT (ARM_WRITE_IT it s) = it) /\
   (!m s. ARM_READ_IT (ARM_WRITE_MODE m s) = ARM_READ_IT s) /\
   (!f b s. ARM_READ_IT (ARM_WRITE_STATUS f b s) = ARM_READ_IT s) /\
   (!d s. ARM_READ_IT (ARM_WRITE_SPSR d s) = ARM_READ_IT s) /\
   (!it s. ARM_READ_IT (ARM_WRITE_IT_SPSR it s) = ARM_READ_IT s) /\
   (!ge s. ARM_READ_IT (ARM_WRITE_GE_SPSR ge s) = ARM_READ_IT s) /\
   (!m s. ARM_READ_IT (ARM_WRITE_MODE_SPSR m s) = ARM_READ_IT s) /\
   (!f b s. ARM_READ_IT (ARM_WRITE_STATUS_SPSR f b s) = ARM_READ_IT s) /\
   (!n m d s. ARM_READ_GE (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_GE s) /\
   (!n d s. ARM_READ_GE (ARM_WRITE_REG n d s) = ARM_READ_GE s) /\
   (!a d s. ARM_READ_GE (ARM_WRITE_MEM a d s) = ARM_READ_GE s) /\
   (!a d s. ARM_READ_GE (ARM_WRITE_MEM_WRITE a d s) = ARM_READ_GE s) /\
   (!a s. ARM_READ_GE (ARM_WRITE_MEM_READ a s) = ARM_READ_GE s) /\
   (!ge s. ARM_READ_GE (ARM_WRITE_GE ge s) = ge) /\
   (!it s. ARM_READ_GE (ARM_WRITE_IT it s) = ARM_READ_GE s) /\
   (!m s. ARM_READ_GE (ARM_WRITE_MODE m s) = ARM_READ_GE s) /\
   (!f b s. ARM_READ_GE (ARM_WRITE_STATUS f b s) = ARM_READ_GE s) /\
   (!d s. ARM_READ_GE (ARM_WRITE_SPSR d s) = ARM_READ_GE s) /\
   (!it s. ARM_READ_GE (ARM_WRITE_IT_SPSR it s) = ARM_READ_GE s) /\
   (!ge s. ARM_READ_GE (ARM_WRITE_GE_SPSR ge s) = ARM_READ_GE s) /\
   (!m s. ARM_READ_GE (ARM_WRITE_MODE_SPSR m s) = ARM_READ_GE s) /\
   (!f b s. ARM_READ_GE (ARM_WRITE_STATUS_SPSR f b s) = ARM_READ_GE s) /\
   (!n m d s. ARM_MODE (ARM_WRITE_REG_MODE (n,m) d s) = ARM_MODE s) /\
   (!n d s. ARM_MODE (ARM_WRITE_REG n d s) = ARM_MODE s) /\
   (!a d s. ARM_MODE (ARM_WRITE_MEM a d s) = ARM_MODE s) /\
   (!a d s. ARM_MODE (ARM_WRITE_MEM_WRITE a d s) = ARM_MODE s) /\
   (!a s. ARM_MODE (ARM_WRITE_MEM_READ a s) = ARM_MODE s) /\
   (!it s. ARM_MODE (ARM_WRITE_IT it s) = ARM_MODE s) /\
   (!ge s. ARM_MODE (ARM_WRITE_GE ge s) = ARM_MODE s) /\
   (!m s. ARM_MODE (ARM_WRITE_MODE m s) = m) /\
   (!f b s. ARM_MODE (ARM_WRITE_STATUS f b s) = ARM_MODE s) /\
   (!d s. ARM_MODE (ARM_WRITE_SPSR d s) = ARM_MODE s) /\
   (!it s. ARM_MODE (ARM_WRITE_IT_SPSR it s) = ARM_MODE s) /\
   (!ge s. ARM_MODE (ARM_WRITE_GE_SPSR ge s) = ARM_MODE s) /\
   (!m s. ARM_MODE (ARM_WRITE_MODE_SPSR m s) = ARM_MODE s) /\
   (!f b s. ARM_MODE (ARM_WRITE_STATUS_SPSR f b s) = ARM_MODE s)`,
  REPEAT STRIP_TAC \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_MODE_def, ARM_READ_STATUS_def, ARM_READ_IT_def,
         ARM_READ_GE_def, PSR_OF_UPDATES]
    \\ TRY (Cases_on `f2`)
    \\ SIMP_TAC (srw_ss()) [ARM_READ_CPSR_def, ARM_WRITE_CPSR_def,
         ARM_READ_SPSR_def, ARM_WRITE_SPSR_def, ARM_WRITE_SPSR_MODE_def,
         ARM_WRITE_STATUS_SPSR_def, ARM_WRITE_IT_SPSR_def,
         ARM_WRITE_GE_SPSR_def, ARM_WRITE_MODE_SPSR_def,
         ARM_WRITE_STATUS_def, ARM_WRITE_IT_def, ARM_WRITE_GE_def,
         ARM_WRITE_MODE_def, SPSR_MODE_NOT_CPSR, UPDATE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [SPSR_MODE_NOT_CPSR, UPDATE_def,
         ARM_READ_SPSR_MODE_def, ARM_WRITE_SPSR_MODE_def]);

val SPSR_COMPONENTS_OF_UPDATES = Q.store_thm("SPSR_COMPONENTS_OF_UPDATES",
  `(!f n m d s. ARM_READ_STATUS_SPSR f (ARM_WRITE_REG_MODE (n,m) d s) =
                ARM_READ_STATUS_SPSR f s) /\
   (!f n d s. ARM_READ_STATUS_SPSR f (ARM_WRITE_REG n d s) =
              ARM_READ_STATUS_SPSR f s) /\
   (!f a d s. ARM_READ_STATUS_SPSR f (ARM_WRITE_MEM a d s) =
              ARM_READ_STATUS_SPSR f s) /\
   (!f a d s. ARM_READ_STATUS_SPSR f (ARM_WRITE_MEM_WRITE a d s) =
              ARM_READ_STATUS_SPSR f s) /\
   (!f a s. ARM_READ_STATUS_SPSR f (ARM_WRITE_MEM_READ a s) =
            ARM_READ_STATUS_SPSR f s) /\
   (!f f2 b s. ARM_READ_STATUS_SPSR f (ARM_WRITE_STATUS f2 b s) =
               ARM_READ_STATUS_SPSR f s) /\
   (!f ge s. ARM_READ_STATUS_SPSR f (ARM_WRITE_GE ge s) =
             ARM_READ_STATUS_SPSR f s) /\
   (!f it s. ARM_READ_STATUS_SPSR f (ARM_WRITE_IT it s) =
             ARM_READ_STATUS_SPSR f s) /\
   (!f b s. ARM_READ_STATUS_SPSR f (ARM_WRITE_STATUS_SPSR f b s) = b) /\
   (!f f2 b s. f <> f2 ==>
       (ARM_READ_STATUS_SPSR f (ARM_WRITE_STATUS_SPSR f2 b s) =
        ARM_READ_STATUS_SPSR f s)) /\
   (!f ge s. ARM_READ_STATUS_SPSR f (ARM_WRITE_GE_SPSR ge s) =
             ARM_READ_STATUS_SPSR f s) /\
   (!f it s. ARM_READ_STATUS_SPSR f (ARM_WRITE_IT_SPSR it s) =
             ARM_READ_STATUS_SPSR f s) /\
   (!f m s. ARM_READ_STATUS_SPSR f (ARM_WRITE_MODE_SPSR m s) =
            ARM_READ_STATUS_SPSR f s) /\
   (!n m d s. ARM_READ_IT_SPSR (ARM_WRITE_REG_MODE (n,m) d s) =
              ARM_READ_IT_SPSR s) /\
   (!n d s. ARM_READ_IT_SPSR (ARM_WRITE_REG n d s) = ARM_READ_IT_SPSR s) /\
   (!a d s. ARM_READ_IT_SPSR (ARM_WRITE_MEM a d s) = ARM_READ_IT_SPSR s) /\
   (!a d s. ARM_READ_IT_SPSR (ARM_WRITE_MEM_WRITE a d s) =
            ARM_READ_IT_SPSR s) /\
   (!a s. ARM_READ_IT_SPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_IT_SPSR s) /\
   (!f b s. ARM_READ_IT_SPSR (ARM_WRITE_STATUS f b s) = ARM_READ_IT_SPSR s) /\
   (!ge s. ARM_READ_IT_SPSR (ARM_WRITE_GE ge s) = ARM_READ_IT_SPSR s) /\
   (!it s. ARM_READ_IT_SPSR (ARM_WRITE_IT it s) = ARM_READ_IT_SPSR s) /\
   (!f b s. ARM_READ_IT_SPSR (ARM_WRITE_STATUS_SPSR f b s) =
            ARM_READ_IT_SPSR s) /\
   (!ge s. ARM_READ_IT_SPSR (ARM_WRITE_GE_SPSR ge s) = ARM_READ_IT_SPSR s) /\
   (!it s. ARM_READ_IT_SPSR (ARM_WRITE_IT_SPSR it s) = it) /\
   (!m s. ARM_READ_IT_SPSR (ARM_WRITE_MODE_SPSR m s) = ARM_READ_IT_SPSR s) /\
   (!n m d s. ARM_READ_GE_SPSR (ARM_WRITE_REG_MODE (n,m) d s) =
              ARM_READ_GE_SPSR s) /\
   (!n d s. ARM_READ_GE_SPSR (ARM_WRITE_REG n d s) = ARM_READ_GE_SPSR s) /\
   (!a d s. ARM_READ_GE_SPSR (ARM_WRITE_MEM a d s) = ARM_READ_GE_SPSR s) /\
   (!a d s. ARM_READ_GE_SPSR (ARM_WRITE_MEM_WRITE a d s) =
            ARM_READ_GE_SPSR s) /\
   (!a s. ARM_READ_GE_SPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_GE_SPSR s) /\
   (!f b s. ARM_READ_GE_SPSR (ARM_WRITE_STATUS f b s) = ARM_READ_GE_SPSR s) /\
   (!ge s. ARM_READ_GE_SPSR (ARM_WRITE_GE ge s) = ARM_READ_GE_SPSR s) /\
   (!it s. ARM_READ_GE_SPSR (ARM_WRITE_IT it s) = ARM_READ_GE_SPSR s) /\
   (!f b s. ARM_READ_GE_SPSR (ARM_WRITE_STATUS_SPSR f b s) =
            ARM_READ_GE_SPSR s) /\
   (!ge s. ARM_READ_GE_SPSR (ARM_WRITE_GE_SPSR ge s) = ge) /\
   (!it s. ARM_READ_GE_SPSR (ARM_WRITE_IT_SPSR it s) = ARM_READ_GE_SPSR s) /\
   (!m s. ARM_READ_GE_SPSR (ARM_WRITE_MODE_SPSR m s) = ARM_READ_GE_SPSR s) /\
   (!n m d s. ARM_READ_MODE_SPSR (ARM_WRITE_REG_MODE (n,m) d s) =
              ARM_READ_MODE_SPSR s) /\
   (!n d s. ARM_READ_MODE_SPSR (ARM_WRITE_REG n d s) = ARM_READ_MODE_SPSR s) /\
   (!a d s. ARM_READ_MODE_SPSR (ARM_WRITE_MEM a d s) = ARM_READ_MODE_SPSR s) /\
   (!a d s. ARM_READ_MODE_SPSR (ARM_WRITE_MEM_WRITE a d s) =
            ARM_READ_MODE_SPSR s) /\
   (!a s. ARM_READ_MODE_SPSR (ARM_WRITE_MEM_READ a s) = ARM_READ_MODE_SPSR s) /\
   (!f b s. ARM_READ_MODE_SPSR (ARM_WRITE_STATUS f b s) =
            ARM_READ_MODE_SPSR s) /\
   (!ge s. ARM_READ_MODE_SPSR (ARM_WRITE_GE ge s) = ARM_READ_MODE_SPSR s) /\
   (!it s. ARM_READ_MODE_SPSR (ARM_WRITE_IT it s) = ARM_READ_MODE_SPSR s) /\
   (!f b s. ARM_READ_MODE_SPSR (ARM_WRITE_STATUS_SPSR f b s) =
            ARM_READ_MODE_SPSR s) /\
   (!ge s. ARM_READ_MODE_SPSR (ARM_WRITE_GE_SPSR ge s) =
           ARM_READ_MODE_SPSR s) /\
   (!it s. ARM_READ_MODE_SPSR (ARM_WRITE_IT_SPSR it s) =
           ARM_READ_MODE_SPSR s) /\
   (!m s. ARM_READ_MODE_SPSR (ARM_WRITE_MODE_SPSR m s) = m)`,
  REPEAT STRIP_TAC \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_READ_SPSR_def, ARM_READ_STATUS_SPSR_def,
         ARM_READ_IT_SPSR_def, ARM_READ_GE_SPSR_def, ARM_READ_MODE_SPSR_def,
         PSR_OF_UPDATES, ARM_MODE_def]
    \\ TRY (Cases_on `f2`)
    \\ SIMP_TAC (srw_ss()) [ARM_READ_CPSR_def, ARM_MODE_def, ARM_WRITE_CPSR_def,
         ARM_READ_SPSR_def, ARM_WRITE_SPSR_def, ARM_WRITE_SPSR_MODE_def,
         ARM_WRITE_STATUS_SPSR_def, ARM_WRITE_IT_SPSR_def,
         ARM_WRITE_GE_SPSR_def, ARM_WRITE_MODE_SPSR_def,
         ARM_WRITE_STATUS_def, ARM_WRITE_IT_def, ARM_WRITE_GE_def,
         ARM_WRITE_MODE_def, SPSR_MODE_NOT_CPSR, UPDATE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [SPSR_MODE_NOT_CPSR, UPDATE_def,
         ARM_READ_SPSR_MODE_def, ARM_WRITE_SPSR_MODE_def]);

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val RevLookUpRName = Q.store_thm("RevLookUpRName",
  `((RevLookUpRName (n,m) = RName_0usr) = (n = 0w)) /\
   ((RevLookUpRName (n,m) = RName_1usr) = (n = 1w)) /\
   ((RevLookUpRName (n,m) = RName_2usr) = (n = 2w)) /\
   ((RevLookUpRName (n,m) = RName_3usr) = (n = 3w)) /\
   ((RevLookUpRName (n,m) = RName_4usr) = (n = 4w)) /\
   ((RevLookUpRName (n,m) = RName_5usr) = (n = 5w)) /\
   ((RevLookUpRName (n,m) = RName_6usr) = (n = 6w)) /\
   ((RevLookUpRName (n,m) = RName_7usr) = (n = 7w)) /\
   ((RevLookUpRName (n,m) = RName_8usr) = (n = 8w) /\ m <> 17w) /\
   ((RevLookUpRName (n,m) = RName_8fiq) = (n = 8w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_9usr) = (n = 9w) /\ m <> 17w) /\
   ((RevLookUpRName (n,m) = RName_9fiq) = (n = 9w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_10usr) = (n = 10w) /\ m <> 17w) /\
   ((RevLookUpRName (n,m) = RName_10fiq) = (n = 10w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_11usr) = (n = 11w) /\ m <> 17w) /\
   ((RevLookUpRName (n,m) = RName_11fiq) = (n = 11w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_12usr) = (n = 12w) /\ m <> 17w) /\
   ((RevLookUpRName (n,m) = RName_12fiq) = (n = 12w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_SPusr) = (n = 13w) /\
                                           m NOTIN {17w;18w;19w;22w;23w;27w}) /\
   ((RevLookUpRName (n,m) = RName_SPfiq) = (n = 13w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_SPirq) = (n = 13w) /\ (m = 18w)) /\
   ((RevLookUpRName (n,m) = RName_SPsvc) = (n = 13w) /\ (m = 19w)) /\
   ((RevLookUpRName (n,m) = RName_SPmon) = (n = 13w) /\ (m = 22w)) /\
   ((RevLookUpRName (n,m) = RName_SPabt) = (n = 13w) /\ (m = 23w)) /\
   ((RevLookUpRName (n,m) = RName_SPund) = (n = 13w) /\ (m = 27w)) /\
   ((RevLookUpRName (n,m) = RName_LRusr) = (n = 14w) /\
                                           m NOTIN {17w;18w;19w;22w;23w;27w}) /\
   ((RevLookUpRName (n,m) = RName_LRfiq) = (n = 14w) /\ (m = 17w)) /\
   ((RevLookUpRName (n,m) = RName_LRirq) = (n = 14w) /\ (m = 18w)) /\
   ((RevLookUpRName (n,m) = RName_LRsvc) = (n = 14w) /\ (m = 19w)) /\
   ((RevLookUpRName (n,m) = RName_LRmon) = (n = 14w) /\ (m = 22w)) /\
   ((RevLookUpRName (n,m) = RName_LRabt) = (n = 14w) /\ (m = 23w)) /\
   ((RevLookUpRName (n,m) = RName_LRund) = (n = 14w) /\ (m = 27w)) /\
   ((RevLookUpRName (n,m) = RName_PC) = (n = 15w))`,
  wordsLib.Cases_on_word `n`
    \\ RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [LESS_THM])
    \\ FULL_SIMP_TAC bool_ss [] \\ EVAL_TAC
    \\ Cases_on `m = 17w`
    \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC
    \\ Cases_on `(m = 18w) \/ (m = 19w) \/ (m = 22w) \/ (m = 23w) \/ (m = 27w)`
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ EVAL_TAC);

val RevLookUpRName_neq = Q.store_thm("RevLookUpRName_neq",
  `!n1 n2 m1 m2.
      n1 <> n2 ==> RevLookUpRName (n1, m1) <> RevLookUpRName (n2, m2)`,
  REPEAT STRIP_TAC
    \\ Cases_on `RevLookUpRName (n1, m1)`
    \\ Cases_on `RevLookUpRName (n2, m2)`
    \\ FULL_SIMP_TAC (srw_ss()) [RevLookUpRName]);

val REG_MODE_OF_UPDATES = Q.store_thm("REG_MODE_OF_UPDATES",
  `(!n1 n2 m1 m2 d s. n1 <> n2 ==>
      (ARM_READ_REG_MODE (n1,m1) (ARM_WRITE_REG_MODE (n2,m2) d s) =
       ARM_READ_REG_MODE (n1,m1) s)) /\
   (!n1 n2 m d s. n1 <> n2 ==>
      (ARM_READ_REG_MODE (n1,m) (ARM_WRITE_REG n2 d s) =
       ARM_READ_REG_MODE (n1,m) s)) /\
   (!n m d s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_REG_MODE (n,m) d s) = d) /\
   (!n m a d s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_MEM a d s) =
                ARM_READ_REG_MODE (n,m) s) /\
   (!n m a d s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_MEM_WRITE a d s) =
                ARM_READ_REG_MODE (n,m) s) /\
   (!n m a s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_MEM_READ a s) =
              ARM_READ_REG_MODE (n,m) s) /\
   (!n m x y s. ARM_READ_REG_MODE (n,m) (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
                ARM_READ_REG_MODE (n,m) s) /\
   (!n m it s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_IT it s) =
               ARM_READ_REG_MODE (n,m) s) /\
   (!n m ge s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_GE ge s) =
               ARM_READ_REG_MODE (n,m) s) /\
   (!n m1 m2 s. ARM_READ_REG_MODE (n,m1) (ARM_WRITE_MODE m2 s) =
                ARM_READ_REG_MODE (n,m1) s) /\
   (!n m f b s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_STATUS f b s) =
                ARM_READ_REG_MODE (n,m) s) /\
   (!n m d s. ARM_READ_REG_MODE (n,m) (ARM_WRITE_SPSR d s) =
              ARM_READ_REG_MODE (n,m) s)`,
  SRW_TAC [] [ARM_WRITE_REG_MODE_def, ARM_WRITE_REG_def, ARM_WRITE_MEM_def,
              ARM_WRITE_MEM_WRITE_def, ARM_WRITE_MEM_READ_def,
              ARM_WRITE_SPSR_def, ARM_WRITE_IT_def, ARM_WRITE_GE_def,
              ARM_WRITE_MODE_def, ARM_WRITE_CPSR_def, ARM_READ_REG_MODE_def,
              CLEAR_EXCLUSIVE_BY_ADDRESS_def]
    \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_WRITE_SPSR_MODE_def, ARM_WRITE_STATUS_def,
                   ARM_WRITE_CPSR_def,  UPDATE_def]
    \\ METIS_TAC [RevLookUpRName_neq]);

val REG_OF_UPDATES = Q.prove(
  `(!n1 n2 m d s. n1 <> n2 ==>
      (ARM_READ_REG n1 (ARM_WRITE_REG_MODE (n2,m) d s) = ARM_READ_REG n1 s)) /\
   (!n1 n2 d s. n1 <> n2 ==>
      (ARM_READ_REG n1 (ARM_WRITE_REG n2 d s) = ARM_READ_REG n1 s)) /\
   (!n d s. ARM_READ_REG n (ARM_WRITE_REG n d s) = d) /\
   (!n a d s. ARM_READ_REG n (ARM_WRITE_MEM a d s) = ARM_READ_REG n s) /\
   (!n a d s. ARM_READ_REG n (ARM_WRITE_MEM_WRITE a d s) = ARM_READ_REG n s) /\
   (!n a s. ARM_READ_REG n (ARM_WRITE_MEM_READ a s) = ARM_READ_REG n s) /\
   (!n x y s. ARM_READ_REG n (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) =
              ARM_READ_REG n s) /\
   (!n it s. ARM_READ_REG n (ARM_WRITE_IT it s) = ARM_READ_REG n s) /\
   (!n ge s. ARM_READ_REG n (ARM_WRITE_GE ge s) = ARM_READ_REG n s) /\
   (!n m s. ARM_READ_REG n (ARM_WRITE_MODE m s) = ARM_READ_REG_MODE (n,m) s) /\
   (!n f b s. ARM_READ_REG n (ARM_WRITE_STATUS f b s) = ARM_READ_REG n s) /\
   (!n d s.  ARM_READ_REG n (ARM_WRITE_SPSR d s) = ARM_READ_REG n s)`,
  SRW_TAC []
    [ARM_READ_REG_def, ARM_WRITE_REG_def, REG_MODE_OF_UPDATES,
     CPSR_COMPONENTS_OF_UPDATES, ARM_MODE_def, PSR_OF_UPDATES]);

val REG_OF_UPDATES = save_thm("REG_OF_UPDATES",
  CONJ REG_MODE_OF_UPDATES REG_OF_UPDATES);

val MEM_OF_UPDATES = Q.store_thm("MEM_OF_UPDATES",
  `(!a n m d s.
      ARM_READ_MEM a (ARM_WRITE_REG_MODE (n,m) d s) = ARM_READ_MEM a s) /\
   (!a n d s. ARM_READ_MEM a (ARM_WRITE_REG n d s) = ARM_READ_MEM a s) /\
   (!a d s. ARM_READ_MEM a (ARM_WRITE_MEM a d s) = d) /\
   (!a b x s. ~(a = b) ==>
      (ARM_READ_MEM a (ARM_WRITE_MEM b x s) = ARM_READ_MEM a s)) /\
   (!a b d s. ARM_READ_MEM a (ARM_WRITE_MEM_WRITE b d s) = ARM_READ_MEM a s) /\
   (!a b s. ARM_READ_MEM a (ARM_WRITE_MEM_READ b s) = ARM_READ_MEM a s) /\
   (!a x y s.
      ARM_READ_MEM a (CLEAR_EXCLUSIVE_BY_ADDRESS (x,y) s) = ARM_READ_MEM a s) /\
   (!a it s. ARM_READ_MEM a (ARM_WRITE_IT it s) = ARM_READ_MEM a s) /\
   (!a ge s. ARM_READ_MEM a (ARM_WRITE_GE ge s) = ARM_READ_MEM a s) /\
   (!a m s. ARM_READ_MEM a (ARM_WRITE_MODE m s) = ARM_READ_MEM a s) /\
   (!a f b s. ARM_READ_MEM a (ARM_WRITE_STATUS f b s) = ARM_READ_MEM a s) /\
   (!a d s. ARM_READ_MEM a (ARM_WRITE_SPSR d s) = ARM_READ_MEM a s)`,
  SRW_TAC [] [ARM_WRITE_REG_MODE_def, ARM_WRITE_REG_def, ARM_WRITE_MEM_def,
              ARM_WRITE_MEM_READ_def, ARM_WRITE_MEM_WRITE_def,
              ARM_WRITE_SPSR_def, ARM_WRITE_IT_def, ARM_WRITE_GE_def,
              ARM_WRITE_MODE_def, ARM_WRITE_CPSR_def, ARM_READ_MEM_def,
              CLEAR_EXCLUSIVE_BY_ADDRESS_def]
    \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_WRITE_SPSR_MODE_def, ARM_WRITE_STATUS_def,
                   ARM_WRITE_CPSR_def, UPDATE_def]);

val MONITORS_OF_UPDATES = Q.store_thm("MONITORS_OF_UPDATES",
  `(!n m d s.  (ARM_WRITE_REG_MODE (n,m) d s).monitors = s.monitors) /\
   (!n d s. (ARM_WRITE_REG n d s).monitors = s.monitors) /\
   (!a d s. (ARM_WRITE_MEM a d s).monitors = s.monitors) /\
   (!a d s. (ARM_WRITE_MEM_WRITE a d s).monitors = s.monitors) /\
   (!a s. (ARM_WRITE_MEM_READ a s).monitors = s.monitors) /\
   (!it s. (ARM_WRITE_IT it s).monitors = s.monitors) /\
   (!ge s. (ARM_WRITE_GE ge s).monitors = s.monitors) /\
   (!m s. (ARM_WRITE_MODE m s).monitors = s.monitors) /\
   (!f b s. (ARM_WRITE_STATUS f b s).monitors = s.monitors) /\
   (!d s. (ARM_WRITE_SPSR d s).monitors = s.monitors)`,
  SRW_TAC [] [ARM_WRITE_REG_MODE_def, ARM_WRITE_REG_def, ARM_WRITE_MEM_def,
              ARM_WRITE_MEM_READ_def, ARM_WRITE_MEM_WRITE_def,
              ARM_WRITE_SPSR_def, ARM_WRITE_IT_def, ARM_WRITE_GE_def,
              ARM_WRITE_MODE_def, ARM_WRITE_CPSR_def]
    \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [ARM_WRITE_SPSR_MODE_def, ARM_WRITE_STATUS_def,
                   ARM_WRITE_CPSR_def, UPDATE_def]);

val ARM_READ_CPSR_COMPONENT_UNCHANGED =
  Q.store_thm("ARM_READ_CPSR_COMPONENT_UNCHANGED",
  `(!b s. (ARM_READ_STATUS psrN s = b) ==>
          ((ARM_READ_CPSR s with N := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrZ s = b) ==>
          ((ARM_READ_CPSR s with Z := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrC s = b) ==>
          ((ARM_READ_CPSR s with C := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrV s = b) ==>
          ((ARM_READ_CPSR s with V := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrQ s = b) ==>
          ((ARM_READ_CPSR s with Q := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrJ s = b) ==>
          ((ARM_READ_CPSR s with J := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrE s = b) ==>
          ((ARM_READ_CPSR s with E := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrA s = b) ==>
          ((ARM_READ_CPSR s with A := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrI s = b) ==>
          ((ARM_READ_CPSR s with I := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrF s = b) ==>
          ((ARM_READ_CPSR s with F := b) = ARM_READ_CPSR s)) /\
   (!b s. (ARM_READ_STATUS psrT s = b) ==>
          ((ARM_READ_CPSR s with T := b) = ARM_READ_CPSR s)) /\
   (!it s. (ARM_READ_IT s = it) ==>
          ((ARM_READ_CPSR s with IT := it) = ARM_READ_CPSR s)) /\
   (!ge s. (ARM_READ_GE s = ge) ==>
          ((ARM_READ_CPSR s with GE := ge) = ARM_READ_CPSR s)) /\
   (!m s. (ARM_MODE s = m) ==>
          ((ARM_READ_CPSR s with M := m) = ARM_READ_CPSR s))`,
  SRW_TAC [] [arm_state_component_equality, ARMpsr_component_equality,
    UPDATE_APPLY_IMP_ID,
    ARM_MODE_def, ARM_WRITE_MODE_def,
    ARM_READ_GE_def, ARM_WRITE_GE_def,
    ARM_READ_IT_def, ARM_WRITE_IT_def,
    ARM_READ_STATUS_def, ARM_WRITE_STATUS_def,
    ARM_READ_CPSR_def, ARM_WRITE_CPSR_def,
    ARM_READ_REG_MODE_def, ARM_WRITE_REG_MODE_def,
    ARM_READ_REG_def, ARM_WRITE_REG_def,
    ARM_READ_MEM_def, ARM_WRITE_MEM_def]);

val ARM_READ_UNCHANGED = Q.store_thm("ARM_READ_UNCHANGED",
  `(!f b s. (ARM_READ_STATUS f s = b) ==> (ARM_WRITE_STATUS f b s = s)) /\
   (!it s. (ARM_READ_IT s = it) ==> (ARM_WRITE_IT it s = s)) /\
   (!ge s. (ARM_READ_GE s = ge) ==> (ARM_WRITE_GE ge s = s)) /\
   (!m s. (ARM_MODE s = m) ==> (ARM_WRITE_MODE m s = s)) /\
   (!cpsr s. (ARM_READ_CPSR s = cpsr) ==> (ARM_WRITE_CPSR cpsr s = s)) /\
   (!f b s. (ARM_READ_STATUS_SPSR f s = b) ==>
            (ARM_WRITE_STATUS_SPSR f b s = s)) /\
   (!it s. (ARM_READ_IT_SPSR s = it) ==> (ARM_WRITE_IT_SPSR it s = s)) /\
   (!ge s. (ARM_READ_GE_SPSR s = ge) ==> (ARM_WRITE_GE_SPSR ge s = s)) /\
   (!m s. (ARM_READ_MODE_SPSR s = m) ==> (ARM_WRITE_MODE_SPSR m s = s)) /\
   (!w s. (ARM_READ_SPSR s = w) ==> (ARM_WRITE_SPSR w s = s)) /\
   (!n w s. (ARM_READ_REG n s = w) ==> (ARM_WRITE_REG n w s = s)) /\
   (!n m w s. (ARM_READ_REG_MODE (n,m) s = w) ==>
              (ARM_WRITE_REG_MODE (n,m) w s = s))`, (* /\
   (!a w s. (ARM_READ_MEM a s = w) ==> (ARM_WRITE_MEM a w s = s))`, *)
  REPEAT STRIP_TAC \\ TRY (Cases_on `f`)
    \\ SRW_TAC [] [arm_state_component_equality, ARMpsr_component_equality,
         UPDATE_APPLY_IMP_ID,
         ARM_MODE_def, ARM_WRITE_MODE_def,
         ARM_READ_MODE_SPSR_def, ARM_WRITE_MODE_SPSR_def,
         ARM_READ_GE_def, ARM_WRITE_GE_def,
         ARM_READ_GE_SPSR_def, ARM_WRITE_GE_SPSR_def,
         ARM_READ_IT_def, ARM_WRITE_IT_def,
         ARM_READ_IT_SPSR_def, ARM_WRITE_IT_SPSR_def,
         ARM_READ_STATUS_def, ARM_WRITE_STATUS_def,
         ARM_READ_STATUS_SPSR_def, ARM_WRITE_STATUS_SPSR_def,
         ARM_READ_CPSR_def, ARM_WRITE_CPSR_def,
         ARM_READ_SPSR_def, ARM_WRITE_SPSR_def,
         ARM_READ_SPSR_MODE_def, ARM_WRITE_SPSR_MODE_def,
         ARM_READ_REG_MODE_def, ARM_WRITE_REG_MODE_def,
         ARM_READ_REG_def, ARM_WRITE_REG_def,
         ARM_READ_MEM_def, ARM_WRITE_MEM_def]);

val ARM_READ_STATUS_UPDATES = Q.store_thm("ARM_READ_STATUS_UPDATES",
  `(!state state'.
       (ARM_READ_STATUS psrN state <=/=> ARM_READ_STATUS psrV state) /\
       (ARM_READ_STATUS psrV state' = ARM_READ_STATUS psrV state) ==>
       (ARM_WRITE_STATUS psrV (~ARM_READ_STATUS psrN state) state' = state')) /\
   (!state state'.
       ~(ARM_READ_STATUS psrC state /\ ~ARM_READ_STATUS psrZ state) /\
       (ARM_READ_STATUS psrC state' = ARM_READ_STATUS psrC state) ==>
       (ARM_WRITE_STATUS psrC
          (ARM_READ_STATUS psrZ state /\
           ARM_READ_STATUS psrC state) state' = state'))`,
  REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (Thm.CONJUNCT1 ARM_READ_UNCHANGED)
    \\ METIS_TAC []);

(* ------------------------------------------------------------------------- *)

val _ = wordsLib.guess_lengths();

val ARM_ALIGN_BX_def = Define`
  (ARM_ALIGN_BX ii npass (opc:word32) enc instr) : bool option M =
  let align_pc =
        seqT (read__reg ii RName_PC)
        (\pc. write__reg ii RName_PC
                (align(pc,if enc = Encoding_ARM then 4 else 2)))
  and write___reg n v =
        seqT (read_cpsr ii)
        (\cpsr.
           seqT (LookUpRName ii (n, cpsr.M))
           (\rname. write__reg ii rname v))
  in
  let align_dp opc n mode1 version rn C =
    if version >= 7 then (* aligned_bx result *)
      if (n = 15w) \/ (opc = 0b1101w) \/ (opc = 0b1111w) then
        if opc IN {0b0000w; 0b1110w} then (* AND, BIC *)
          align_pc
        else
         (case mode1
          of Mode1_register imm5 type m =>
              (if (m = 15w) /\ (type = 0b00w) /\ (imm5 = 0w) then
                 align_pc
               else
                 if m = 15w then
                   address_mode1 ii F mode1 >>=
                   (\(shifted,C_shift).
                     let result = FST (data_processing_alu opc rn shifted C) in
                       read__reg ii RName_PC >>=
                       (\pc.
                          write__reg ii RName_PC
                            (if aligned(pc,4) /\ aligned_bx result
                             then pc else -8w)))
                 else
                   align_pc >>=
                   (\u:unit.
                     ((if opc IN {0b1101w; 0b1111w} then
                         constT 0w
                       else
                         read_reg ii n) ||| read_reg ii m |||
                      address_mode1 ii F mode1) >>=
                     (\(rn,rm,(shifted,C_shift)).
                       let result = FST (data_processing_alu opc rn shifted C)
                       in
                         write___reg m (if aligned_bx result then rm else 0w))))
             | _ => align_pc)
      else
        align_pc >>=
        (\u:unit.
           address_mode1 ii F mode1 >>=
           (\(shifted,C_shift).
             let result = FST (data_processing_alu opc rn shifted C) in
             let align_rn =
                   write___reg n
                     (if aligned_bx result then
                        rn
                      else if opc IN {0b0000w; 0b1110w} then (* AND, BIC *)
                        0w
                      else if opc = 0b1100w then (* ORR *)
                        1w
                      else if opc = 0b0001w then (* EOR *)
                        shifted
                      else
                        rn ?? 1w)
             in
             let align_shift_reg m =
                   if n = m then
                     write___reg n (if aligned_bx result then rn else 0w)
                   else
                     align_rn
             in
               (case mode1
                of Mode1_immediate _                     => align_rn
                 | Mode1_register _ _ m                  => align_shift_reg m
                 | Mode1_register_shifted_register _ _ m => constT ())))
    else (* version < 6, aligned (result,4) *)
      if (n = 15w) \/ (opc = 0b1101w) \/ (opc = 0b1111w) then
        (case mode1
          of Mode1_register imm5 type m =>
               (if opc IN {0b0000w; 0b1110w} then (* AND, BIC *)
                  align_pc
                else if m = 15w then
                  if (type = 0b00w) /\ (imm5 = 0w) then
                    align_pc
                  else
                    address_mode1 ii F mode1 >>=
                    (\(shifted,C_shift).
                      let result = FST (data_processing_alu opc rn shifted C) in
                        read__reg ii RName_PC >>=
                        (\pc.
                           write__reg ii RName_PC
                             (if aligned(pc,4) /\ aligned(result,4) then
                                pc
                              else
                                -8w)))
                else
                  align_pc >>=
                  (\u:unit.
                    ((if opc IN {0b1101w; 0b1111w} then
                         constT 0w
                       else
                         read_reg ii n) |||
                     read_reg ii m ||| address_mode1 ii F mode1) >>=
                    (\(rn,rm,(shifted,C_shift)).
                      let result = FST (data_processing_alu opc rn shifted C) in
                        write___reg m
                          (if aligned(result,4) then rm else
                             case opc
                               of 0b0101w => if C then -1w else 0w
                                | 0b0110w => if C then 0w else -1w
                                | 0b0111w => if C then 0w else 1w
                                | 0b1111w => -1w
                                | _       => 0w))))
           | _ => align_pc)
      else
        align_pc >>=
        (\u:unit.
           address_mode1 ii F mode1 >>=
           (\(shifted,C_shift).
             let result = FST (data_processing_alu opc rn shifted C) in
               (case mode1
                of Mode1_immediate _ =>
                     write___reg n
                      (case opc
                       of 0b0000w => (* AND *)
                           (if aligned(result,4) then rn else 0w)
                        | 0b1110w => (* BIC *)
                           (if aligned(result,4) then rn else 0w)
                        | 0b0001w => (* EOR *)
                           (if aligned(result,4) then rn else shifted)
                        | 0b1100w => (* ORR *)
                           (align(rn,4)) (* possibly no solution *)
                        | 0b0010w => (* SUB *)
                           (align(result,4) + shifted)
                        | 0b0011w => (* RSB *)
                           (shifted - align(result,4))
                        | 0b0100w => (* ADD *)
                           (align(result,4) - shifted)
                        | 0b0101w => (* ADC *)
                           (align(result,4) - shifted - if C then 1w else 0w)
                        | 0b0110w => (* SBC *)
                           (align(result,4) + shifted + if C then 0w else 1w)
                        | _       => (* RSC *)
                           (shifted + (if C then 0w else -1w) -
                            align(result,4)))
                 | Mode1_register imm5 type m =>
                     if n = m then
                       if opc IN {0b0101w; 0b0110w; 0b0111w} then
                         constT () (* no solution *)
                       else
                         write___reg n (if aligned(result,4) then rn else 0w)
                     else if opc = 0b1100w then (* ORR *)
                       write___reg n (if aligned(result,4) then rn else 0w) >>=
                       (\u:unit.
                          if m = 15w then
                            read__reg ii RName_PC >>=
                            (\pc.
                               write__reg ii RName_PC
                                 (if (type = 0b00w) /\ (imm5 = 0w) \/
                                     aligned(result,4)
                                  then pc else -8w))
                          else
                            (read_reg ii m >>=
                             (\rm.
                                 write___reg m
                                   (if aligned(result,4) then rm else 0w))))
                     else
                       write___reg n
                         (case opc
                          of 0b0000w => (* AND *)
                              (if aligned(result,4) then rn else 0w)
                           | 0b1110w => (* BIC *)
                              (if aligned(result,4) then rn else 0w)
                           | 0b0001w => (* EOR *)
                              (if aligned(result,4) then rn else shifted)
                           | 0b0010w => (* SUB *)
                              (align(result,4) + shifted)
                           | 0b0011w => (* RSB *)
                              (shifted - align(result,4))
                           | 0b0100w => (* ADD *)
                              (align(result,4) - shifted)
                           | 0b0101w => (* ADC *)
                              (align(result,4) - shifted - if C then 1w else 0w)
                           | 0b0110w => (* SBC *)
                              (align(result,4) + shifted + if C then 0w else 1w)
                           | _       => (* RSC *)
                              (shifted + (if C then 0w else -1w) -
                               align(result,4)))
                 | Mode1_register_shifted_register _ _ m => constT ())))
  and align_br m =
        align_pc >>=
        (\u:unit.
          condT (m <> 15w)
            (read_reg ii m >>=
             (\rm. write___reg m (if aligned_bx rm then rm else 0w))) >>=
           (\u:unit. constT NONE))
  and good_spsr_mode =
        (read_cpsr ii ||| read_spsr ii) >>=
        (\(cpsr,spsr).
          write_spsr ii
            (if GOOD_MODE spsr.M /\ (spsr.IT = 0w) then spsr
             else spsr with <| M := 16w; IT := 0w |>))
  in
    if npass then align_pc >>= (\u:unit. constT NONE) else
    case instr
      of Branch (Branch_Exchange m) => (* bx_write *)
           align_br m
       | Branch (Branch_Link_Exchange_Register m) => (* bx_write *)
           align_br m
       | DataProcessing (Add_Sub add n d imm12) =>
           (* alu_write *)
           align_pc >>=
           (\u:unit.
               if (enc = Encoding_ARM) /\ (d = 15w) /\ n <> 15w then
                 arch_version ii >>=
                 (\version.
                    condT (version <> 6)
                      ((read_reg ii n ||| arm_expand_imm ii imm12) >>=
                       (\(rn,imm32).
                          let result = if add then rn + imm32 else rn - imm32
                          in
                            write___reg n
                              (if version >= 7 then
                                 if aligned_bx result then rn else rn ?? 1w
                               else (* version < 6 *)
                                 align(result, 4) - (result - rn)))) >>=
                      (\u:unit. constT NONE))
               else if (enc = Encoding_Thumb2) /\ (d = 13w) /\ n <> 15w then
                 (read_reg ii n ||| arm_expand_imm ii imm12) >>=
                 (\(rn,imm32).
                    let result = if add then rn + imm32 else rn - imm32
                    in
                      write___reg n (align(result, 4) - (result - rn)) >>=
                      (\u:unit. constT NONE))
               else
                 constT NONE)
       | DataProcessing (Data_Processing opc setflags n d mode1) =>
           (* alu_write or branch_write *)
            condT (setflags /\ (d = 15w) /\
                   ((enc = Encoding_ARM) \/
                    (enc = Encoding_Thumb2) /\ (n = 14w) /\ (opc = 0b0010w)))
               good_spsr_mode >>=
            (\u:unit.
              (if (enc = Encoding_ARM) /\ (d = 15w) /\ ((3 -- 2 ) opc) <> 2w
               then
                 arch_version ii >>=
                 (\version.
                    (if (version = 6) \/ (version >= 7) /\ setflags then
                       align_pc
                     else
                       ((if opc IN {0b1101w; 0b1111w} then
                            constT 0w
                          else
                            read_reg ii n) ||| read_flags ii) >>=
                        (\(rn,(N,Z,C,V)).
                           align_dp opc n mode1 version rn C)) >>=
                     (\u:unit. constT NONE))
               else if enc <> Encoding_ARM /\ (d = 13w) /\
                       opc IN {0b0010w; 0b0100w; 0b1101w}
               then
                 (read_reg ii n ||| read_flags ii) >>=
                 (\(rn,(N,Z,C,V)).
                    align_dp opc n mode1 4 rn C >>= (\u:unit. constT NONE))
               else
                 align_pc >>= (\u:unit. constT NONE)))
       | DataProcessing (Divide _ _ _ m) =>
           align_pc >>=
           (\u:unit.
              condT (m <> 15w)
                (read_reg ii m >>=
                 (\rm. write___reg m (if rm <> 0w then rm else 1w))) >>=
              (\u:unit. constT NONE))
       | LoadStore (Load indx add load_byte _ _ n t mode2) => (* load_write *)
           align_pc >>=
           (\u:unit.
             if ~load_byte /\ (t = 15w) then
               if n = 15w then
                 (case mode2 of
                    Mode2_register 2w 0w m =>
                     ((read_reg ii m >>=
                       (\rm.
                          write___reg m
                          (if rm << 2 <> 0xFFFFFFF8w then rm else 0w))) >>=
                       (\u:unit. constT (SOME T)))
                  | _ => constT (SOME T))
               else
                  arch_version ii >>=
                  (\version.
                     condT (if version >= 5 then
                               ~aligned_bx opc \/
                               (enc = Encoding_Thumb2) /\
                               ~aligned_bx ((23 >< 16) opc)
                            else
                               ~aligned (opc,4))
                       ((read__reg ii RName_PC ||| read_reg ii n) >>=
                        (\(pc,rn).
                           address_mode2 ii indx add rn mode2 >>=
                           (\(offset_addr,address).
                             write___reg n
                               (if pc <> align (address,4) /\
                                  (enc <> Encoding_Thumb2 \/
                                   pc + 2w <> align (address,4))
                                then rn else rn + 4w)))) >>=
                       (\u:unit. constT (SOME T)))
             else
               constT NONE)
       | LoadStore (Load_Multiple indx add system _ n registers) =>
           (* load_write *)
           align_pc >>=
           (\u:unit.
             if n <> 15w /\ registers ' 15 then
               (condT system good_spsr_mode ||| arch_version ii) >>=
               (\(u:unit,version).
                  condT ((if version >= 5 then
                            ~aligned_bx opc \/
                            (enc = Encoding_Thumb2) /\
                            ~aligned_bx ((23 >< 16) opc)
                          else
                            ~aligned (opc,4)))
                    ((read__reg ii RName_PC ||| read_reg ii n) >>=
                     (\(pc,rn).
                        let count = n2w (4 * bit_count registers) in
                        let address = if add then rn else rn - count in
                        let address = if indx = add then address + 4w
                                                    else address in
                        let address = address + (count - 4w)
                        in
                          write___reg n
                            (if pc <> align (address,4) /\
                               (enc <> Encoding_Thumb2 \/
                                pc + 2w <> align (address,4))
                             then rn else rn + 4w))) >>=
                    (\u:unit. constT (SOME T)))
             else
               constT NONE)
       | LoadStore (Return_From_Exception P inc _ n) =>
           align_pc >>=
           (\u:unit.
             (read__reg ii RName_PC ||| read_reg ii n) >>=
             (\(pc,rn).
               let address = if inc then rn else rn - 8w in
               let address = if P = inc then address + 4w else address in
               let address = address + 4w
               in
                 write___reg n
                   (if pc <> align (address,4) /\
                       (enc <> Encoding_Thumb2 \/
                        pc + 2w <> align (address,4))
                    then rn else rn + 4w) >>=
                 (\u:unit. constT (SOME F))))
       | StatusAccess (Register_to_Status _ mask n) =>
           (align_pc ||| current_mode_is_priviledged ii) >>=
           (\(u:unit,priviledged).
              condT (mask ' 0 /\ priviledged /\ n <> 15w)
                (read_reg ii n >>=
                 (\rn.
                    write___reg n
                      (if GOOD_MODE ((4 >< 0) rn) then rn else rn || 31w))) >>=
              (\u:unit. constT NONE))
       | _ => align_pc >>= (\u:unit. constT NONE)`;

(* ------------------------------------------------------------------------- *)

val ARM_MEMORY_FOOTPRINT_def = Define`
  ARM_MEMORY_FOOTPRINT ii npass inst =
  let lookup_rname n =
        if n = 15w then
          constT RName_PC
        else
          read_cpsr ii >>= (\cpsr. LookUpRName ii (n,cpsr.M))
  in
  let write_address (r,a) =
        lookup_rname r >>=
        (\name. condT (name <> RName_PC) (write__reg ii name a))
  in
  let reg_align (r,a,n,rn) = write_address (r,align(rn + a,n) - a)
  and con_align (r,a,n,rn) = write_address (r,if aligned(a,n) then rn else 0w)
  in
  let align_mode2 (load,indx,add,byte,n,mode2) =
        (if load /\ is_mode2_immediate mode2 then
           read_reg_literal ii n
         else
           read_reg ii n) >>=
        (\rn.
           address_mode2 ii indx add rn mode2 >>=
           (\(offset_addr,address).
              if byte then
                constT NONE
              else
                case mode2
                  of Mode2_register _ _ m =>
                       if n = 15w then
                         read_reg ii m >>=
                         (\rm.
                            con_align (m, address, 4, rm) >>=
                            (\u.
                               address_mode2 ii indx add rn mode2 >>=
                               (\(offset_addr,address).
                                  constT (SOME (align (address,4))))))
                       else if n = m then
                         con_align (n, address, 4, rn) >>=
                         (\u.
                            read_reg ii n >>=
                            (\rn.
                               address_mode2 ii indx add rn mode2 >>=
                               (\(offset_addr,address).
                                  constT (SOME (align (address,4))))))
                       else
                         reg_align (n, address - rn, 4, rn) >>=
                         (\u:unit. constT (SOME (align (address,4))))
                   | _ =>
                       reg_align (n, address - rn, 4, rn) >>=
                       (\u:unit. constT (SOME (align (address,4))))))
  and align_mode3 (load,indx,add,N,B,n,mode3) =
        (if load /\ is_mode3_immediate mode3 then
           read_reg_literal ii n
         else
           read_reg ii n) >>=
        (\rn.
           address_mode3 ii indx add rn mode3 >>=
           (\(offset_addr,address).
              if N = 1 then
                constT NONE
              else
                case mode3
                  of Mode3_register _ m =>
                       if n = 15w then
                         read_reg ii m >>=
                         (\rm.
                            con_align (m, address, N, rm) >>=
                            (\u.
                               address_mode3 ii indx add rn mode3 >>=
                               (\(offset_addr,address). constT NONE)))
                       else if n = m then
                         con_align (n, address, N, rn) >>=
                         (\u.
                            read_reg ii n >>=
                            (\rn.
                               address_mode3 ii indx add rn mode3 >>=
                               (\(offset_addr,address). constT NONE)))
                       else
                         reg_align (n, address - rn, N, rn) >>=
                         (\u:unit. constT NONE)
                   | _ =>
                       reg_align (n, address - rn, N, rn) >>=
                       (\u:unit. constT NONE)))
  in
    if npass then constT NONE else
    case inst
    of Branch (Table_Branch_Byte n is_tbh m) =>
         (read_reg ii n ||| read_reg ii m) >>=
         (\(rn,rm).
            condT is_tbh (reg_align (n,LSL(rm,1),2,rn)) >>=
            (\u:unit. constT NONE))
     | Miscellaneous (Swap swap_byte n _ _) =>
         read_reg ii n >>=
         (\rn.
            condT (~swap_byte) (reg_align (n,0w,4,rn)) >>=
            (\u:unit. constT NONE))
     | LoadStore (Return_From_Exception P inc _ n) =>
         read_reg ii n >>=
         (\rn.
            let address = if inc then rn else rn - 8w in
            let address = if P = inc then address + 4w else address
            in
              reg_align (n, address - rn, 4, rn) >>=
              (\u:unit. constT (SOME (align (address,4) + 4w))))
     | LoadStore (Store_Return_State P inc _ mode) =>
         read_reg_mode ii (13w,mode) >>=
         (\rn.
            let address = if inc then rn else rn - 8w in
            let address = if P = inc then address + 4w else address
            in
              write_reg_mode ii (13w,mode)
                (align (address, 4) - (address - rn)) >>=
              (\u:unit. constT NONE))
     | LoadStore (Load indx add load_byte _ _ n _ mode2) =>
         align_mode2 (T,indx,add,load_byte,n,mode2)
     | LoadStore (Load_Halfword indx add _ _ load_half _ n _ mode3) =>
         align_mode3 (T,indx,add,if load_half then 2 else 1,2,n,mode3)
     | LoadStore (Load_Dual indx add _ n _ _ mode3) =>
         align_mode3 (T,indx,add,4,8,n,mode3)
     | LoadStore (Load_Multiple indx add _ _ n registers) =>
         read_reg ii n >>=
         (\rn.
            let count = 4 * bit_count registers in
            let base_address = if add then rn else rn - n2w count in
            let start_address = if indx = add then base_address + 4w
                                              else base_address
            in
              reg_align (n, start_address - rn, 4, rn) >>=
              (\u:unit.
                 constT (SOME (align (start_address,4) + n2w (count - 4)))))
     | LoadStore (Load_Exclusive n _ imm8) =>
         read_reg ii n >>=
         (\rn. reg_align (n, (w2w imm8) << 2, 4, rn) >>= (\u:unit. constT NONE))
     | LoadStore (Load_Exclusive_Doubleword n _ _) =>
         read_reg ii n >>=
         (\rn. reg_align (n,0w,8,rn) >>= (\u:unit. constT NONE))
     | LoadStore (Load_Exclusive_Halfword n _) =>
         read_reg ii n >>=
         (\rn. reg_align (n,0w,2,rn) >>= (\u:unit. constT NONE))
     | LoadStore (Load_Exclusive_Byte n _) =>
         read_reg ii n >>= (\rn. constT NONE)
     | LoadStore (Store indx add store_byte _ _ n _ mode2) =>
         align_mode2 (F,indx,add,store_byte,n,mode2)
     | LoadStore (Store_Halfword indx add _ _ n _ mode3) =>
         align_mode3 (F,indx,add,2,2,n,mode3)
     | LoadStore (Store_Dual indx add _ n _ _ mode3) =>
         align_mode3 (F,indx,add,4,8,n,mode3)
     | LoadStore (Store_Multiple indx add _ _ n registers) =>
         read_reg ii n >>=
         (\rn.
            let count = 4 * bit_count registers in
            let base_address = if add then rn else rn - n2w count in
            let start_address = if indx = add then base_address + 4w
                                              else base_address
            in
               reg_align (n, start_address - rn, 4, rn) >>=
               (\u:unit. constT NONE))
     | LoadStore (Store_Exclusive n _ _ imm8) =>
         read_reg ii n >>=
         (\rn.
            reg_align (n, (w2w imm8) << 2, 4, rn) >>=
            (\u:unit. constT NONE))
     | LoadStore (Store_Exclusive_Doubleword n _ _ _) =>
         read_reg ii n >>=
         (\rn. reg_align (n,0w,8,rn) >>= (\u:unit. constT NONE))
     | LoadStore (Store_Exclusive_Halfword n _ _) =>
         read_reg ii n >>=
         (\rn. reg_align (n,0w,2,rn) >>= (\u:unit. constT NONE))
     | LoadStore (Store_Exclusive_Byte n _ _) =>
         read_reg ii n >>= (\rn. constT NONE)
     | _ => constT NONE`;

(* ------------------------------------------------------------------------- *)

val arm_next_thm = Q.store_thm("arm_next_thm",
  `!s x P h g inp.
     (!s. P s ==> (g s = s)) /\
     (P s ==> (h (g s) = x)) /\
     (arm_next <| proc := 0 |> inp (g s) = ValueState () x) ==>
     (P s ==> (ARM_NEXT inp s = SOME (h s)))`,
  SRW_TAC [] [STATE_OPTION_def,ARM_NEXT_def]
    \\ `g s = s` by RES_TAC \\ POP_ASSUM SUBST_ALL_TAC
    \\ Cases_on `arm_next <|proc := 0|> inp s`
    \\ FULL_SIMP_TAC (srw_ss()) []);

val arm_next_thm2 = Q.store_thm("arm_next_thm2",
  `!s c x1 x2 P h1 h2 g inp.
     (!s. P s ==> (g s = s)) /\
     (P s ==> (h1 (g s) = x1)) /\
     (P s ==> (h2 (g s) = x2)) /\
     (arm_next <| proc := 0 |> inp (g s) =
       if c then ValueState () x1 else ValueState () x2) ==>
     (P s ==> (ARM_NEXT inp s = SOME (if c then h1 s else h2 s)))`,
  SRW_TAC [] [STATE_OPTION_def,ARM_NEXT_def]
    \\ `g s = s` by RES_TAC \\ POP_ASSUM SUBST_ALL_TAC
    \\ Cases_on `arm_next <|proc := 0|> inp s`
    \\ FULL_SIMP_TAC (srw_ss()) []);

(* ------------------------------------------------------------------------- *)

val _ = export_theory ();
