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

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;

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

val _ = export_theory ();
