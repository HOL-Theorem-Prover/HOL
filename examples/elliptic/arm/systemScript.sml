(* ========================================================================= *)
(* FILE          : systemScript.sml                                          *)
(* DESCRIPTION   : Model of a basic ARM system, with upto 16 coprocessors    *)
(*                 plus main memory.                                         *)
(* AUTHOR        : Anthony Fox (with some contributions by Juliano Iyoda)    *)
(*                 University of Cambridge                                   *)
(* DATE          : 2005 - 2006                                               *)
(* ========================================================================= *)

(* interactive use: 
  app load ["wordsLib","wordsSyntax","armTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q wordsTheory rich_listTheory bsubstTheory;
open armTheory;

val _ = new_theory "system";

(* -------------------------------------------------------------------------- *)
(* In what follows, the term "cp" stands for "coprocessor".                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* We assume that there are up to 16 coprocessor with 16 registers each.      *)
(* The register word size can be different for each coprocessor               *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype `cp_register = cr0   | cr1   | cr2   | cr3
                                  | cr4   | cr5   | cr6   | cr7
                                  | cr8   | cr9   | cr10  | cr11
                                  | cr12  | cr13  | cr14  | cr15`;

val _ = type_abbrev("cp_registers",``:cp_register->'a word``);

val _ = Hol_datatype`
  all_cp_registers =
    <| p0_registers:'a0 cp_registers;
       p1_registers:'a1 cp_registers;
       p2_registers:'a2 cp_registers;
       p3_registers:'a3 cp_registers;
       p4_registers:'a4 cp_registers;
       p5_registers:'a5 cp_registers;
       p6_registers:'a6 cp_registers;
       p7_registers:'a7 cp_registers;
       p8_registers:'a8 cp_registers;
       p9_registers:'a9 cp_registers;
       p10_registers:'a10 cp_registers;
       p11_registers:'a11 cp_registers;
       p12_registers:'a12 cp_registers;
       p13_registers:'a13 cp_registers;
       p14_registers:'a14 cp_registers;
       p15_registers:32 cp_registers
    |>`;

(* -------------------------------------------------------------------------- *)
(* Memory + CP and bus output                                                 *)
(* -------------------------------------------------------------------------- *)

val _ = type_abbrev("mem", ``:word30->word32``);

val _ = Hol_datatype`
  cp_output = <| data : word32 option list; absent : bool |>`;

val _ = Hol_datatype`
  bus = <| data : word32 list; memory : mem; abort : num option;
           p15_registers : 32 cp_registers |>`;

(* -------------------------------------------------------------------------- *)
(* The system state                                                           *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype`
  arm_sys_state =
     <| registers : registers;
        psrs : psrs;
        memory : mem;
        undefined : bool;
        cp_registers : ('a0,'a1,'a2,'a3,'a4,'a5,'a6,'a7,
                        'a8,'a9,'a10,'a11,'a12,'a13,'a14) all_cp_registers
     |>`;

val Rg = inst [alpha |-> ``:32``,beta |-> ``:4``] wordsSyntax.word_extract_tm;

(* -------------------------------------------------------------------------- *)
(* The model is paramaterised by a collection of coprocessor operations       *)
(* i.e. sixteen mrc, mcr, stc, ldc and cdp functions:                         *)
(*                                                                            *)
(* absent : user_mode ireg => bool                                            *)
(*                                - controls which instructions are accepted  *)
(* f_mrc : user_mode regs Cop1 Cop2 CRn CRm => word32                         *)
(*                                - output for MRC instruction                *)
(* f_mcr : user_mode regs Cop1 Cop2 data CRm => regs                          *)
(*                                - operation for MCR instruction             *)
(* f_stc : user_mode regs N CRd => word32 option list                         *)
(*                                - output for STC instruction                *)
(* f_ldc : user_mode regs N CRd data => regs                                  *)
(*                                - operation for LDC instruction             *)
(* f_cdp : user_mode regs Cop1 Cop2 CRd CRn CRm => regs                       *)
(*                                - operation for CDP instruction             *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype `coproc_ops =
  <| absent:bool->word32->bool;
     f_mrc:bool->'a cp_registers->word3->word3->word4->word4->word32;
     f_mcr:bool->'a cp_registers->word3->word3-> word32->word4->'a cp_registers;
     f_stc:bool->'a cp_registers->bool->word4->word32 option list;
     f_ldc:bool->'a cp_registers->word4->bool->word32 list->'a cp_registers;
     f_cdp:bool->'a cp_registers->word4->word3->
           word4->word4->word4->'a cp_registers
  |>`;

val _ = Hol_datatype `all_coproc_ops =
  <| p0_ops : 'a0 coproc_ops;
     p1_ops : 'a1 coproc_ops;
     p2_ops : 'a2 coproc_ops;
     p3_ops : 'a3 coproc_ops;
     p4_ops : 'a4 coproc_ops;
     p5_ops : 'a5 coproc_ops;
     p6_ops : 'a6 coproc_ops;
     p7_ops : 'a7 coproc_ops;
     p8_ops : 'a8 coproc_ops;
     p9_ops : 'a9 coproc_ops;
     p10_ops : 'a10 coproc_ops;
     p11_ops : 'a11 coproc_ops;
     p12_ops : 'a12 coproc_ops;
     p13_ops : 'a13 coproc_ops;
     p14_ops : 'a14 coproc_ops;
     p15_ops : 32 coproc_ops
  |>`;

(* -------------------------------------------------------------------------- *)
(* REG_READ_CP and REG_WRITE_CP                                               *)
(* -------------------------------------------------------------------------- *)

val word2cp_register = Define`
  word2cp_register (n:word4) = num2cp_register (w2n n)`;

val CP_REG_READ_def = Define`
  CP_REG_READ (cp_registers:'a cp_registers) n =
    cp_registers (word2cp_register n)`;

val CP_REG_WRITE_def = Define`
  CP_REG_WRITE (cp_registers:'a cp_registers) n data =
    ((word2cp_register n :- data) cp_registers)`;

(* -------------------------------------------------------------------------- *)
(* DECODE_CDP                                                                 *)
(* -------------------------------------------------------------------------- *)

val DECODE_CDP_def = Define`
  DECODE_CDP (ireg:word32) =
    (^Rg 23 20 ireg,          (* Cop1 *)
     ^Rg 19 16 ireg,          (* CRn *)
     ^Rg 15 12 ireg,          (* CRd *)
     ((7 >< 5) ireg):word3, (* Cop2 *)
     ^Rg 03 00 ireg)`;        (* CRm *)

(* -------------------------------------------------------------------------- *)
(* DECODE_MRC_MCR                                                             *)
(* -------------------------------------------------------------------------- *)

val DECODE_MRC_MCR_def = Define`
  DECODE_MRC_MCR (ireg:word32) =
    (((23 >< 21) ireg):word3, (* Cop1 *)
     ^Rg 19 16 ireg,          (* CRn *)
     ((07 >< 05) ireg):word3, (* Cop2 *)
     ^Rg 03 00 ireg)`;        (* CRm *)

(* -------------------------------------------------------------------------- *)
(* DECODE_LDC_STC'                                                            *)
(* -------------------------------------------------------------------------- *)

val DECODE_LDC_STC'_def = Define`
  DECODE_LDC_STC' w =
    (w %% 22,               (* N *)
     ^Rg 15 12 w)`;         (* CRd *)

(* -------------------------------------------------------------------------- *)
(* CP                                                                         *)
(* Returns the coprocessor number from the instruction                        *)
(* -------------------------------------------------------------------------- *)

val CP_def = Define `CP (w:word32) = ((11 >< 8) w):word4`;

(* -------------------------------------------------------------------------- *)
(* DECODE_CP                                                                  *)
(* Determines the instruction class ** for a coprocessor instruction **       *)
(* -------------------------------------------------------------------------- *)

val DECODE_CP_def = Define`
  DECODE_CP (w:word32) =
    case ((26 >< 25) w):word3 of
       6w -> ldc_stc
    || 7w -> if ~(w %% 24) /\ w %% 4 then
               if w %% 20 then mrc else mcr
             else
               cdp_und
    || _ -> cdp_und`;

(* -------------------------------------------------------------------------- *)
(* MRC_OUT                                                                    *)
(* -------------------------------------------------------------------------- *)

val MRC_OUT_def = Define`
  MRC_OUT f_mrc (cp_registers:'a cp_registers) ireg user_mode =
    let (Cop1,CRn,Cop2,CRm) = DECODE_MRC_MCR ireg
    in
      [SOME (f_mrc user_mode cp_registers Cop1 Cop2 CRn CRm) ;
       NONE: word32 option]`;

(* -------------------------------------------------------------------------- *)
(* STC_OUT                                                                    *)
(* -------------------------------------------------------------------------- *)

val STC_OUT_def = Define`
  STC_OUT f_stc (cp_registers:'a cp_registers) ireg user_mode =
    let (N,CRd) = DECODE_LDC_STC' ireg
    in
      (f_stc user_mode cp_registers N CRd):word32 option list`;

(* -------------------------------------------------------------------------- *)
(* OUT_CPN                                                                    *)
(* Returns output from one coprocessor                                        *)
(* -------------------------------------------------------------------------- *)

val OUT_CPN_def = Define`
  OUT_CPN cp_ops cp_registers ireg user_mode =
    if cp_ops.absent user_mode ireg then
      <| data := []; absent := T |>
    else
      <| data :=
            case DECODE_CP ireg of
               mrc     -> MRC_OUT cp_ops.f_mrc cp_registers ireg user_mode
            || ldc_stc -> if ireg %% 20 then
                            []
                          else
                            STC_OUT cp_ops.f_stc cp_registers ireg user_mode
            || _ -> [];
         absent := F |>`;
                   
(* -------------------------------------------------------------------------- *)
(* OUT_CP                                                                     *)
(* It is assumed that only one coprocessor (i.e. "CP ireg") can accept the    *)
(* instruction but in general this need not be the case                       *)
(* -------------------------------------------------------------------------- *)

val OUT_CP_def = Define`
  OUT_CP cp_ops cp_state ireg arm_out =
    if arm_out.cpi then
      case CP ireg of
         0w  -> OUT_CPN cp_ops.p0_ops cp_state.p0_registers ireg arm_out.user
      || 1w  -> OUT_CPN cp_ops.p1_ops cp_state.p1_registers ireg arm_out.user
      || 2w  -> OUT_CPN cp_ops.p2_ops cp_state.p2_registers ireg arm_out.user
      || 3w  -> OUT_CPN cp_ops.p3_ops cp_state.p3_registers ireg arm_out.user
      || 4w  -> OUT_CPN cp_ops.p4_ops cp_state.p4_registers ireg arm_out.user
      || 5w  -> OUT_CPN cp_ops.p5_ops cp_state.p5_registers ireg arm_out.user
      || 6w  -> OUT_CPN cp_ops.p6_ops cp_state.p6_registers ireg arm_out.user
      || 7w  -> OUT_CPN cp_ops.p7_ops cp_state.p7_registers ireg arm_out.user
      || 8w  -> OUT_CPN cp_ops.p8_ops cp_state.p8_registers ireg arm_out.user
      || 9w  -> OUT_CPN cp_ops.p9_ops cp_state.p9_registers ireg arm_out.user
      || 10w -> OUT_CPN cp_ops.p10_ops cp_state.p10_registers ireg arm_out.user
      || 11w -> OUT_CPN cp_ops.p11_ops cp_state.p11_registers ireg arm_out.user
      || 12w -> OUT_CPN cp_ops.p12_ops cp_state.p12_registers ireg arm_out.user
      || 13w -> OUT_CPN cp_ops.p13_ops cp_state.p13_registers ireg arm_out.user
      || 14w -> OUT_CPN cp_ops.p14_ops cp_state.p14_registers ireg arm_out.user
      || _   -> OUT_CPN cp_ops.p15_ops cp_state.p15_registers ireg arm_out.user
    else <| data := []; absent := T |>`;


(* -------------------------------------------------------------------------- *)
(* MCR                                                                        *)
(* -------------------------------------------------------------------------- *)

val MCR_def = Define`
  MCR f_mcr (cp_registers:'a cp_registers) (data:word32 list) ireg user_mode =
    let (Cop1,CRn,Cop2,CRm) = DECODE_MRC_MCR ireg
    in
      f_mcr user_mode cp_registers Cop1 Cop2 (HD data) CRm`;

(* -------------------------------------------------------------------------- *)
(* LDC                                                                        *)
(* -------------------------------------------------------------------------- *)

val LDC_def = Define`
  LDC f_ldc (cp_registers:'a cp_registers) (data:word32 list) ireg user_mode =
    let (N,CRd) = DECODE_LDC_STC' ireg
    in
      f_ldc user_mode cp_registers CRd N data`;

(* -------------------------------------------------------------------------- *)
(* CDP                                                                        *)
(* -------------------------------------------------------------------------- *)

val CDP_def = Define`
  CDP f_cdp (cp_registers:'a cp_registers) ireg user_mode =
    let (Cop1,CRn,CRd,Cop2,CRm) = DECODE_CDP ireg
    in
      f_cdp user_mode cp_registers Cop1 Cop2 CRd CRn CRm`;

(* -------------------------------------------------------------------------- *)
(* RUN_CPN                                                                    *)
(* Updates state of one coprocessor                                           *)
(* -------------------------------------------------------------------------- *)

val RUN_CPN_def = Define`
  RUN_CPN cp_ops cp_registers data ireg user_mode =
    case DECODE_CP ireg of
       mcr     -> MCR cp_ops.f_mcr cp_registers data ireg user_mode
    || ldc_stc -> if ireg %% 20 then
                    LDC cp_ops.f_ldc cp_registers data ireg user_mode
                  else
                    cp_registers
    || cdp_und -> CDP cp_ops.f_cdp cp_registers ireg user_mode
    || _ -> cp_registers`;

(* -------------------------------------------------------------------------- *)
(* RUN_CP                                                                     *)
(* Takes a CP state and the input (word32 list) and returns the next state    *)
(* -------------------------------------------------------------------------- *)

val RUN_CP_def = Define`
  RUN_CP cp_ops cp_state absent data ireg arm_out =
    if arm_out.cpi /\ ~absent then
      case CP ireg of
         0w  -> cp_state with p0_registers :=
            RUN_CPN cp_ops.p0_ops cp_state.p0_registers data ireg arm_out.user
      || 1w  -> cp_state with p1_registers :=
            RUN_CPN cp_ops.p1_ops cp_state.p1_registers data ireg arm_out.user
      || 2w  -> cp_state with p2_registers :=
            RUN_CPN cp_ops.p2_ops cp_state.p2_registers data ireg arm_out.user
      || 3w  -> cp_state with p3_registers :=
            RUN_CPN cp_ops.p3_ops cp_state.p3_registers data ireg arm_out.user
      || 4w  -> cp_state with p4_registers :=
            RUN_CPN cp_ops.p4_ops cp_state.p4_registers data ireg arm_out.user
      || 5w  -> cp_state with p5_registers :=
            RUN_CPN cp_ops.p5_ops cp_state.p5_registers data ireg arm_out.user
      || 6w  -> cp_state with p6_registers :=
            RUN_CPN cp_ops.p6_ops cp_state.p6_registers data ireg arm_out.user
      || 7w  -> cp_state with p7_registers :=
            RUN_CPN cp_ops.p7_ops cp_state.p7_registers data ireg arm_out.user
      || 8w  -> cp_state with p8_registers :=
            RUN_CPN cp_ops.p8_ops cp_state.p8_registers data ireg arm_out.user
      || 9w  -> cp_state with p9_registers :=
            RUN_CPN cp_ops.p9_ops cp_state.p9_registers data ireg arm_out.user
      || 10w -> cp_state with p10_registers :=
            RUN_CPN cp_ops.p10_ops cp_state.p10_registers data ireg arm_out.user
      || 11w -> cp_state with p11_registers :=
            RUN_CPN cp_ops.p11_ops cp_state.p11_registers data ireg arm_out.user
      || 12w -> cp_state with p12_registers :=
            RUN_CPN cp_ops.p12_ops cp_state.p12_registers data ireg arm_out.user
      || 13w -> cp_state with p13_registers :=
            RUN_CPN cp_ops.p13_ops cp_state.p13_registers data ireg arm_out.user
      || 14w -> cp_state with p14_registers :=
            RUN_CPN cp_ops.p14_ops cp_state.p14_registers data ireg arm_out.user
      || _   -> cp_state with p15_registers :=
            RUN_CPN cp_ops.p15_ops cp_state.p15_registers data ireg arm_out.user
    else cp_state`;

(* -------------------------------------------------------------------------- *)
(* NEXT_ARM_SYS and STATE_ARM_SYS                                             *)
(* NB. Assumes that there are no prefetch aborts or hardware                  *)
(*     interrupts (fiq, irq)                                                  *)
(* -------------------------------------------------------------------------- *)

val ADDR30_def = Define `ADDR30 (addr:word32) = (31 >< 2) addr:word30`;

val NEXT_ARM_SYS_def = Define`
  NEXT_ARM_SYS bus_op (cp_ops: ('a0,'a1,'a2,'a3,'a4,'a5,'a6,'a7,
                         'a8,'a9,'a10,'a11,'a12,'a13,'a14) all_coproc_ops)
          state =
    let ireg = state.memory (ADDR30 (FETCH_PC state.registers)) in
    let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
               ireg := ireg;
               exception := if state.undefined then undefined else software |>
    in
    let arm_out = OUT_ARM s
    in
    let cp_out  = OUT_CP cp_ops state.cp_registers ireg arm_out
    in
    let bus = bus_op arm_out state.cp_registers.p15_registers
                      cp_out.data state.memory
    in
    let r = RUN_ARM s (if IS_SOME bus.abort then
                          SOME (THE bus.abort)
                       else
                          NONE)
                       bus.data cp_out.absent
    and p = RUN_CP cp_ops
                   (state.cp_registers with
                      p15_registers := bus.p15_registers)
                   cp_out.absent bus.data ireg arm_out
    in
      <| registers := r.reg; psrs := r.psr; memory := bus.memory;
         undefined := (~state.undefined /\ arm_out.cpi /\ cp_out.absent);
         cp_registers := p |>`;

val STATE_ARM_SYS_def = Define`
  (STATE_ARM_SYS bus_op co_ops 0 s = s) /\
  (STATE_ARM_SYS bus_op co_ops (SUC t) s =
    NEXT_ARM_SYS bus_op co_ops (STATE_ARM_SYS bus_op co_ops t s))`;

(* -------------------------------------------------------------------------- *)
(* An Idealistic Memory Model                                                 *)
(* -------------------------------------------------------------------------- *)

val SET_BYTE_def = Define`
  SET_BYTE (oareg:word2) (b:word8) (w:word32) =
    word_modify (\i x.
                  (i < 8) /\ (if oareg = 0w then b %% i else x) \/
       (8 <= i /\ i < 16) /\ (if oareg = 1w then b %% (i - 8) else x) \/
      (16 <= i /\ i < 24) /\ (if oareg = 2w then b %% (i - 16) else x) \/
      (24 <= i /\ i < 32) /\ (if oareg = 3w then b %% (i - 24) else x)) w`;

val SET_HALF_def = Define`
  SET_HALF (oareg:bool) (hw:word16) (w:word32) =
    word_modify (\i x.
                 (i < 16) /\ (if ~oareg then hw %% i else x) \/
      (16 <= i /\ i < 32) /\ (if oareg then hw %% (i - 16) else x)) w`;

val MEM_WRITE_BYTE_def = Define`
  MEM_WRITE_BYTE (mem:mem) addr (word:word8) =
    let addr30 = ADDR30 addr in
      (addr30 :- SET_BYTE ((1 >< 0) addr) word (mem addr30)) mem`;

val MEM_WRITE_HALF_def = Define`
  MEM_WRITE_HALF (mem:mem) addr (word:word16) =
    let addr30 = ADDR30 addr in
      (addr30 :- SET_HALF (addr %% 1) word (mem addr30)) mem`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD (mem:mem) addr word = (ADDR30 addr :- word) mem`;

val MEM_WRITE_def = Define`
  MEM_WRITE mem addr d =
    case d of
       Byte b  -> MEM_WRITE_BYTE mem addr b
    || Half hw -> MEM_WRITE_HALF mem addr hw
    || Word w  -> MEM_WRITE_WORD mem addr w`;

val TRANSFER_def = Define`
  TRANSFER cpi (cp_data,data,mem) t =
    case t of
       MemRead a ->
         if cpi then
           let (f, b) = SPLITP IS_SOME cp_data in
             (b, data ++
                MAP (\addr. mem (ADDR30 addr)) (ADDRESS_LIST a (LENGTH f)), mem)
         else
           (cp_data, data ++ [mem (ADDR30 a)], mem)
    || MemWrite a d ->
         if cpi then
           let (f, b) = SPLITP IS_NONE cp_data in
             (b, data,
                FOLDL (\m (addr,cpd). MEM_WRITE mem addr (Word (THE cpd)))
                  mem (ZIP (ADDRESS_LIST a (LENGTH f), f)))
         else
            (cp_data, data, MEM_WRITE mem a d)
    || CPWrite w ->
         (cp_data, if cpi then data ++ [w] else data, mem)`;

val TRANSFERS_def = Define`
  TRANSFERS arm_out p15_regs cp_data mem =
    let (data, mem) = 
      if arm_out.cpi /\ NULL arm_out.transfers then
        (MAP THE cp_data, mem)
      else
        SND (FOLDL (TRANSFER arm_out.cpi) (cp_data, [], mem) arm_out.transfers)
    in
      <| data := data; memory := mem;
         abort := NONE; p15_registers := p15_regs |>`;

(* -------------------------------------------------------------------------- *)
(* NEXT_ARM_MEM and STATE_ARM_MEM                                             *)
(* -------------------------------------------------------------------------- *)

val NO_CP_OPS_def = Define`
  NO_CP_OPS = <|
    p0_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p1_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p2_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p3_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p4_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p5_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p6_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p7_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p8_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p9_ops  := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p10_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p11_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p12_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p13_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p14_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>;
    p15_ops := <| absent := \u i. T; f_mrc := ARB; f_mcr := ARB;
                   f_stc := ARB; f_ldc := ARB; f_cdp := ARB |>
  |>`;

val OUT_CP_NO_CPS =
  SIMP_CONV (srw_ss()) [OUT_CP_def,OUT_CPN_def,NO_CP_OPS_def,bool_case_EQ_COND]
  ``OUT_CP NO_CP_OPS cp_state ireg arm_out``;

val RUN_CP_NO_CPS = SIMP_CONV (srw_ss()) [RUN_CP_def,NO_CP_OPS_def]
  ``RUN_CP NO_CP_OPS cp_state T data ireg arm_out``;

val NEXT_ARM_MEM_def = Define `NEXT_ARM_MEM = NEXT_ARM_SYS TRANSFERS NO_CP_OPS`;

val STATE_ARM_MEM_def = Define`
  (STATE_ARM_MEM 0 s = s) /\
  (STATE_ARM_MEM (SUC t) s = NEXT_ARM_MEM (STATE_ARM_MEM t s))`;

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val TRANSFERS = prove(
  `(!arm_out p15_reg data mem.
        (TRANSFERS arm_out p15_reg data mem).abort = NONE) /\
   (!arm_out p15_reg data mem.
        (TRANSFERS arm_out p15_reg data mem).p15_registers = p15_reg)`,
  SRW_TAC [] [TRANSFERS_def] \\ FULL_SIMP_TAC (srw_ss()) []);

val NEXT_ARM_MEM = store_thm("NEXT_ARM_MEM",
  `NEXT_ARM_MEM state =
     let ireg = state.memory (ADDR30 (FETCH_PC state.registers)) in
     let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
                ireg := ireg;
                exception := if state.undefined then undefined else software |>
     in
     let arm_out = OUT_ARM s in
     let mmu_out = TRANSFERS arm_out state.cp_registers.p15_registers []
                             state.memory
     in
     let r = RUN_ARM s NONE mmu_out.data T
     in
       <| registers := r.reg; psrs := r.psr; memory := mmu_out.memory;
          undefined := (~state.undefined /\ arm_out.cpi);
          cp_registers := state.cp_registers |>`,
  SRW_TAC [boolSimps.LET_ss]
    [NEXT_ARM_SYS_def,NEXT_ARM_MEM_def,RUN_CP_NO_CPS,OUT_CP_NO_CPS,TRANSFERS]
    \\ Cases_on `state.cp_registers`
    \\ SIMP_TAC (srw_ss()) [definition "all_cp_registers_p15_registers_fupd"]);

(* ------------------------------------------------------------------------- *)
(* Export ML versions of functions                                           *)
(*---------------------------------------------------------------------------*)

val mem_read_def        = Define`mem_read (m: mem, a) = m a`;
val mem_write_def       = Define`mem_write (m:mem) a d = (a :- d) m`;
val mem_write_block_def = Define`mem_write_block (m:mem) a cr = (a ::- cr) m`;
val mem_items_def       = Define`mem_items (m:mem) = []:(word30 # word32) list`;
val empty_memory_def    = Define`empty_memory = (\a. 0xE6000010w):mem`;
val empty_registers_def = Define`empty_registers = (\n. 0w):registers`;
val empty_psrs_def      = Define`empty_psrs = (\x. SET_IFMODE F F usr 0w):psrs`;

val empty_cp_registers_def = Define`
  empty_cp_registers = (\n. 0w):one cp_registers`;

val empty_all_cp_registers_def = Define`
  empty_all_cp_registers =
    <| p0_registers := empty_cp_registers;
       p1_registers := empty_cp_registers;
       p2_registers := empty_cp_registers;
       p3_registers := empty_cp_registers;
       p4_registers := empty_cp_registers;
       p5_registers := empty_cp_registers;
       p6_registers := empty_cp_registers;
       p7_registers := empty_cp_registers;
       p8_registers := empty_cp_registers;
       p9_registers := empty_cp_registers;
       p10_registers := empty_cp_registers;
       p11_registers := empty_cp_registers;
       p12_registers := empty_cp_registers;
       p13_registers := empty_cp_registers;
       p14_registers := empty_cp_registers;
       p15_registers := (\n. 0w)
    |>`;

(* ------------------------------------------------------------------------- *)

open arithmeticTheory numeralTheory bitTheory;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val word_ss = arith_ss++fcpLib.FCP_ss++wordsLib.SIZES_ss++
  rewrites [n2w_def,word_extract_def,word_bits_n2w,w2w,
    BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
    DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def]

val MOD_DIMINDEX_32 = (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
   Thm.INST_TYPE [alpha |-> ``:32``]) MOD_DIMINDEX;

val DECODE_TAC = SIMP_TAC std_ss [DECODE_PSR_def,DECODE_BRANCH_def,
      DECODE_DATAP_def,DECODE_MRS_def,DECODE_MSR_def,DECODE_LDR_STR_def,
      DECODE_LDRH_STRH_def,DECODE_MLA_MUL_def,DECODE_LDM_STM_def,
      DECODE_SWP_def,DECODE_LDC_STC_def,SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,
      CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV rich_listTheory.GENLIST,
      NZCV_def,REGISTER_LIST_def,rich_listTheory.SNOC,word_extract_def]
 \\ SIMP_TAC word_ss [];

val DECODE_PSR_THM = store_thm("DECODE_PSR_THM",
  `!n.  DECODE_PSR (n2w n) =
     let (q0,m) = DIVMOD_2EXP 5 n in
     let (q1,i) = DIVMOD_2EXP 1 (DIV2 q0) in
     let (q2,f) = DIVMOD_2EXP 1 q1 in
     let (q3,V) = DIVMOD_2EXP 1 (DIV_2EXP 20 q2) in
     let (q4,C) = DIVMOD_2EXP 1 q3 in
     let (q5,Z) = DIVMOD_2EXP 1 q4 in
       ((ODD q5,Z=1,C=1,V=1),f = 1,i = 1,n2w m)`, DECODE_TAC);

val DECODE_BRANCH_THM = store_thm("DECODE_BRANCH_THM",
  `!n. DECODE_BRANCH (n2w n) =
         let (L,offset) = DIVMOD_2EXP 24 n in (ODD L,n2w offset)`, DECODE_TAC);

val DECODE_DATAP_THM = store_thm("DECODE_DATAP_THM",
  `!n. DECODE_DATAP (n2w n) =
     let (q0,opnd2) = DIVMOD_2EXP 12 n in
     let (q1,Rd) = DIVMOD_2EXP 4 q0 in
     let (q2,Rn) = DIVMOD_2EXP 4 q1 in
     let (q3,S) = DIVMOD_2EXP 1 q2 in
     let (q4,opcode) = DIVMOD_2EXP 4 q3 in
       (ODD q4,n2w opcode,S = 1,n2w Rn,n2w Rd,n2w opnd2)`, DECODE_TAC);

val DECODE_MRS_THM = store_thm("DECODE_MRS_THM",
  `!n. DECODE_MRS (n2w n) =
     let (q,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 12 n) in
      (ODD (DIV_2EXP 6 q),n2w Rd)`, DECODE_TAC);

val DECODE_MSR_THM = store_thm("DECODE_MSR_THM",
  `!n. DECODE_MSR (n2w n) =
     let (q0,opnd) = DIVMOD_2EXP 12 n in
     let (q1,bit16) = DIVMOD_2EXP 1 (DIV_2EXP 4 q0) in
     let (q2,bit19) = DIVMOD_2EXP 1 (DIV_2EXP 2 q1) in
     let (q3,R) = DIVMOD_2EXP 1 (DIV_2EXP 2 q2) in
       (ODD (DIV_2EXP 2 q3),R = 1,bit19 = 1,bit16 = 1,
        n2w (MOD_2EXP 4 opnd),n2w opnd)`,
  DECODE_TAC \\ `4096 = 16 * 256` by numLib.ARITH_TAC
    \\ ASM_REWRITE_TAC [] \\ SIMP_TAC arith_ss [MOD_MULT_MOD]);

val DECODE_LDR_STR_THM = store_thm("DECODE_LDR_STR_THM",
  `!n. DECODE_LDR_STR (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 12 n in
    let (q1,Rd) = DIVMOD_2EXP 4 q0 in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,L) = DIVMOD_2EXP 1 q2 in
    let (q4,W) = DIVMOD_2EXP 1 q3 in
    let (q5,B) = DIVMOD_2EXP 1 q4 in
    let (q6,U) = DIVMOD_2EXP 1 q5 in
    let (q7,P) = DIVMOD_2EXP 1 q6 in
      (ODD q7,P = 1,U = 1,B = 1,W = 1,L = 1,n2w Rn,n2w Rd,n2w offset)`,
   DECODE_TAC);

val DECODE_LDRH_STRH_THM = store_thm("DECODE_LDRH_STRH_THM",
  `!n. DECODE_LDRH_STRH (n2w n) =
    let (q0,offsetL) = DIVMOD_2EXP 4 n in
    let (q1,H) = DIVMOD_2EXP 1 (DIV2 q0) in
    let (q2,S) = DIVMOD_2EXP 1 q1 in
    let (q3,offsetH) = DIVMOD_2EXP 4 (DIV2 q2) in
    let (q4,Rd) = DIVMOD_2EXP 4 q3 in
    let (q5,Rn) = DIVMOD_2EXP 4 q4 in
    let (q6,L) = DIVMOD_2EXP 1 q5 in
    let (q7,W) = DIVMOD_2EXP 1 q6 in
    let (q8,I) = DIVMOD_2EXP 1 q7 in
    let (q9,U) = DIVMOD_2EXP 1 q8 in
      (ODD q9,U = 1,I = 1,W = 1,L = 1,n2w Rn,n2w Rd,
       n2w offsetH,S = 1,H = 1,n2w offsetL)`,
   DECODE_TAC);

val DECODE_MLA_MUL_THM = store_thm("DECODE_MLA_MUL_THM",
  `!n. DECODE_MLA_MUL (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rs) = DIVMOD_2EXP 4 (DIV_2EXP 4 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
    let (q3,Rd) = DIVMOD_2EXP 4 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,A) = DIVMOD_2EXP 1 q4 in
    let (q6,Sgn) = DIVMOD_2EXP 1 q5 in
      (ODD q6,Sgn = 1,A = 1,S = 1,n2w Rd,n2w Rn,n2w Rs,n2w Rm)`, DECODE_TAC);

val DECODE_LDM_STM_THM = store_thm("DECODE_LDM_STM_THM",
  `!n. DECODE_LDM_STM (n2w n) =
    let (q0,list) = DIVMOD_2EXP 16 n in
    let (q1,Rn) = DIVMOD_2EXP 4 q0 in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,S) = DIVMOD_2EXP 1 q3 in
    let (q5,U) = DIVMOD_2EXP 1 q4 in
      (ODD q5, U = 1, S = 1, W = 1, L = 1,n2w Rn,n2w list)`, DECODE_TAC);

val DECODE_SWP_THM = store_thm("DECODE_SWP_THM",
  `!n. DECODE_SWP (n2w n) =
    let (q0,Rm) = DIVMOD_2EXP 4 n in
    let (q1,Rd) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,Rn) = DIVMOD_2EXP 4 q1 in
      (ODD (DIV_2EXP 2 q2),n2w Rn,n2w Rd,n2w Rm)`, DECODE_TAC);

val DECODE_LDC_STC_THM = store_thm("DECODE_LDC_STC_THM",
  `!n. DECODE_LDC_STC (n2w n) =
    let (q0,offset) = DIVMOD_2EXP 8 n in
    let (q1,Rn) = DIVMOD_2EXP 4 (DIV_2EXP 8 q0) in
    let (q2,L) = DIVMOD_2EXP 1 q1 in
    let (q3,W) = DIVMOD_2EXP 1 q2 in
    let (q4,U) = DIVMOD_2EXP 1 (DIV2 q3) in
      (ODD q4,U = 1,W = 1,L = 1,n2w Rn,n2w offset)`, DECODE_TAC);

(* ------------------------------------------------------------------------- *)

fun w2w_n2w_sizes a b = (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [] o
  Thm.INST_TYPE [alpha |-> a, beta |-> b]) w2w_n2w;

val SHIFT_IMMEDIATE_THM = store_thm("SHIFT_IMMEDIATE_THM",
  `!reg mode C opnd2.
     SHIFT_IMMEDIATE reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let shift = MOD_2EXP 5 q1 in
       let rm = REG_READ reg mode (n2w Rm) in
         SHIFT_IMMEDIATE2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:12``) [``:8``, ``:4``, ``:2``])
    \\ DECODE_TAC);

val SHIFT_REGISTER_THM = store_thm("SHIFT_REGISTER_THM",
  `!reg mode C opnd2.
     SHIFT_REGISTER reg mode C (n2w opnd2) =
       let (q0,Rm) = DIVMOD_2EXP 4 opnd2 in
       let (q1,Sh) = DIVMOD_2EXP 2 (DIV2 q0) in
       let Rs = MOD_2EXP 4 (DIV2 q1) in
       let shift = MOD_2EXP 8 (w2n (REG_READ reg mode (n2w Rs)))
       and rm = REG_READ (INC_PC reg) mode (n2w Rm) in
         SHIFT_REGISTER2 (n2w shift) (n2w Sh) rm C`,
  ONCE_REWRITE_TAC [w2w_n2w_sizes ``:32`` ``:8``]
    \\ ONCE_REWRITE_TAC (map (w2w_n2w_sizes ``:12``) [``:8``, ``:4``, ``:2``])
    \\ SIMP_TAC std_ss [SHIFT_REGISTER_def,word_extract_def,
         (GSYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [n2w_w2n,BITS_THM,DIV_1,
            (GSYM o SIMP_RULE std_ss [] o SPEC `8`) MOD_2EXP_def] o
          SPECL [`7`,`0`,`w2n (a:word32)`] o
          Thm.INST_TYPE [alpha |-> ``:32``]) word_bits_n2w]
    \\ SIMP_TAC word_ss []);

(* ------------------------------------------------------------------------- *)

val REGISTER_LIST_THM = store_thm("REGISTER_LIST_THM",
  `!n. REGISTER_LIST (n2w n) =
       let (q0,b0) = DIVMOD_2EXP 1 n in
       let (q1,b1) = DIVMOD_2EXP 1 q0 in
       let (q2,b2) = DIVMOD_2EXP 1 q1 in
       let (q3,b3) = DIVMOD_2EXP 1 q2 in
       let (q4,b4) = DIVMOD_2EXP 1 q3 in
       let (q5,b5) = DIVMOD_2EXP 1 q4 in
       let (q6,b6) = DIVMOD_2EXP 1 q5 in
       let (q7,b7) = DIVMOD_2EXP 1 q6 in
       let (q8,b8) = DIVMOD_2EXP 1 q7 in
       let (q9,b9) = DIVMOD_2EXP 1 q8 in
       let (q10,b10) = DIVMOD_2EXP 1 q9 in
       let (q11,b11) = DIVMOD_2EXP 1 q10 in
       let (q12,b12) = DIVMOD_2EXP 1 q11 in
       let (q13,b13) = DIVMOD_2EXP 1 q12 in
       let (q14,b14) = DIVMOD_2EXP 1 q13 in
       MAP SND (FILTER FST
         [(b0 = 1,0w); (b1 = 1,1w); (b2 = 1,2w); (b3 = 1,3w);
          (b4 = 1,4w); (b5 = 1,5w); (b6 = 1,6w); (b7 = 1,7w);
          (b8 = 1,8w); (b9 = 1,9w); (b10 = 1,10w); (b11 = 1,11w);
          (b12 = 1,12w); (b13 = 1,13w); (b14 = 1,14w); (ODD q14,15w)])`,
  DECODE_TAC);

(* ------------------------------------------------------------------------- *)

val DECODE_ARM_THM = store_thm("DECODE_ARM_THM",
  `!ireg. DECODE_ARM (ireg : word32) =
    let b n = ireg %% n in
      if b 27 then
        if b 26 then
          if b 25 then
            if b 24 then (* (T,T,T,T,...) *)
              swi_ex
            else (* (T,T,T,F,...) *)
              if b 4 then
                if b 20 then mrc else mcr
              else
                cdp_und
          else (* (T,T,F,...) *)
            ldc_stc
        else (* (T,F,...) *)
          if b 25 then br else ldm_stm
      else
         if b 26 then (* (F,T,...) *)
           if b 25 then
             if b 4 then cdp_und else ldr_str
           else
             ldr_str
         else
           if b 25 then (* (F,F,T,...) *)
             if b 24 /\ ~b 23 /\ ~b 20 then
               if b 21 then
                 msr
               else
                 cdp_und
             else
               data_proc
           else
             if b 24 then (* (F,F,F,T,...) *)
               if b 7 then
                 if b 4 then
                   if b 20 then
                     if b 6 then
                       ldrh_strh
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 6 then
                       cdp_und
                     else
                       if b 5 then
                         ldrh_strh
                       else
                         if ~b 23 /\ ~b 21 then
                           swp
                         else
                           cdp_und
                 else
                   data_proc
               else
                 if b 4 then
                   data_proc
                 else
                   if ~b 23 /\ ~b 20 /\ ~b 6 /\ ~b 5 then
                     if b 21 then msr else mrs
                   else
                     data_proc
             else (* (F,F,F,F,...) *)
               if b 7 then
                 if b 4 then
                   if b 6 \/ b 5 then
                     if b 20 /\ b 6 then
                       ldrh_strh
                     else
                       if ~b 6 /\ b 5 then
                         ldrh_strh
                       else
                         cdp_und
                   else
                     if b 23 \/ ~b 22 then mla_mul else cdp_und
                 else
                   data_proc
               else
                 if b 4 then data_proc else data_proc`,
  SRW_TAC [boolSimps.LET_ss] [DECODE_ARM_def]
    \\ FULL_SIMP_TAC (srw_ss()) [bool_case_ID]);

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

(*---------------------------------------------------------------------------*)

val LDR_STR_OUT = prove(
  `!r C mode ireg.
    (LDR_STR r C mode ARB ARB ireg).out =
      (let (I,P,U,B,W,L,Rn,Rd,offset) = DECODE_LDR_STR ireg in
       let (addr,wb_addr) = ADDR_MODE2 r.reg mode C I P U Rn offset in
       let pc_reg = INC_PC r.reg
       in
         [(if L then
             MemRead addr
           else
             let w = REG_READ pc_reg mode Rd in
               MemWrite addr (if B then Byte ((7 >< 0) w) else Word w))])`,
  SRW_TAC [boolSimps.LET_ss] [LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def]);

val LDRH_STRH_OUT = prove(
  `!r C mode ireg.
    (LDRH_STRH r mode ARB ARB ireg).out =
      (let (P,U,I,W,L,Rn,Rd,offsetH,S,H,offsetL) = DECODE_LDRH_STRH ireg in
       let (addr,wb_addr) = ADDR_MODE3 r.reg mode I P U Rn offsetH offsetL in
       let pc_reg = INC_PC r.reg
       in
         [(if L then
             MemRead addr
           else
             MemWrite addr (Half ((15 >< 0) (REG_READ pc_reg mode Rd))))])`,
  SRW_TAC [boolSimps.LET_ss]
    [LDRH_STRH_def,DECODE_LDRH_STRH_def,ADDR_MODE3_def]);

val LDM_STM_OUT = prove(
   `!r mode ireg.
     (LDM_STM r mode ARB ARB ireg).out =
       (let (P,U,S,W,L,Rn,list) = DECODE_LDM_STM ireg in
        let pc_in_list = list %% 15 and rn = REG_READ r.reg mode Rn in
        let (rp_list,addr_list,rn') = ADDR_MODE4 P U rn list and
            mode' = (if S /\ (L ==> ~pc_in_list) then usr else mode) and
            pc_reg = INC_PC r.reg
        in
        let wb_reg =
              (if W /\ ~(Rn = 15w) then
                 REG_WRITE pc_reg (if L then mode else mode') Rn rn'
               else
                 pc_reg)
        in
          (if L then
             MAP MemRead addr_list
           else
             STM_LIST (if HD rp_list = Rn then pc_reg else wb_reg)
               mode' (ZIP (rp_list,addr_list))))`,
  SRW_TAC [boolSimps.LET_ss] [LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def]);

val SWP_OUT = prove(
  `!r mode ireg.
    (SWP r mode ARB ARB ireg).out =
       (let (B,Rn,Rd,Rm) = DECODE_SWP ireg in
        let rn = REG_READ r.reg mode Rn and pc_reg = INC_PC r.reg in
        let rm = REG_READ pc_reg mode Rm in
          [MemRead rn;
           MemWrite rn (if B then Byte ((7 >< 0) rm) else Word rm)])`,
  SRW_TAC [boolSimps.LET_ss] [SWP_def,DECODE_SWP_def]);

val OUT_ARM =
   REWRITE_RULE [LDR_STR_OUT,LDRH_STRH_OUT,LDM_STM_OUT,SWP_OUT] OUT_ARM_def;

(*---------------------------------------------------------------------------*)

val register_decl = `register =
 r0     | r1     | r2      | r3      | r4      | r5      | r6      | r7  |
 r8     | r9     | r10     | r11     | r12     | r13     | r14     | r15 |
 r8_fiq | r9_fiq | r10_fiq | r11_fiq | r12_fiq | r13_fiq | r14_fiq |
                                                 r13_irq | r14_irq |
                                                 r13_svc | r14_svc |
                                                 r13_abt | r14_abt |
                                                 r13_und | r14_und`;

val cp_register_decl = `cp_register =
   cr0 | cr1 | cr2  | cr3  | cr4  | cr5  | cr6  | cr7 |
   cr8 | cr9 | cr10 | cr11 | cr12 | cr13 | cr14 | cr15`;

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

val RHS_REWRITE_RULE =
  GEN_REWRITE_RULE (DEPTH_CONV o RAND_CONV) empty_rewrites;

val n2w_w2n_rule = GEN_ALL o SIMP_RULE bool_ss [wordsTheory.n2w_w2n];

val spec_word_rule16 = n2w_w2n_rule o Q.SPEC `w2n (w:word16)`;
val spec_word_rule32 = n2w_w2n_rule o Q.SPEC `w2n (w:word32)`;

val spec_word_rule12 =
  n2w_w2n_rule o INST [`opnd2` |-> `w2n (w:word12)`] o SPEC_ALL;

val mem_read_rule = ONCE_REWRITE_RULE [GSYM mem_read_def];

val _ = ConstMapML.insert ``dimword``;
val _ = ConstMapML.insert ``dimindex``;
val _ = ConstMapML.insert ``INT_MIN``;
val _ = ConstMapML.insert ``n2w_itself``;

fun mk_word n =
  let val s = Int.toString n
      val w = "type word" ^ s ^ " = wordsML.word" ^ s
  in
    EmitML.MLSIG w
  end;

val defs_rule =
  BETA_RULE o PURE_REWRITE_RULE
    [GSYM n2w_itself_def, GSYM w2w_itself_def, GSYM sw2sw_itself_def,
     GSYM word_concat_itself_def, GSYM word_extract_itself_def,
     GSYM mem_write_def, literal_case_THM] o
  RHS_REWRITE_RULE [GSYM word_eq_def];

val _ = let open EmitML in emitML (!Globals.emitMLDir)
    ("bsubst", OPEN ["num", "fcp", "words"]
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
         :: DATATYPE (`data = Byte of word8 | Half of word16 | Word of word32`)
         :: map DEFN
              [SUBST_def, BSUBST_def, mem_read_def,
               mem_write_def, mem_write_block_def]
          @ map (DEFN o defs_rule o ONCE_REWRITE_RULE [GSYM mem_read_def])
              [empty_memory_def, mem_items_def, ADDR30_def, GET_HALF_def,
               SIMP_RULE std_ss [literal_case_DEF] GET_BYTE_def,
               FORMAT_def, SET_BYTE_def, SET_HALF_def,
               MEM_WRITE_BYTE_def, MEM_WRITE_HALF_def,
               MEM_WRITE_WORD_def, MEM_WRITE_def])
end;

val _ = temp_type_abbrev("cp_registers32",``:32 cp_registers``);

val _ = let open EmitML in emitML (!Globals.emitMLDir) ("arm",
  OPEN ["num", "option", "set", "fcp", "list", "rich_list", "bit", "words"]
    :: MLSIG "type 'a word = 'a wordsML.word"
    :: MLSIG "type num = numML.num"
    :: map (fn decl => DATATYPE decl) [register_decl, cp_register_decl,
                                       psr_decl, mode_decl, condition_decl]
     @ map (fn decl => EQDATATYPE ([], decl)) [exceptions_decl,iclass_decl]
     @ ABSDATATYPE (["'a","'b"],`state_inp = <| state : 'a; inp : num -> 'b |>`)
    :: ABSDATATYPE (["'a","'b"],`state_out = <| state : 'a; out : 'b |>`)
    :: map mk_word [2,4,5,8,12,16,24,30,32]
     @ MLSTRUCT "type registers = register->word32"
    :: MLSTRUCT "type 'a cp_registers = cp_register->'a word"
    :: MLSTRUCT "type cp_registers32 = cp_register-> word32"
    :: MLSTRUCT "type psrs = psr->word32"
    :: MLSTRUCT "type mem = bsubstML.mem"
    :: MLSTRUCT "type data = bsubstML.data"
    :: MLSIG "type registers = register->word32"
    :: MLSIG "type 'a cp_registers = cp_register->'a word"
    :: MLSIG "type cp_registers32 = cp_register-> word32"
    :: MLSIG "type psrs = psr->word32"
    :: MLSIG "type mem = bsubstML.mem"
    :: MLSIG "type data = bsubstML.data"
    :: DATATYPE (`all_cp_registers = <|
            p0_registers:'a0 cp_registers; p1_registers:'a1 cp_registers;
            p2_registers:'a2 cp_registers; p3_registers:'a3 cp_registers;
            p4_registers:'a4 cp_registers; p5_registers:'a5 cp_registers;
            p6_registers:'a6 cp_registers; p7_registers:'a7 cp_registers;
            p8_registers:'a8 cp_registers; p9_registers:'a9 cp_registers;
            p10_registers:'a10 cp_registers; p11_registers:'a11 cp_registers;
            p12_registers:'a12 cp_registers; p13_registers:'a13 cp_registers;
            p14_registers:'a14 cp_registers; p15_registers:32 cp_registers
          |>`)
    :: DATATYPE (`regs = <| reg : registers; psr : psrs |>`)
    :: DATATYPE (`memop = MemRead of word32 | MemWrite of word32=>data |
                          CPWrite of word32`)
    :: DATATYPE (`arm_state = <| regs : regs; ireg : word32;
                                 exception : exceptions |>`)
    :: DATATYPE (`arm_output = <| transfers : memop list;
                                  cpi : bool; user : bool |>`)
    :: DATATYPE (`cp_output = <| data : word32 option list; absent : bool |>`)
    :: DATATYPE (`bus = <| data : word32 list; memory : mem; abort : num option;
                           p15_registers : 32 cp_registers |>`)
    :: DATATYPE (`arm_sys_state = <| registers : registers; psrs : psrs;
            memory : mem; undefined : bool;
            cp_registers : ('a0,'a1,'a2,'a3,'a4,'a5,'a6,'a7, 'a8,'a9,
                            'a10,'a11,'a12,'a13,'a14) all_cp_registers |>`)
    :: DATATYPE (`interrupt = Reset of regs | Undef | Prefetch |
                              Dabort of num | Fiq | Irq`)
    :: DATATYPE (`arm_input = <| ireg : word32; data : word32 list;
                                 interrupt : interrupt option; no_cp : bool |>`)
    :: MLSTRUCT "val mem_updates = ref ([]: word30 list)"
    :: MLSIG "val mem_updates : word30 list ref"
    :: map (DEFN o defs_rule) (map spec_word_rule32
         [DECODE_PSR_THM, DECODE_BRANCH_THM, DECODE_DATAP_THM,
          DECODE_MRS_THM, DECODE_MSR_THM, DECODE_LDR_STR_THM,
           DECODE_MLA_MUL_THM, DECODE_LDM_STM_THM, DECODE_SWP_THM,
           DECODE_LDC_STC_THM, DECODE_LDRH_STRH_THM]
       @ [USER_def, mode_reg2num_def, DECODE_ARM_def, mode_num_def,
          state_out_state, state_out_out, exceptions2num_thm, register2num_thm,
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
          SPEC `f` ALU_arith_def, SPEC `f` ALU_arith_neg_def, ALU_logic_def,
          numLib.REDUCE_RULE SUB_def, ADD_def, AND_def, EOR_def, ORR_def,
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
          OUT_ARM, mem_read_rule TRANSFER_def, TRANSFERS_def,
          mem_read_rule NEXT_ARM_MEM, empty_registers_def,
          empty_cp_registers_def, empty_all_cp_registers_def]))
 end;

(* -------------------------------------------------------------------------- *)

val _ = export_theory();
