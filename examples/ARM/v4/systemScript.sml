(* ========================================================================= *)
(* FILE          : systemScript.sml                                          *)
(* DESCRIPTION   : Model of a basic ARM system, with upto 16 coprocessors    *)
(*                 plus main memory.                                         *)
(* AUTHOR        : Anthony Fox (with some contributions by Juliano Iyoda)    *)
(*                 University of Cambridge                                   *)
(* DATE          : 2005 - 2006                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "wordsSyntax", "armTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q wordsTheory rich_listTheory updateTheory armTheory;

val _ = new_theory "system";

(* -------------------------------------------------------------------------- *)
(* In what follows, the term "cp" stands for "coprocessor".                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Memory + CP and bus output                                                 *)
(* -------------------------------------------------------------------------- *)

val _ = type_abbrev("mem", ``:word30->word32``);

val _ = Hol_datatype`
  cp_output = <| data : word32 option list; absent : bool |>`;

val _ = Hol_datatype `bus =
   <| data     : word32 list;
      memory   : mem;
      abort    : num option;
      cp_state : 'a
   |>`;

(* -------------------------------------------------------------------------- *)
(* The system state                                                           *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype `arm_sys_state =
   <| registers : registers;
      psrs      : psrs;
      memory    : mem;
      undefined : bool;
      cp_state  : 'a
   |>`;

(* -------------------------------------------------------------------------- *)
(* The model is paramaterised by a collection of coprocessor operations       *)
(* i.e. cdp, mrc, mcr, stc and ldc functions:                                 *)
(*                                                                            *)
(* absent: is_usr ireg => bool            ... which instructions are accepted *)
(*                                                                            *)
(* f_cdp : state is_usr ireg => state     ... operation for CDP instruction   *)
(*                                                                            *)
(* f_mrc : state is_usr ireg => word32    ... output for MRC instruction      *)
(*                                                                            *)
(* f_mcr : state is_usr ireg data => state                                    *)
(*                                        ... operation for MCR instruction   *)
(*                                                                            *)
(* f_stc : state is_usr ireg => word32 option list                            *)
(*                                        ... output for STC instruction      *)
(*                                                                            *)
(* f_ldc : state is_usr ireg data => state                                    *)
(*                                        ... operation for LDC instruction   *)
(*                                                                            *)
(* n_ldc : state is_usr ireg => num       ... number of words to load         *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val _ = Hol_datatype `coproc =
  <| absent : bool -> word32 -> bool;
     f_cdp  : 'a -> bool -> word32 -> 'a;
     f_mrc  : 'a -> bool -> word32 -> word32;
     f_mcr  : 'a -> bool -> word32 -> word32 -> 'a;
     f_stc  : 'a -> bool -> word32 -> word32 option list;
     f_ldc  : 'a -> bool -> word32 -> word32 list -> 'a;
     n_ldc  : 'a -> bool -> word32 -> num
  |>`;

(* -------------------------------------------------------------------------- *)
(* ADD_COPROC                                                                 *)
(* Add a new coprocessor (cp1) to an existing specification (cp2)             *)
(* -------------------------------------------------------------------------- *)

val ADD_COPROC = Define`
  ADD_COPROC (cp1:'a coproc) (cp2:'b coproc) =
    <| absent := \is_usr ireg. cp1.absent is_usr ireg /\ cp2.absent is_usr ireg;
       f_cdp := \state is_usr ireg.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_cdp (FST state) is_usr ireg,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_cdp (SND state) is_usr ireg);
       f_mrc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.f_mrc (SND state) is_usr ireg
                   else
                     cp1.f_mrc (FST state) is_usr ireg;
       f_mcr := \state is_usr ireg data.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_mcr (FST state) is_usr ireg data,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_mcr (SND state) is_usr ireg data);
       f_stc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.f_stc (SND state) is_usr ireg
                   else
                     cp1.f_stc (FST state) is_usr ireg;
       f_ldc := \state is_usr ireg data.
                  (if cp1.absent is_usr ireg then
                     FST state
                   else
                     cp1.f_ldc (FST state) is_usr ireg data,
                   if cp2.absent is_usr ireg then
                     SND state
                   else
                     cp2.f_ldc (SND state) is_usr ireg data);
       n_ldc := \state is_usr ireg.
                   if cp1.absent is_usr ireg then
                     cp2.n_ldc (SND state) is_usr ireg
                   else
                     cp1.n_ldc (FST state) is_usr ireg
    |>`;

(* -------------------------------------------------------------------------- *)
(* CPN                                                                        *)
(* Returns the coprocessor number from the instruction                        *)
(* -------------------------------------------------------------------------- *)

val _ = wordsLib.guess_lengths();

val DECODE_CPN_def = Define `DECODE_CPN (w:word32) = (11 >< 8) w`;

(* -------------------------------------------------------------------------- *)
(* DECODE_CDP                                                                 *)
(* -------------------------------------------------------------------------- *)

val DECODE_CDP_def = Define`
  DECODE_CDP (w:word32) =
    ((23 >< 20) w, (* Cop1 *)
     (19 >< 16) w, (* CRn  *)
     (15 >< 12) w, (* CRd  *)
     (11 >< 8) w,  (* CPN  *)
     (7 >< 5) w,   (* Cop2 *)
     (3 >< 0) w)`; (* CRm  *)

(* -------------------------------------------------------------------------- *)
(* DECODE_CP                                                                  *)
(* Determines the instruction class ** for a coprocessor instruction **       *)
(* -------------------------------------------------------------------------- *)

val DECODE_CP_def = Define`
  DECODE_CP (w:word32) =
    if w ' 25 then
      if w ' 4 /\ w ' 27 then
        if w ' 20 then
          mrc
        else
          mcr
      else
        cdp_und
    else
      ldc_stc`;

(* -------------------------------------------------------------------------- *)
(* OUT_CP                                                                     *)
(* It is assumed that only one coprocessor (i.e. "CP ireg") can accept the    *)
(* instruction but in general this need not be the case                       *)
(* -------------------------------------------------------------------------- *)

val OUT_CP_def = Define`
  OUT_CP cp state ireg arm_out =
    let is_usr = arm_out.user in
      if arm_out.cpi /\ ireg ' 27 /\ ~cp.absent is_usr ireg then
        <| data :=
             let ic = DECODE_CP ireg in
               if ic = mrc then
                 [SOME (cp.f_mrc state is_usr ireg) ; NONE ]
               else if (ic = ldc_stc) /\ ~(ireg ' 20) then
                 cp.f_stc state is_usr ireg
               else
                 GENLIST (K NONE) (cp.n_ldc state is_usr ireg);
           absent := F |>
      else
        <| data := []; absent := T |>`;

(* -------------------------------------------------------------------------- *)
(* RUN_CP                                                                     *)
(* Takes a CP state and the input (word32 list) and returns the next state    *)
(* -------------------------------------------------------------------------- *)

val RUN_CP_def = Define`
  RUN_CP cp state absent is_usr ireg data =
    if ~absent then
      let ic = DECODE_CP ireg in
        if ic = mcr then
          cp.f_mcr state is_usr ireg (HD data)
        else if (ic = ldc_stc) /\ ireg ' 20 then
          cp.f_ldc state is_usr ireg data
        else if ic = cdp_und then
          cp.f_cdp state is_usr ireg
        else
          state
    else
      state`;

(* -------------------------------------------------------------------------- *)
(* NEXT_ARM_SYS and STATE_ARM_SYS                                             *)
(* NB. Assumes that there are no prefetch aborts or hardware                  *)
(*     interrupts (fiq, irq)                                                  *)
(* -------------------------------------------------------------------------- *)

val addr30_def  = Define `addr30 (x:word32) = (31 >< 2) x`;

val NEXT_ARM_SYS_def = Define`
  NEXT_ARM_SYS bus_op (cp:'a coproc) (state:'a arm_sys_state) =
    let ireg = state.memory (addr30 (FETCH_PC state.registers)) in
    let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
               ireg := ireg;
               exception := if state.undefined then undefined else software |>
    in
    let arm_out = OUT_ARM s
    in
    let cp_out  = OUT_CP cp state.cp_state ireg arm_out
    in
    let b = bus_op arm_out state.cp_state cp_out.data state.memory
    in
    let r = RUN_ARM s (if IS_SOME b.abort then
                          SOME (THE b.abort)
                       else
                          NONE)
                       b.data cp_out.absent
    and p = RUN_CP cp b.cp_state cp_out.absent arm_out.user ireg b.data
    in
      <| registers := r.reg; psrs := r.psr; memory := b.memory;
         undefined := (~state.undefined /\ arm_out.cpi /\ cp_out.absent);
         cp_state := p |>`;

val STATE_ARM_SYS_def = Define`
  (STATE_ARM_SYS bus_op cp 0 s = s) /\
  (STATE_ARM_SYS bus_op cp (SUC t) s =
    NEXT_ARM_SYS bus_op cp (STATE_ARM_SYS bus_op cp t s))`;

(* -------------------------------------------------------------------------- *)
(* An Idealistic Memory Model                                                 *)
(* -------------------------------------------------------------------------- *)

val SET_BYTE_def = Define`
  SET_BYTE (oareg:word2) (b:word8) (w:word32) =
    word_modify (\i x.
                  (i < 8) /\ (if oareg = 0w then b ' i else x) \/
       (8 <= i /\ i < 16) /\ (if oareg = 1w then b ' (i - 8) else x) \/
      (16 <= i /\ i < 24) /\ (if oareg = 2w then b ' (i - 16) else x) \/
      (24 <= i /\ i < 32) /\ (if oareg = 3w then b ' (i - 24) else x)) w`;

val SET_HALF_def = Define`
  SET_HALF (oareg:bool) (hw:word16) (w:word32) =
    word_modify (\i x.
                 (i < 16) /\ (if ~oareg then hw ' i else x) \/
      (16 <= i /\ i < 32) /\ (if oareg then hw ' (i - 16) else x)) w`;

val MEM_WRITE_BYTE_def = Define`
  MEM_WRITE_BYTE (mem:mem) addr (word:word8) =
    let a30 = addr30 addr in
      (a30 =+ SET_BYTE ((1 >< 0) addr) word (mem a30)) mem`;

val MEM_WRITE_HALF_def = Define`
  MEM_WRITE_HALF (mem:mem) addr (word:word16) =
    let a30 = addr30 addr in
      (a30 =+ SET_HALF (addr ' 1) word (mem a30)) mem`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD (mem:mem) addr word = (addr30 addr =+ word) mem`;

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
                MAP (\addr. mem (addr30 addr)) (ADDRESS_LIST a (LENGTH f)), mem)
         else
           (cp_data, data ++ [mem (addr30 a)], mem)
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
  TRANSFERS arm_out cp_state cp_data mem =
    let (data, mem) =
      if arm_out.cpi /\ NULL arm_out.transfers then
        (MAP THE cp_data, mem)
      else
        SND (FOLDL (TRANSFER arm_out.cpi) (cp_data, [], mem) arm_out.transfers)
    in
      <| data := data; memory := mem;
         abort := NONE; cp_state := cp_state |>`;

(* -------------------------------------------------------------------------- *)
(* NEXT_ARM_MMU                                                               *)
(* -------------------------------------------------------------------------- *)

val NEXT_ARM_MMU_def = Define `NEXT_ARM_MMU = NEXT_ARM_SYS TRANSFERS`;

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val TRANSFERS = prove(
  `(!arm_out p15_reg data mem.
        (TRANSFERS arm_out cp_state data mem).abort = NONE) /\
   (!arm_out p15_reg data mem.
        (TRANSFERS arm_out cp_state data mem).cp_state = cp_state)`,
  SRW_TAC [] [TRANSFERS_def] \\ FULL_SIMP_TAC (srw_ss()) []);

val NEXT_ARM_MMU = store_thm("NEXT_ARM_MMU",
 `NEXT_ARM_MMU cp state =
    let ireg = state.memory (addr30 (FETCH_PC state.registers)) in
    let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
               ireg := ireg;
               exception := if state.undefined then undefined else software |>
    in
    let arm_out = OUT_ARM s
    in
    let cp_out  = OUT_CP cp state.cp_state ireg arm_out
    in
    let b = TRANSFERS arm_out state.cp_state cp_out.data state.memory
    in
    let r = RUN_ARM s NONE b.data cp_out.absent
    and p = RUN_CP cp state.cp_state cp_out.absent arm_out.user ireg b.data
    in
      <| registers := r.reg; psrs := r.psr; memory := b.memory;
         undefined := (~state.undefined /\ arm_out.cpi /\ cp_out.absent);
         cp_state := p |>`,
  SRW_TAC [boolSimps.LET_ss] [NEXT_ARM_SYS_def,NEXT_ARM_MMU_def,TRANSFERS]);

val STATE_ARM_MMU_def = Define`
  (STATE_ARM_MMU cp 0 s = s) /\
  (STATE_ARM_MMU cp (SUC t) s = NEXT_ARM_MMU cp (STATE_ARM_MMU cp t s))`;

(* -------------------------------------------------------------------------- *)
(* NEXT_ARM_MEM and STATE_ARM_MEM                                             *)
(* -------------------------------------------------------------------------- *)

val NO_CP_def = Define `NO_CP = <| absent := \u i. T |> : 'a coproc`;

val OUT_CP_NO_CPS =
  SIMP_CONV (srw_ss()++boolSimps.LET_ss) [OUT_CP_def,NO_CP_def]
  ``OUT_CP NO_CP state ireg arm_out``;

val RUN_CP_NO_CPS =
  SIMP_CONV (srw_ss()++boolSimps.LET_ss) [RUN_CP_def,NO_CP_def]
  ``RUN_CP NO_CP state T is_usr ireg data``;

val NEXT_ARM_MEM_def  = Define `NEXT_ARM_MEM = NEXT_ARM_MMU NO_CP`;
val STATE_ARM_MEM_def = Define `STATE_ARM_MEM = STATE_ARM_MMU NO_CP`;

val NEXT_ARM_MEM = store_thm("NEXT_ARM_MEM",
  `NEXT_ARM_MEM state =
     let ireg = state.memory (addr30 (FETCH_PC state.registers)) in
     let s = <| regs := <| reg := state.registers; psr := state.psrs |>;
                ireg := ireg;
                exception := if state.undefined then undefined else software |>
     in
     let arm_out = OUT_ARM s in
     let mmu_out = TRANSFERS arm_out state.cp_state [] state.memory
     in
     let r = RUN_ARM s NONE mmu_out.data T
     in
       <| registers := r.reg; psrs := r.psr; memory := mmu_out.memory;
          undefined := (~state.undefined /\ arm_out.cpi);
          cp_state := state.cp_state |>`,
  SRW_TAC [boolSimps.LET_ss]
          [NEXT_ARM_MEM_def,NEXT_ARM_MMU,RUN_CP_NO_CPS,OUT_CP_NO_CPS]);

(* ------------------------------------------------------------------------- *)
(* Export ML versions of functions                                           *)
(*---------------------------------------------------------------------------*)

val mem_read_def        = Define`mem_read (m: mem, a) = m a`;
val mem_write_def       = Define`mem_write (m:mem) a d = (a =+ d) m`;
val mem_write_block_def = Define`mem_write_block (m:mem) a cr = (a |: cr) m`;
val mem_items_def       = Define`mem_items (m:mem) = []:(word30 # word32) list`;
val empty_memory_def    = Define`empty_memory = (\a. 0xE6000010w):mem`;
val empty_registers_def = Define`empty_registers = (\n. 0w):registers`;
val empty_psrs_def      = Define`empty_psrs = (\x. SET_IFMODE F F usr 0w):psrs`;

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
      DECODE_SWP_def,DECODE_LDC_STC_def,DECODE_CDP_def,DECODE_MRC_MCR_def,
      SHIFT_IMMEDIATE_def,SHIFT_REGISTER_def,
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
  DECODE_TAC \\ `4096 = 16 * 256n` by numLib.ARITH_TAC
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
    let (q1,CPN) = DIVMOD_2EXP 4 q0 in
    let (q2,CRd) = DIVMOD_2EXP 4 q1 in
    let (q3,Rn) = DIVMOD_2EXP 4 q2 in
    let (q4,L) = DIVMOD_2EXP 1 q3 in
    let (q5,W) = DIVMOD_2EXP 1 q4 in
    let (q6,N) = DIVMOD_2EXP 1 q5 in
    let (q7,U) = DIVMOD_2EXP 1 q6 in
      (ODD q7,U = 1,N = 1,W = 1,L = 1,n2w Rn,n2w CRd,n2w CPN,n2w offset)`,
  DECODE_TAC);

val DECODE_CDP_THM = store_thm("DECODE_CDP_THM",
  `!n. DECODE_CDP (n2w n) =
    let (q0,CRm) = DIVMOD_2EXP 4 n in
    let (q1,Cop2) = DIVMOD_2EXP 3 (DIV2 q0) in
    let (q2,CPN) = DIVMOD_2EXP 4 q1 in
    let (q3,CRd) = DIVMOD_2EXP 4 q2 in
    let (q4,CRn) = DIVMOD_2EXP 4 q3 in
      (n2w (MOD_2EXP 4 q4),n2w CRn,n2w CRd,n2w CPN,n2w Cop2,n2w CRm)`,
  DECODE_TAC);

val DECODE_MRC_MCR_THM = store_thm("DECODE_MRC_MCR_THM",
  `!n. DECODE_MRC_MCR (n2w n) =
    let (q0,CRm) = DIVMOD_2EXP 4 n in
    let (q1,Cop2) = DIVMOD_2EXP 3 (DIV2 q0) in
    let (q2,CPN) = DIVMOD_2EXP 4 q1 in
    let (q3,CRd) = DIVMOD_2EXP 4 q2 in
    let (q4,CRn) = DIVMOD_2EXP 4 q3 in
      (n2w (MOD_2EXP 3 (DIV2 q4)),n2w CRn,n2w CRd,n2w CPN,n2w Cop2,n2w CRm)`,
  DECODE_TAC);

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
    let b n = ireg ' n in
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

(* -------------------------------------------------------------------------- *)

val _ = export_theory();
